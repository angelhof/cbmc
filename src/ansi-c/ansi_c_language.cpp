/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ansi_c_language.h"

#include <cstring>
#include <sstream>
#include <fstream>
#include <iostream>

#include <util/config.h>
#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/get_base_name.h>

#include <linking/linking.h>
#include <linking/remove_internal_symbols.h>

#include "ansi_c_entry_point.h"
#include "ansi_c_typecheck.h"
#include "ansi_c_parser.h"
#include "expr2c.h"
#include "c_preprocess.h"
#include "ansi_c_internal_additions.h"
#include "type2name.h"

std::set<std::string> ansi_c_languaget::extensions() const
{
  return { "c", "i" };
}

void ansi_c_languaget::modules_provided(std::set<std::string> &modules)
{
  modules.insert(get_base_name(parse_path, true));
}

/// ANSI-C preprocessing
bool ansi_c_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream)
{
  // stdin?
  if(path.empty())
    return c_preprocess(instream, outstream, get_message_handler());

  return c_preprocess(path, outstream, get_message_handler());
}

bool ansi_c_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  // store the path
  parse_path=path;

  // preprocessing
  std::ostringstream o_preprocessed;

  if(preprocess(instream, path, o_preprocessed))
    return true;

  std::istringstream i_preprocessed(o_preprocessed.str());

  // parsing

  std::string code;
  ansi_c_internal_additions(code);
  std::istringstream codestr(code);

  ansi_c_parser.clear();
  ansi_c_parser.set_file(ID_built_in);
  ansi_c_parser.in=&codestr;
  ansi_c_parser.set_message_handler(get_message_handler());
  ansi_c_parser.for_has_scope=config.ansi_c.for_has_scope;
  ansi_c_parser.ts_18661_3_Floatn_types=config.ansi_c.ts_18661_3_Floatn_types;
  ansi_c_parser.cpp98=false; // it's not C++
  ansi_c_parser.cpp11=false; // it's not C++
  ansi_c_parser.mode=config.ansi_c.mode;

  ansi_c_scanner_init();

  bool result=ansi_c_parser.parse();

  if(!result)
  {
    ansi_c_parser.set_line_no(0);
    ansi_c_parser.set_file(path);
    ansi_c_parser.in=&i_preprocessed;
    ansi_c_scanner_init();
    result=ansi_c_parser.parse();
  }

  // save result
  parse_tree.swap(ansi_c_parser.parse_tree);

  // save some memory
  ansi_c_parser.clear();

  return result;
}

bool ansi_c_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module,
  const bool keep_file_local)
{
  symbol_tablet new_symbol_table;

  if(ansi_c_typecheck(
    parse_tree,
    new_symbol_table,
    module,
    get_message_handler()))
  {
    return true;
  }

  remove_internal_symbols(
    new_symbol_table, this->get_message_handler(), keep_file_local);

  if(linking(symbol_table, new_symbol_table, get_message_handler()))
    return true;

  return false;
}

bool ansi_c_languaget::generate_support_functions(
  symbol_tablet &symbol_table)
{
  // This creates __CPROVER_start and __CPROVER_initialize:
  return ansi_c_entry_point(
    symbol_table, get_message_handler(), object_factory_params);
}

// Question: There should be a better (cleaner) way to do this
bool is_call_to_function(std::string function_name, exprt expr) {
  // Question: What is the difference between base name and identifier?
      
  // Question: Isn't there a canonical way to access fields
  // of an expression with methods, or finding the id of an
  // expression with methods such as "is_symbol" or
  // operand.identifier
  
  return expr.id() == "side_effect"
    && expr.find(ID_statement).id() == "function_call"
    && expr.op0().id() == "symbol"
    && expr.op0().find(ID_identifier).id() == function_name;
}

// QUESTION: Should I make that static or define it somewhere else?
exprt aggregate_function_conditions(std::string target_function_name, ansi_c_declaratort function) {
  exprt function_body = function.value();
  
  // TODO: I probably have to add some check that inside the
  // code in the precondition there is nothing funky going on?
  exprt::operandst conditions;
  
  // Question: Is there a better way to get the members of the parse
  // tree (rather than checking their id strings?
  for (depth_iteratort it = function_body.depth_begin(); it != function_body.depth_end(); ++it) {
    
    // Question: What is the correct way of finding a function call?
    // std::cout << it->id() << " -- " << it->find(ID_statement).id() << "\n";
    // Filters the function calls
    if (is_call_to_function(target_function_name, *it)) {
      exprt condition = it->op1().op0();
      // std::cout << "Precondition:\n" << precondition.pretty() << "\n";
      // std::cout << "Precondition type:\n" << precondition.type().id() << "\n";
      
      // Note: it is not very efficient to push back in a vector.
      conditions.push_back(condition);

      // TODO: I should probably go to the next sibling or parent
      // after finding a function call to the target name and not just
      // iterate it once
    }
  }

  // WARNING: In order for it to make sense to return the conjunction
  // of the preconditions, they have to be in the beginning of the
  // function body before anythinf else.
  //
  // TODO: Maybe I should add a check to ensure that
  //
  // WARNING: Similarly with postconditions

  
  // Return all the preconditions in a conjunction
  // TODO: I probably have to add metadata to this conjunction
  //
  // Question: It seems that function calls do not have a type. Is it
  // correct to put them in an and expression like that?
  return conjunction(conditions);
}

// Extends the specified contract (requires/ensures) of the function declaration with the given condition.
//
// TODO: What is a way to add as a precondition to this function that
// declaration should be a function definition, and that condition
// should be boolean, etc...
void extend_contract(const irep_namet &contract_name,
                     const exprt condition,
                     ansi_c_declarationt* declaration) {
  exprt old_contract = static_cast<const exprt&>(declaration->find(contract_name));
  if (old_contract.is_nil()) {
    old_contract = make_boolean_expr(true);
  }
  exprt new_contract = and_exprt(old_contract, condition);
  declaration->add(contract_name, new_contract);
}

bool ansi_c_languaget::preconditions_to_contracts() {

  // QUESTION: What is the canonical way to find function definitions?  
  std::list<ansi_c_declarationt> declarations = parse_tree.items;
  for (std::list<ansi_c_declarationt>::iterator it = declarations.begin(); it != declarations.end(); ++it){
    std::cout << "Declaration:\n";

    // Question: Does it always hold that a declaration either has 0 or 1 declarator?
    if (!it->declarators().empty()) {
      ansi_c_declaratort decl = it->declarator();
      std::cout << "  " << decl.get_name() << "\n";
      exprt precondition = aggregate_function_conditions("__CPROVER_precondition", decl);
      // std::cout << "Folded precondition:\n" << precondition.pretty() << "\n";

      // TODO: Add the same for postconditions. Maybe the function
      // has to be different so that it checks whether
      // postconditions are in the right place.
      
      // TODO: Also postconditions are more difficult because they
      // might talk about values that were declared in the function
      // body.
      
      // exprt postcondition = aggregate_function_conditions("__CPROVER_postcondition", *it2);

      if (!precondition.is_true()) {
        std::cout << "  -- Successfully turned precondition into contract\n";
      }
      
      // std::cout << "Previous declaration\n" << it->pretty() << "\n";
      // Question: Is there any better way of passing a pointer to that declaration?
      extend_contract(ID_C_spec_requires, precondition, &(*it));
      // std::cout << "New declaration\n" << it->pretty() << "\n";
    }
  }

  // TODO: I need a way to print the parsed function (with the
  // contract) back to C in order to debug whether the contracts were
  // added correctly.
  
  // show_parse(std::cout);
  return false;
}

void ansi_c_languaget::show_parse(std::ostream &out)
{
  parse_tree.output(out);
}

std::unique_ptr<languaget> new_ansi_c_language()
{
  return util_make_unique<ansi_c_languaget>();
}

bool ansi_c_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2c(expr, ns);
  return false;
}

bool ansi_c_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2c(type, ns);
  return false;
}

bool ansi_c_languaget::type_to_name(
  const typet &type,
  std::string &name,
  const namespacet &ns)
{
  name=type2name(type, ns);
  return false;
}

bool ansi_c_languaget::to_expr(
  const std::string &code,
  const std::string &,
  exprt &expr,
  const namespacet &ns)
{
  expr.make_nil();

  // no preprocessing yet...

  std::istringstream i_preprocessed(
    "void __my_expression = (void) (\n"+code+"\n);");

  // parsing

  ansi_c_parser.clear();
  ansi_c_parser.set_file(irep_idt());
  ansi_c_parser.in=&i_preprocessed;
  ansi_c_parser.set_message_handler(get_message_handler());
  ansi_c_parser.mode=config.ansi_c.mode;
  ansi_c_parser.ts_18661_3_Floatn_types=config.ansi_c.ts_18661_3_Floatn_types;
  ansi_c_scanner_init();

  bool result=ansi_c_parser.parse();

  if(ansi_c_parser.parse_tree.items.empty())
    result=true;
  else
  {
    expr=ansi_c_parser.parse_tree.items.front().declarator().value();

    // typecheck it
    result=ansi_c_typecheck(expr, get_message_handler(), ns);
  }

  // save some memory
  ansi_c_parser.clear();

  // now remove that (void) cast
  if(expr.id()==ID_typecast &&
     expr.type().id()==ID_empty &&
     expr.operands().size()==1)
    expr=expr.op0();

  return result;
}

ansi_c_languaget::~ansi_c_languaget()
{
}
