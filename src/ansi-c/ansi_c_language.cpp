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

// Question: Are those [is_*] functions correct?

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

bool is_code_postcondition(exprt expr) {
  return expr.find(ID_statement).is_not_nil()
    && expr.get(ID_statement) == "expression"
    && is_call_to_function("__CPROVER_postcondition", expr.op0());
}

// Question: Is this name reasonable?
// Question: There is probably a better way to do that
bool is_symbol(exprt expr) {
  // Question: What is the difference between base name and identifier?
      
  // Question: Isn't there a canonical way to access fields
  // of an expression with methods, or finding the id of an
  // expression with methods such as "is_symbol" or
  // operand.identifier
  
  return expr.id() == "symbol";
}

bool is_variable_declaration(exprt expr) {
  // Question: What is the difference between base name and identifier?
      
  // Question: Isn't there a canonical way to access fields
  // of an expression with methods, or finding the id of an
  // expression with methods such as "is_symbol" or
  // operand.identifier
  
  return expr.find(ID_statement).is_not_nil()
    && expr.get(ID_statement) == "decl";
}

bool is_return_statement(exprt expr) {
  return expr.find(ID_statement).is_not_nil()
    && expr.get(ID_statement) == "return";
}

exprt::operandst filter_pre_post_conditions(std::string target_function_name, exprt function_body) {
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
  return conditions;
}


// This function finds all postconditions and collects them in groups
// of sequences. Each sequence refers to a function exit point
// (return). 
//
// Question: Maybe vector isn't the best candidate container for that task
std::vector<exprt::operandst> collect_postconditions(exprt function_body) {

  // TODO:
  //
  // - Find all postconditions in a straight line before the exit
  //   point.  Note: This is not trivial to do, as postconditions
  //   might not be in an uninterrupted sequence (is that possible?)
  //
  //   Note: Postconditions don't make sense if they are not just
  //   before the function exit point. If some "effectful" operation
  //   happens between a postcondition and the exit point, then the
  //   postcondition was really meant to be an assert, but it could
  //   not hold at the exit point.
  //
  //   Note: A major difficulty is that a sequence of postconditions
  //   might be interrupted by a jump or a branch (e.g. in case a
  //   postcondition holds for both branches of an if-then-else
  //   statement), and we have to be able to deal with that. Plan to
  //   get around that. Can we make an iterator that can go back and
  //   forth? So that when we find the return value we can take back
  //   steps and get all postconditions in our way?
  //
  // - (Maybe) Explicitly warn when a postcondition can not be matched
  //   to any exit point so it is skipped.

  // std::cout << "Function body:\n" << function_body.pretty() << "\n";

  // For now, instead of getting the proper postconditions before each
  // return, we can instead just find any block that contains a return
  // (in its operands) and then get all the postconditions before it
  // in the same block. This is not complete, but should work for now.
  std::vector<exprt::operandst> postconditions;

  // Warning: This is pretty inefficient, because it checks all
  // children twice. Once for whether they contain a return, and one
  // for the iteration itself.
  for (depth_iteratort d_it = function_body.depth_begin(); d_it != function_body.depth_end(); ++d_it) {
    // If the list of operands of this node contains a return then get
    // all the postconditions before that return.
    exprt::operandst operands = d_it->operands();
    
    // Find all the return statement in the block
    exprt::operandst::reverse_iterator it = operands.rbegin();
    while (it != operands.rend()) {
      
      // Find the last return statement
      for (; it != operands.rend() && !is_return_statement(*it); ++it)
        ;
      
      // If a return statement was indeed found in the operands
      if (it != operands.rend()) {
        assert(is_return_statement(*it));
        // std::cout << "Found return statement\n" << return_statement->pretty() << "\n";
        // Collect all postconditions that are in sequence before the
        // return statement
        std::list<exprt> postcondition_group;
        ++it;
        while (it != operands.rend() && is_code_postcondition(*it)) {
          // std::cout << "Found postcondition\n" << it->op0().pretty() << "\n";
          postcondition_group.push_front(it->op0());
          ++it;
        }
        
        exprt::operandst postcondition_group_vec(postcondition_group.begin(), postcondition_group.end());
        postconditions.push_back(postcondition_group_vec);
      }
    }
  }
  
  return postconditions;
}

// This function finds all the names of variables declared in the function body.
std::unordered_set<std::string> get_body_variable_names(exprt function_body) {
  std::unordered_set<std::string> body_variable_names;
  for (depth_iteratort d_it = function_body.depth_begin(); d_it != function_body.depth_end(); ++d_it) {
    
    // Question: What is the correct way of finding all variable
    // declarations in the function body?
    //
    // Filters the variable declarations
    if (is_variable_declaration(*d_it)) {
      // std::cout << "Variable Declaration:\n";
      // std::cout << d_it->pretty() << "\n";
      
      exprt::operandst declared_vars = d_it->op0().operands();
      
      // Keep the name of all declared variables in the function body
      for (exprt::operandst::iterator it = declared_vars.begin(); it != declared_vars.end(); ++it) {
        // std::cout << it->pretty() << "\n";
        std::string var_name = it->get_string(ID_name);
        // std::cout << var_name << "\n";
        body_variable_names.insert(var_name);
      }
      
      // std::string var_name = d_it->get_string(ID_identifier);
      
      // Note: It might be more efficient to skip to the next
      // sibling instead of just incrementing d_it when we found a
      // declaration
    }
  }
  return body_variable_names;
}

// Returns true if the expression refers to a variable in the given
// set of variable names
bool refers_to_variable_in_set(exprt expr, std::unordered_set<std::string> variable_names) {
  bool rval = false;
  for (depth_iteratort d_it = expr.depth_begin(); d_it != expr.depth_end(); ++d_it) {   
    // Question: What is the correct way of finding all variable references?
    // Filters the variable references
    if (is_symbol(*d_it)) {
      // std::cout << d_it->pretty() << "\n";
      std::string var_name = d_it->get_string(ID_identifier);
      if (variable_names.find(var_name) != variable_names.end()) {
        rval = true;
        break;
      }
    }
  }
  return rval;
}

exprt aggregate_function_postconditions(ansi_c_declaratort function) {
  exprt function_body = function.value();
  
  // Gather the variable names that were declared in the function body
  std::unordered_set<std::string> body_variable_names = get_body_variable_names(function_body);

  exprt::operandst aggregated_groups;
  
  if (function_body.is_not_nil()) {  
    // TODO: I probably have to add some check that inside the
    // code in the postconditions there is nothing funky going on?
    std::vector<exprt::operandst> postconditions = collect_postconditions(function_body);
    std::cout << "  -- Found " << postconditions.size() << " exit points\n";
    int i = 1;
    for (auto group = postconditions.begin(); group != postconditions.end(); ++group) {
      std::cout << "   + Exit point: " << i << " has " << group->size() << " postconditions\n";
      ++i;

      // WARNING: In order for it to make sense to return the disjunction
      // of the potconditions, they have to be at the end of the body, and
      // they have to not refer to anything that is declared in the body.
      //
      // Question: Is there any other constraint for the postconditions so
      // that they can be turned to function contracts?
      
      for (exprt::operandst::iterator it = group->begin(); it != group->end(); ++it) {
        // Turn all postconditions that refer to symbols other than the arguments to true
        exprt postcondition = *it;
        
        // std::cout << "Before:\n" << it->pretty() << "\n"; If this
        // specific postcondition refers to a variable that was
        // declared in the body (and thus in an inner scope), then
        // make it be true
        if (refers_to_variable_in_set(*it, body_variable_names)) {
          *it = make_boolean_expr(true);
          std::cout << "   +- Postcondition reference to body variable\n";
        }
        // std::cout << "After:\n" << it->pretty() << "\n";
      }

      // Aggregate all the postconditions in a conjunction as they are in sequence
      aggregated_groups.push_back(conjunction(*group));
    }
  }
  
  // Aggregate the conjunction of each group as a disjunction
  //
  // TODO: Instead of aggregating into a disjunction, try to
  // aggregate based on the return value
  return disjunction(aggregated_groups);
}

// QUESTION: Should I make that static or define it somewhere else?
exprt aggregate_function_preconditions(ansi_c_declaratort function) {
  exprt function_body = function.value();
  
  // TODO: I probably have to add some check that inside the
  // code in the precondition there is nothing funky going on?
  exprt::operandst preconditions = filter_pre_post_conditions("__CPROVER_precondition", function_body);
  

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
  return conjunction(preconditions);
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
      exprt precondition = aggregate_function_preconditions(decl);
      // std::cout << "Folded precondition:\n" << precondition.pretty() << "\n";
      if (!precondition.is_true()) {
        std::cout << "  -- Successfully turned precondition into contract\n";
      }
      // std::cout << "Previous declaration\n" << it->pretty() << "\n";
      // Question: Is there any better way of passing a pointer to that declaration?
      extend_contract(ID_C_spec_requires, precondition, &(*it));
      // std::cout << "New declaration\n" << it->pretty() << "\n";
      
      // exprt postcondition = aggregate_function_conditions("__CPROVER_postcondition", *it2);
      exprt postcondition = aggregate_function_postconditions(decl);
      // std::cout << "Folded postcondition:\n" << postcondition.pretty() << "\n";
      if (!postcondition.is_false()) {
        std::cout << "  -- Successfully turned postcondition into contract\n";
      }
      // std::cout << "Previous declaration\n" << it->pretty() << "\n";
      // Question: Is there any better way of passing a pointer to that declaration?
      extend_contract(ID_C_spec_ensures, postcondition, &(*it));
      // std::cout << "New declaration\n" << it->pretty() << "\n";
      
    }
  }

  // TODO: Make a check for preconditions and ensure that they happen
  // before anything else in the code. Should this check just be that
  // the preconditions are a prefix of the function body?

  // TODO: Get the preconditions from code
  //
  // - Search for all the postconditions as we do about the preconditions.
  //
  //   + There are some issues with that. Postconditions might be
  //     different in each function exit point. The best thing to do
  //     for start would be to get their disjunction and turn that
  //     into an ensures. In the future we would like to talk about
  //     the return value and its correlation with the final
  //     postcondition.
  //
  //   + Postconditions might talk about values that were declared in
  //     the function. We should filter any postcondition "conjunct"
  //     that refers to a variable that was declared during the
  //     function. For start we could just filter out any
  //     postcondition that refers to anything that is not included in
  //     the function arguments.
  
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
