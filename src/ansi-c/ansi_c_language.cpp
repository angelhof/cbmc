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

// Question: Are those [is_*] functions correct? Are they sound/complete?
bool is_call_to_function(irep_idt function_name, exprt expr) {
  if(can_cast_expr<side_effect_expr_function_callt>(expr))
  {
    const side_effect_expr_function_callt function_call = to_side_effect_expr_function_call(expr);
    const exprt function = function_call.function();
    
    if(can_cast_expr<symbol_exprt>(function))
    {
      const symbol_exprt function_symbol = to_symbol_expr(function);
      return function_symbol.get_identifier() == function_name;
    }
  }
  return false;
}

bool is_code_postcondition(exprt expr) {
  if(can_cast_expr<code_expressiont>(expr))
  {
    exprt expr0 = to_code_expression(to_code(expr)).expression();
    return is_call_to_function("__CPROVER_postcondition", expr0);
  }
  return false;
}


exprt::operandst filter_pre_post_conditions(irep_idt target_function_name, code_blockt function_body) {
  // TODO: I probably have to add some check that inside the
  // code in the precondition there is nothing funky going on?
  exprt::operandst conditions;
  for (depth_iteratort it = function_body.depth_begin(); it != function_body.depth_end(); ++it) {
    // std::cout << it->id() << " -- " << it->find(ID_statement).id() << "\n";
    if (is_call_to_function(target_function_name, *it)) {
      const side_effect_expr_function_callt function_call = to_side_effect_expr_function_call(*it);
      exprt condition = function_call.arguments().front();
      // std::cout << "Precondition:\n" << precondition.pretty() << "\n";
      // std::cout << "Precondition type:\n" << precondition.type().id() << "\n";
      
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
std::vector<exprt::operandst> collect_postconditions(code_blockt function_body) {

  // TODO: (Maybe) Explicitly warn when a postcondition can not be
  // matched to any exit point so it is skipped.

  // std::cout << "Function body:\n" << function_body.pretty() << "\n";

  // For now, instead of getting the proper postconditions before each
  // return, we can instead just find any block that contains a return
  // (in its operands) and then get all the postconditions before it
  // in the same block. This is not complete, but should work for now.
  std::vector<exprt::operandst> postconditions;
  for (depth_iteratort d_it = function_body.depth_begin(); d_it != function_body.depth_end(); ++d_it) {
    if(can_cast_expr<code_blockt>(*d_it)){
      const code_blockt block = to_code_block(to_code(*d_it));
      code_blockt::code_operandst operands = block.statements();
    
      // Find all the return statement in the block
      exprt::operandst::reverse_iterator it = operands.rbegin();
      while (it != operands.rend()) {
        
        // Find the last return statement
        for (; it != operands.rend() && !can_cast_expr<code_returnt>(*it); ++it)
          ;
        
        // If a return statement was indeed found in the operands
        if (it != operands.rend()) {
          assert(can_cast_expr<code_returnt>(*it));
          ++it;
          // std::cout << "Found return statement\n" << return_statement->pretty() << "\n";
          // Collect all postconditions that are in sequence before the
          // return statement
          std::list<exprt> postcondition_group;
          while (it != operands.rend() && is_code_postcondition(*it)) {
            // std::cout << "Found postcondition\n" << it->op0().pretty() << "\n";
            const code_expressiont code_expr = to_code_expression(to_code(*it));
            const side_effect_expr_function_callt function_call =
              to_side_effect_expr_function_call(code_expr.expression());
            postcondition_group.push_front(function_call.arguments().front());
            ++it;
          }
          
          exprt::operandst postcondition_group_vec(postcondition_group.begin(), postcondition_group.end());
          postconditions.push_back(postcondition_group_vec);
          it = operands.rend();
        }
      }
    }
  }

  // If postconditions vec is empty, it means that no return statement
  // was found. This is possible in case of void functions and then
  // postconditions should be searched from the end of the function
  // body
  if (postconditions.empty()) {
    code_blockt::code_operandst operands = function_body.statements();
    
    // Find all the consecutive postconditions at the end fo the block
    code_blockt::code_operandst::reverse_iterator it = operands.rbegin();
    std::list<exprt> postcondition_group;
    while (it != operands.rend() && is_code_postcondition(*it)) {
      // std::cout << "Found postcondition\n" << it->op0().pretty() << "\n";
      const code_expressiont code_expr = to_code_expression(to_code(*it));
      const side_effect_expr_function_callt function_call =
        to_side_effect_expr_function_call(code_expr.expression());
      postcondition_group.push_front(function_call.arguments().front());
      ++it;
    }

    exprt::operandst postcondition_group_vec(postcondition_group.begin(), postcondition_group.end());
    postconditions.push_back(postcondition_group_vec);
  }

  // Question: Is there a straightforward way to assert that the
  // postconditions vector has length equal to the number of exit
  // points in the function.
  INVARIANT(!postconditions.empty(),
            "The postconditions vector should never be empty."
            "It's length should be equal to the number of exit points in the function.");
  
  return postconditions;
}

// This function finds all the names of variables declared in the function body.
std::unordered_set<irep_idt> get_body_variable_names(code_blockt function_body) {
  std::unordered_set<irep_idt> body_variable_names;
  for (depth_iteratort d_it = function_body.depth_begin(); d_it != function_body.depth_end(); ++d_it) {
    
    // Question: Is there a more straightforward way of finding all
    // variable declarations in the body?
    if (can_cast_expr<code_declt>(*d_it)) {
      // std::cout << "Variable Declaration:\n";
      // std::cout << d_it->pretty() << "\n";
      exprt::operandst declared_vars = d_it->op0().operands();
      
      // Keep the name of all declared variables in the function body
      for (exprt::operandst::iterator it = declared_vars.begin(); it != declared_vars.end(); ++it) {
        // std::cout << it->pretty() << "\n";
        irep_idt var_name = it->get(ID_name);
        // std::cout << var_name << "\n";
        body_variable_names.insert(var_name);
      }
    }
  }
  return body_variable_names;
}

// Returns true if the expression refers to a variable in the given
// set of variable names
bool refers_to_variable_in_set(exprt expr, std::unordered_set<irep_idt> variable_names) {
  bool rval = false;
  for(depth_iteratort d_it = expr.depth_begin(); d_it != expr.depth_end(); ++d_it)
  { 
    if(can_cast_expr<symbol_exprt>(*d_it))
    {
      // std::cout << d_it->pretty() << "\n";
      const irep_idt var_name = to_symbol_expr(*d_it).get_identifier();
      if (variable_names.find(var_name) != variable_names.end()) {
        rval = true;
        break;
      }
    }
  }
  return rval;
}

// Question: Is there a way to optimize this (Returning a balanced
// tree instead of a chain tree)? Is there a standard function that I
// can call for this?
//
// TODO: Unify the disjunction and the conjunction as they do the same
// thing essentially except for the call to and/or
//
// If this function returns nil expression, it means that no postcondition was aggregated.
exprt postcondition_group_disjunction(const exprt::operandst &nil_op)
{
  exprt::operandst op;
  
  // filter non nil expressions
  std::copy_if (nil_op.begin(), nil_op.end(), std::back_inserter(op), [](exprt e){return e.is_not_nil();} );
  
  if(op.empty()) {
    // Question: What is a better way to do this?
    exprt expr = exprt(ID_nil);
    INVARIANT(expr.is_nil(), "Postcondition disjunction should be nil if no postcondition group was found.");
    return expr;
    // return make_boolean_expr(true);
  }
  else if(op.size()==1) {
    return op.front();
  }
  else
  {
    // If the first op is trivially true recurse for free
    auto it = op.begin();
    exprt op0 = *it;
    ++it;
    exprt op1 = *it;
    ++it;
    exprt acc = or_exprt(op0, op1);

    for ( ; it != op.end(); ++it) {
      // Is this invariant correct?
      INVARIANT(it->is_not_nil(), "Disjunction of conditions should never have nil arguments as they have been filtered.");
      acc = or_exprt(acc, *it);
    }

    return acc;
  }
}

// Question: Is there a way to optimize this? Is there a standard
// function that I can call for this?
//
// If this function returns nil expression, it means that no (pre/post)condition was aggregated.
exprt condition_conjunction(const exprt::operandst &nil_op)
{
  exprt::operandst op;
  
  // filter non nil expressions
  std::copy_if (nil_op.begin(), nil_op.end(), std::back_inserter(op), [](exprt e){return e.is_not_nil();} );
  
  if(op.empty()) {
    // Question: What is a better way to do this?
    exprt expr = exprt(ID_nil);
    INVARIANT(expr.is_nil(), "Postcondition conjunction should be nil if no postcondition group was found.");
    return expr;
    // return make_boolean_expr(true);
  }
  else if(op.size()==1) {
    return op.front();
  }
  else
  {
    // If the first op is trivially true recurse for free
    auto it = op.begin();
    exprt op0 = *it;
    ++it;
    exprt op1 = *it;
    ++it;
    exprt acc = and_exprt(op0, op1);

    for ( ; it != op.end(); ++it) {
      // Is this invariant correct?
      INVARIANT(it->is_not_nil(), "Conjunction of conditions should never be called with nil arguments");
      acc = and_exprt(acc, *it);
    }

    // This means that we didn't see any non-nil postcondition group
    INVARIANT(!acc.is_true(), "Assuming that the invariant in the loop holds this should never be the case.");

    return acc;
  }
}

exprt aggregate_function_postconditions(code_blockt function_body) {
  // Gather the variable names that were declared in the function body
  std::unordered_set<irep_idt> body_variable_names = get_body_variable_names(function_body);

  exprt::operandst aggregated_groups;
  
  if (function_body.is_not_nil()) {  
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
        
        // std::cout << "Before:\n" << it->pretty() << "\n";
        //
        // If this specific postcondition refers to a variable that
        // was declared in the body (and thus in an inner scope), then
        // make it be true
        if (refers_to_variable_in_set(*it, body_variable_names)) {
          *it = make_boolean_expr(true);
          std::cout << "   +- Postcondition reference to body variable\n";
        }
        // std::cout << "After:\n" << it->pretty() << "\n";
      }

      // Aggregate all the postconditions in a conjunction as they are in sequence
      aggregated_groups.push_back(condition_conjunction(*group));
    }
  }
  
  // Aggregate the conjunction of each group as a disjunction
  //
  // TODO: Instead of aggregating into a disjunction, try to
  // aggregate based on the return value
  //
  // Question: What happens if there is no aggregated group? What should the returned contract be?
  return postcondition_group_disjunction(aggregated_groups);
}

// TODO: Remove the filter_pre_post_conditions, as it is only used for
// preconditions and add its code here.
//
// QUESTION: Should I make that static or define it somewhere else?
exprt aggregate_function_preconditions(code_blockt function_body) {

  exprt::operandst preconditions = filter_pre_post_conditions("__CPROVER_precondition", function_body);
  
  // WARNING: In order for it to make sense to return the conjunction
  // of the preconditions, they have to be in the beginning of the
  // function body before anythinf else.
  //
  // TODO: Maybe I should add a check to ensure that
  
  return condition_conjunction(preconditions);
}

// Extends the specified contract (requires/ensures) of the function declaration with the given condition.
//
// TODO: What is a way to add as a precondition to [extend_contract]
// that [declaration] should be a function definition, and that
// [condition] should be boolean, etc...
void extend_contract(const irep_namet &contract_name,
                     const exprt condition,
                     ansi_c_declarationt* declaration) {
  exprt old_contract = static_cast<const exprt&>(declaration->find(contract_name));
  exprt new_contract;
  if (old_contract.is_nil()) {
    new_contract = condition;
  } else {
    new_contract = and_exprt(old_contract, condition);
  }
  declaration->add(contract_name, new_contract);
}

bool ansi_c_languaget::preconditions_to_contracts() {

  // QUESTION: What is the canonical way to find function definitions?  
  for (std::list<ansi_c_declarationt>::iterator it = parse_tree.items.begin(); it != parse_tree.items.end(); ++it){
    std::cout << "Declaration:\n";

    // Question: Does it always hold that a declaration either has 0 or 1 declarator?
    if (!it->declarators().empty()) {
      ansi_c_declaratort decl = it->declarator();
      std::cout << "  " << decl.get_name() << "\n";

      if(can_cast_expr<code_blockt>(decl.value()))
      {
        code_blockt function_body = to_code_block(to_code(decl.value()));
        exprt precondition = aggregate_function_preconditions(function_body);

        // std::cout << "Folded precondition:\n" << precondition.pretty() << "\n";
        if (precondition.is_not_nil()) {
          std::cout << "  -- Successfully turned precondition into contract\n";
          // std::cout << "Previous declaration\n" << it->pretty() << "\n";
          // Question: Is there any better way of passing a pointer to that declaration?
          extend_contract(ID_C_spec_requires, precondition, &(*it));
          // std::cout << "New declaration\n" << it->pretty() << "\n";
        }
        
        exprt postcondition = aggregate_function_postconditions(function_body);
        // std::cout << "Folded postcondition:\n" << postcondition.pretty() << "\n";
        
        // WARNING: This will always succeed if there are at least two
        // return points in the function even if they have no
        // postconditions
        if (postcondition.is_not_nil()) {
          std::cout << "  -- Successfully turned postcondition into contract\n";
          // // std::cout << "Previous declaration\n" << it->pretty() << "\n";
          // // Question: Is there any better way of passing a pointer to that declaration?
          
          extend_contract(ID_C_spec_ensures, postcondition, &(*it));
          
          // it->set(ID_C_spec_ensures, postcondition);
          // if(decl.get_name() == "s_sift_down" || decl.get_name() == "s_sift_up") {
          //   std::cout << "New declaration\n" << it->pretty() << "\n";
          // }
          // std::cout << "New declaration\n" << it->pretty() << "\n";
        }
      }
    }
  }

  // TODO: Make a check for preconditions and ensure that they happen
  // before anything else in the code. Should this check just be that
  // the preconditions are a prefix of the function body?
  
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
