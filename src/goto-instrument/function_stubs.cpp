/*******************************************************************\

Module: Create function stubs in C from code contracts

Author: Konstantinos Kallas

Date: July 2019

\*******************************************************************/

/// \file
/// Create function stubs in C from code contracts

#include "function_stubs.h"

#include <fstream>

#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/replace_symbol.h>

#include <goto-programs/remove_skip.h>

#include <analyses/local_may_alias.h>

#include <linking/static_lifetime_init.h>

#include "loop_utils.h"

class function_stubst
{
public:
  function_stubst(
    symbol_tablet &_symbol_table,
    goto_functionst &_goto_functions,
    irep_idt _function_name,
    messaget &_log)
    : ns(_symbol_table),
      symbol_table(_symbol_table),
      goto_functions(_goto_functions),
      function_name(_function_name),
      log(_log),
      temporary_counter(0)
  {
  }

  bool operator()();

protected:
  namespacet ns;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;
  const irep_idt function_name;
  messaget &log;

  unsigned temporary_counter;

  void stub_function(
    const irep_idt &function_id,
    goto_functionst::goto_functiont &goto_function);

  const symbolt &new_tmp_symbol(
    const typet &type,
    const source_locationt &source_location,
    const irep_idt &function_id,
    const irep_idt &mode);
};

// It creates a stub for each function based on the associated
// requires and ensures
void function_stubst::stub_function(
  const irep_idt &function_id,
  goto_functionst::goto_functiont &goto_function)
{
  // Get the function requires and ensures
  const symbolt &f_sym = ns.lookup(function_id);
  const code_typet &type = to_code_type(f_sym.type);

  const exprt &requires =
    static_cast<const exprt &>(type.find(ID_C_spec_requires));
  const exprt &ensures =
    static_cast<const exprt &>(type.find(ID_C_spec_ensures));

  // Clear the function body
  goto_function.body.clear();

  // Add the assertion in the function body
  if(requires.is_not_nil())
    goto_function.body.add(
      goto_programt::make_assertion(requires, requires.source_location()));
  // TODO: Add a comment in the source location of the assertion

  // Get the implementation function symbol
  //
  // Question: Should I do lookups on the symbol table or should I do
  // them on the namespace?
  const symbolt &impl_f_sym =
    symbol_table.lookup_ref(stub_name_of_function(function_id));

  // Make the function call to the implementation function
  code_function_callt call(impl_f_sym.symbol_expr());

  // Declare a variable to store the return value from the internal call
  symbol_exprt r = get_fresh_aux_symbol(
                     type.return_type(),
                     id2string(function_id) + "::ret_val",
                     "ret_val",
                     source_locationt(),
                     impl_f_sym.mode,
                     symbol_table)
                     .symbol_expr();

  replace_symbolt replace;

  if(type.return_type() != empty_typet())
  {
    // Declare the return variable and assign to it the return value
    // of the call
    goto_function.body.add(goto_programt::make_decl(r));
    call.lhs() = r;

    // Replace the return_value with r
    symbol_exprt ret_val(CPROVER_PREFIX "return_value", type.return_type());
    replace.insert(ret_val, r);
  }

  // Add the parameters as arguments to the call
  auto parameter_identifiers = type.parameter_identifiers();
  for(auto it = parameter_identifiers.begin();
      it != parameter_identifiers.end();
      it++)
  {
    const symbolt &parameter_symbol = ns.lookup(*it);
    call.arguments().push_back(parameter_symbol.symbol_expr());
  }

  goto_function.body.add(
    goto_programt::make_function_call(code_function_callt(call)));
  // Maybe: Add location/comments maybe?

  // Add the postcondition assumption
  if(ensures.is_not_nil())
  {
    exprt ensures_replaced = ensures;
    replace(ensures_replaced);
    goto_function.body.add(goto_programt::make_assumption(
      ensures_replaced, ensures.source_location()));
    // TODO: Add comment as is done in the loop code in code_contracts.cpp
  }

  if(type.return_type() != empty_typet())
  {
    code_returnt return_expr(r);
    goto_function.body.add(goto_programt::make_return(return_expr));
  }

  // Append the end of function instruction
  goto_function.body.add(
    goto_programt::make_end_function(ensures.source_location()));

  log.debug() << "Function body after adding the assumption: "
              << "\n";
  goto_function.body.output(ns, function_id, log.debug());
  log.debug() << messaget::eom;
  
  // Question: do I need to call some update or something after I do the changes?
}

bool function_stubst::operator()()
{
  // Get the body of the requested function to stub
  goto_functiont function_body;
  auto requested_function_body =
    goto_functions.function_map.find(function_name);
  if(requested_function_body == goto_functions.function_map.end())
  {
    log.error() << "The body of function: " << function_name
                << " doesn't exist in the goto_model\n"
                << messaget::eom;
    return true;
  }
  function_body.copy_from(requested_function_body->second);

  log.debug() << "Function: " << function_name << messaget::eom;

  // Add a declaration of the impl function, that will be called in the function body
  //
  // Problem: If we declare this to have a CPROVER PREFIX then dump c doesn't print it

  // Create a new function symbol for the internal implementation
  // function
  //
  // TODO: Change its metadata to be correct
  //
  // Question: Is it enough to add it in the symbol_table?
  //
  // Question: Should I make lookups on the symbol table or should I
  // make them on the namespace?
  if(!symbol_table.has_symbol(function_name))
  {
    log.error() << "Function: " << function_name
                << " doesn't exist in the symbol table"
                << messaget::eom;
    return true;
  }
  symbolt function_symbol = symbol_table.lookup_ref(function_name);
  const irep_idt stub_function_name = stub_name_of_function(function_name);
  function_symbol.name = stub_function_name;
  function_symbol.location = source_locationt();

  // Question: Maybe I should also change the module?

  // Question: Is it correct to change all names with that name?
  function_symbol.base_name = stub_function_name;
  function_symbol.pretty_name = stub_function_name;

  // Question: Is this the correct way to add the symbol to the symbol table? Does this change cascade to the namespace?
  //
  // Question: Should I somehow check and get a fresh name if this is already used?
  if(symbol_table.has_symbol(function_symbol.name))
  {
    log.error() << "The internal stub implementation name: "
                << function_symbol.name
                << " already exists in the symbol table"
                << messaget::eom;
    return true;
  }
  symbol_table.add(function_symbol);
  stub_function(function_name, function_body);

  // Delete all other functions and just keep the stub so that we can output it in C
  goto_functions.clear();
  goto_functions.update();
  goto_functions.function_map[function_name].copy_from(function_body);
  goto_functions.update();
  return false;
}

// This is copied from code_contracts.cpp
//
// Question: Probably something like that exists in some utils library
const symbolt &function_stubst::new_tmp_symbol(
  const typet &type,
  const source_locationt &source_location,
  const irep_idt &function_id,
  const irep_idt &mode)
{
  return get_fresh_aux_symbol(
    type,
    id2string(function_id) + "::tmp_cc",
    "tmp_cc",
    source_location,
    mode,
    symbol_table);
}

bool function_stubs(
  goto_modelt &goto_model,
  std::string function_name,
  messaget &log)
{
  return function_stubst(
    goto_model.symbol_table, goto_model.goto_functions, function_name, log)();
}

const std::string stub_name_of_function(const irep_idt &function_name)
{
  std::stringstream ss;
  ss << "__stub_" << function_name << "_impl";
  return ss.str();
}
