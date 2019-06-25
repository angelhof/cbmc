/*******************************************************************\

Module: Create function stubs in C from code contracts

Author: Konstantinos Kallas

Date: July 2019

\*******************************************************************/

/// \file
/// Create function stubs in C from code contracts

#include "function_stubs.h"

#include <fstream>
#include <iostream>

#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/replace_symbol.h>

#include <goto-programs/remove_skip.h>

#include <analyses/local_may_alias.h>

#include <linking/static_lifetime_init.h>

#include "function_modifies.h"
#include "loop_utils.h"

class function_stubst
{
public:
  function_stubst(
    symbol_tablet &_symbol_table,
    goto_functionst &_goto_functions,
    std::string _function_name)
    : ns(_symbol_table),
      symbol_table(_symbol_table),
      goto_functions(_goto_functions),
      function_name(_function_name),
      temporary_counter(0)
  {
  }

  void operator()();

protected:
  namespacet ns;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;
  const std::string function_name;

  unsigned temporary_counter;

  std::unordered_set<irep_idt> summarized;

  void stub_function(
    const irep_idt &function_id,
    goto_functionst::goto_functiont &goto_function,
    function_modifiest function_modifies);

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
  goto_functionst::goto_functiont &goto_function,
  function_modifiest function_modifies)
{
  // Get the function requires and ensures
  const symbolt &f_sym = ns.lookup(function_id);
  const code_typet &type = to_code_type(f_sym.type);

  const exprt &requires =
    static_cast<const exprt &>(type.find(ID_C_spec_requires));
  const exprt &ensures =
    static_cast<const exprt &>(type.find(ID_C_spec_ensures));

  // TODO: We probably have to produce a warning or exit if there is
  // no contract.

  // Question: What about variables that were declared in the function
  // body but are contained in the ensures?

  // Find what is modified in the function.
  //
  // Question: Is this a sound analysis? If so, then it will also
  // havoc memory locations?
  //
  // There is another problem. The modifies analysis should happen
  // before the stubs because otherwise havocing some modified
  // variable may make the approximation more loose if we then do an
  // analysis on a function that calls the already havoced function.
  modifiest modifies;
  local_may_aliast local_may_alias(goto_function);
  const goto_programt &goto_program = goto_function.body;

  // get_modifies(local_may_alias, goto_program, modifies)

  // Run the modifies analysis for all instructions in the goto
  // program
  forall_goto_program_instructions(i_it, goto_program)
    function_modifies.get_modifies(local_may_alias, i_it, modifies);

  // Clear the function body
  goto_function.body.clear();

  // Add the assertion in the function body
  if(requires.is_not_nil())
    goto_function.body.add(
      goto_programt::make_assertion(requires, requires.source_location()));
  // TODO: Add a comment in the source location of the assertion

  // Havoc the may-change variables.
  //
  // TODO: This probably needs improvement. I am not sure whether it
  // is really sound havoc. Whether it really havocs all the necessary
  // variables/memory locations.
  //
  // Question: This is defined in loop_utils. Does this only work for
  // loop code? Inspect and make sure that it works for any code.
  //
  // Problem: Havoc introduces a lot of random variables and havocs
  // them so we should probably do some unused variable analysis after
  // the stub generation to cut them
  //
  // Problem: The havoc doesn't havoc any memory location
  //
  // Problem: The modifies analysis doesnt find that dst of memcpy is
  // indeed modified and so it doesn't havoc it.
  //
  // build_havoc_code_at_source_location(requires.source_location(), modifies, goto_function.body);

  // Get the implementation function symbol
  const symbolt &impl_f_sym =
    symbol_table.lookup_ref(impl_fun_name(id2string(function_id)));

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

  if(type.return_type() != empty_typet())
  {
    // Declare the return variable and assign to it the return value
    // of the call
    goto_function.body.add(goto_programt::make_decl(r));
    call.lhs() = r;
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
    goto_function.body.add(
      goto_programt::make_assumption(ensures, ensures.source_location()));
  // TODO: Add comment as is done in the loop code

  if(type.return_type() != empty_typet())
  {
    code_returnt return_expr(r);
    goto_function.body.add(goto_programt::make_return(return_expr));
  }

  // Append the end of function instruction
  goto_function.body.add(
    goto_programt::make_end_function(ensures.source_location()));

  std::cout << "Function body after adding the assumption: "
            << "\n";
  goto_function.body.output(ns, function_id, std::cout);

  // Question: do I need to call some update or something after I do the changes?
}

void function_stubst::operator()()
{
  // We should first find all the modifies of all functions, and then
  // stub out the ones that we want.
  //
  // Question: Is it safe to change the goto_functions after giving
  // them to function_modifies?

  // Do the function_modifies analysis to all goto_functions.
  function_modifiest function_modifies(goto_functions);

  // Get the body of the requested function to stub
  goto_functiont function_body;
  // There should be some error checking/handling here
  function_body.copy_from(goto_functions.function_map.at(function_name));

  std::cout << "Function: " << function_name << "\n";

  // Add a declaration of the impl function, that will be called in the function body
  //
  // Problem: If we declare this to have a CPROVER PREFIX then dump c doesn't print it

  // Create a new function symbol for the internal implementation
  // function
  //
  // TODO: Change its metadata to be correct
  //
  // Question: Is it enough to add it in the symbol_table?
  symbolt function_symbol = symbol_table.lookup_ref(function_name);
  function_symbol.name = impl_fun_name(function_name);
  function_symbol.location = source_locationt();

  // Question: Maybe I should also change the module?

  // Question: Is it correct to change all names with that name?

  function_symbol.base_name = impl_fun_name(function_name);
  function_symbol.pretty_name = impl_fun_name(function_name);
  // std::cout << function_symbol << "\n";

  // Question: Is this the correct way to add the symbol to the symbol table? Does this change cascade to the namespace?
  //
  // Question: Should I somehow check and get a fresh name if this is already used?
  INVARIANT(
    !symbol_table.has_symbol(function_symbol.name),
    "The implementation symbol shouldn't exist in the symbol table.");
  symbol_table.add(function_symbol);

  // Question: Is it correct to call stub_function with
  // function_modifies initialized with goto_functions and here
  // have stub_functions? Could something go wrong?
  stub_function(function_name, function_body, function_modifies);

  // TODO: Find a way to not include any necessary header file in the
  // stub. Maybe add the name of a header file as a second cmdline
  // argument.

  // Delete all other functions and just keep the stub so that we can output it in C
  goto_functions.clear();
  goto_functions.update();
  goto_functions.function_map[function_name].copy_from(function_body);
  goto_functions.update();

  // TODO: Output C properly and not by calling dump-c.
}

// This is copied from code_contracts
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

void function_stubs(goto_modelt &goto_model, std::string function_name)
{
  function_stubst(
    goto_model.symbol_table, goto_model.goto_functions, function_name)();
}

const std::string impl_fun_name(const std::string function_name)
{
  return "__stub_" + function_name + "_impl";
}
