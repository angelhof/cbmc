/*******************************************************************\

Module: Turn pre and post conditions to code contracts

Author: Konstantinos Kallas

Date: July 2019

\*******************************************************************/

/// \file
/// Turns the pre and postconditions of all functions to code contracts.

#include "pre_postconditions_to_contracts.h"

#include <fstream>
#include <iostream>

#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/replace_symbol.h>

#include <goto-programs/remove_skip.h>

#include <analyses/local_may_alias.h>

#include <linking/static_lifetime_init.h>

#include "loop_utils.h"
#include "function_modifies.h"

class pre_postconditions_to_contractst
{
public:
  pre_postconditions_to_contractst(
    symbol_tablet &_symbol_table,
    goto_functionst &_goto_functions):
      ns(_symbol_table),
      symbol_table(_symbol_table),
      goto_functions(_goto_functions),
      temporary_counter(0)
  {
  }

  void operator()();

protected:
  namespacet ns;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;
  
  unsigned temporary_counter;

  std::unordered_set<irep_idt> summarized;

  void function_pre_postconditions_to_contracts(
    const irep_idt &function_id,
    goto_functionst::goto_functiont &goto_function);
};

void pre_postconditions_to_contractst::function_pre_postconditions_to_contracts(
  const irep_idt &function_id,
  goto_functionst::goto_functiont &goto_function)
{ 

  

  // For each function, we need to find the preconditions (from the start)

  // Then we need to find all postconditions

  // We then need to aggregate them and extend the contracts

  // Issues:
  //
  // - It seems much harder to reconstruct the initial pre and
  //   postconditions from the goto-code as there are several
  //   transformations happening in between. It is possible, but seems
  //   not worth it for the complexity.
  //
  // - If we do some trick where we save the whole pre and
  //   postconditions as text in the comment of the asserts, then we
  //   won't be able to make any checks, such as checking that the
  //   variables in the assertions are all arguments of the function
  //   (and not declared in it). Also I will not be able to check
  //   whether pre and postconditions are indeed in the beginning or
  //   the end, as someone could just move them anywhere. Also it
  //   doesn't seem straightforward how to connect the postconditions
  //   in one big expression, as it will not be easy to find different
  //   groups of postconditions.
  // 
  // - How could we solve this? Find all pre and postcondition asserts
  //   and go back from them to reconstruct the conditions. This seems
  //   wrong and very difficult.
  //
  // - Another way might be to let them be functions for specific
  //   function names, so that we can get them in goto. This actually
  //   doesn't solve the problem, because from what it seems GOTO is
  //   flat in the sense that it doesn't allow for nested function
  //   calls. Therefore not turning them into asserts, just saves us
  //   from the need to annotate them, but nothing else. The problem
  //   is that the flattening and any simplification of the GOTO loses
  //   a lot of the syntactic information, which we would later need
  //   to reconstruct.
  //
  // Conclusion: Because of the above it seems to me that doing this
  //             on the AST is much better. I don't remember what the
  //             problem with doing it on the AST is exactly.

  std::cout << "Function: " << function_id << "\n";

  if(function_id == "s_sift_down")
  {
    goto_function.body.output(ns, function_id, std::cout);
  }
  
  return;

  // // Get the function requires and ensures
  // const symbolt &f_sym=ns.lookup(function_id);
  // const code_typet &type=to_code_type(f_sym.type);
  
  // const exprt &requires=
  //   static_cast<const exprt&>(type.find(ID_C_spec_requires));
  // const exprt &ensures=
  //   static_cast<const exprt&>(type.find(ID_C_spec_ensures));

  // // TODO: We probably have to produce a warning or exit if there is
  // // no contract.
 
  // // Question: What about variables that were declared in the function
  // // body but are contained in the ensures?

  // // Find what is modified in the function.
  // //
  // // Question: Is this a sound analysis? If so, then it will also
  // // havoc memory locations?
  // //
  // // There is another problem. The modifies analysis should happen
  // // before the stubs because otherwise havocing some modified
  // // variable may make the approximation more loose if we then do an
  // // analysis on a function that calls the already havoced function.
  // modifiest modifies;
  // local_may_aliast local_may_alias(goto_function);
  // const goto_programt &goto_program = goto_function.body;

  // // get_modifies(local_may_alias, goto_program, modifies)

  // // Run the modifies analysis for all instructions in the goto
  // // program
  // forall_goto_program_instructions(i_it, goto_program)
  //   function_modifies.get_modifies(local_may_alias, i_it, modifies);

  // // Clear the function body
  // goto_function.body.clear();

  // // Add the assertion in the function body
  // if(requires.is_not_nil())
  //   goto_function.body.add(
  //     goto_programt::make_assertion(requires,
  //                                   requires.source_location()));
  //   // TODO: Add a comment in the source location of the assertion


  
  // // Havoc the may-change variables.
  // //
  // // TODO: This probably needs improvement. I am not sure whether it
  // // is really sound havoc. Whether it really havocs all the necessary
  // // variables/memory locations.
  // //
  // // Question: This is defined in loop_utils. Does this only work for
  // // loop code? Inspect and make sure that it works for any code.
  // //
  // // Problem: Havoc introduces a lot of random variables and havocs
  // // them so we should probably do some unused variable analysis after
  // // the stub generation to cut them
  // //
  // // Problem: The havoc doesn't havoc any memory location
  // //
  // // Problem: The modifies analysis doesnt find that dst of memcpy is
  // // indeed modified and so it doesn't havoc it.
  // //
  // // build_havoc_code_at_source_location(requires.source_location(), modifies, goto_function.body);

  // // Get the implementation function symbol
  // const symbolt &impl_f_sym =
  //   symbol_table.lookup_ref(
  //     impl_fun_name(
  //       id2string(
  //         function_id)));

  // // Make the function call to the implementation function
  // code_function_callt call(impl_f_sym.symbol_expr());

  // // Declare a variable to store the return value from the internal call
  // symbol_exprt r =
  //   get_fresh_aux_symbol(
  //     type.return_type(),
  //     id2string(function_id) + "::ret_val",
  //     "ret_val",
  //     source_locationt(),
  //     impl_f_sym.mode,
  //     symbol_table)
  //   .symbol_expr();

  // if(type.return_type()!=empty_typet())
  // {
  //   // Declare the return variable and assign to it the return value
  //   // of the call
  //   goto_function.body.add(goto_programt::make_decl(r));
  //   call.lhs()=r;
  // }
  
  // // Add the parameters as arguments to the call
  // auto parameter_identifiers = type.parameter_identifiers();
  // for (auto it=parameter_identifiers.begin(); it!=parameter_identifiers.end(); it++) {
  //   const symbolt &parameter_symbol = ns.lookup(*it);
  //   call.arguments().push_back(parameter_symbol.symbol_expr());
  // }

  // goto_function.body.add(
  //   goto_programt::make_function_call(
  //     code_function_callt(call)));
  // // Maybe: Add location/comments maybe?
  
  // // Add the postcondition assumption
  // if(ensures.is_not_nil())
  //   goto_function.body.add(
  //     goto_programt::make_assumption(ensures,
  //                                    ensures.source_location()));
  // // TODO: Add comment as is done in the loop code

  // if(type.return_type()!=empty_typet())
  // {
  //   code_returnt return_expr(r);
  //   goto_function.body.add(goto_programt::make_return(return_expr));
  // }
  
  // // Append the end of function instruction
  // goto_function.body.add(goto_programt::make_end_function(ensures.source_location()));
  
  // std::cout << "Function body after adding the assumption: " << "\n";
  // goto_function.body.output(ns, function_id, std::cout);

  // // Question: do I need to call some update or something after I do the changes?
} 

void pre_postconditions_to_contractst::operator()()
{
  // For each function, turn the pre and postconditions to contracts
  Forall_goto_functions(it, goto_functions)
  {
    function_pre_postconditions_to_contracts(it->first, it->second);
  }
}


void pre_postconditions_to_contracts(goto_modelt &goto_model)
{
  pre_postconditions_to_contractst(goto_model.symbol_table, goto_model.goto_functions)();
}

