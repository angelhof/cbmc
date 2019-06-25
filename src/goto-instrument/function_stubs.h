/*******************************************************************\

Module: Create function stubs in C from code contracts

Author: Konstantinos Kallas

Date: July 2019

\*******************************************************************/

/// \file
/// Create function stubs in C from code contracts

#ifndef CPROVER_GOTO_INSTRUMENT_FUNCTION_STUBS_H
#define CPROVER_GOTO_INSTRUMENT_FUNCTION_STUBS_H

#include <string>

#include "util/irep.h"
#include "util/message.h"

class goto_modelt;

// This function creates a stub for the specified [function_name]. It
// is required that the function with [function_name] exists in the
// goto_model.
//
// The stub generation mechanism uses the contract of the specified
// function. It asserts the contract requirements, and in the end it
// assumes what the contract ensures. In between, it calls a function
// with name stub_name_of_function(function_name) that is meant as a
// placeholder for any custom implementation needed in the stub.
bool function_stubs(goto_modelt &, std::string function_name, messaget &log);

// This function outputs the stub implementation name for the given
// [function_name].
const std::string stub_name_of_function(const irep_idt &function_name);

#endif // CPROVER_GOTO_INSTRUMENT_FUNCTION_STUBS_H
