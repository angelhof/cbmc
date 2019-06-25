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

class goto_modelt;

void function_stubs(goto_modelt &, std::string function_name);

const std::string impl_fun_name(const std::string function_name);

#endif // CPROVER_GOTO_INSTRUMENT_FUNCTION_STUBS_H
