/*******************************************************************\

Module: Turn pre and post conditions to code contracts

Author: Konstantinos Kallas

Date: July 2019

\*******************************************************************/

/// \file
/// Turns the pre and postconditions of all functions to code contracts.

#ifndef CPROVER_GOTO_INSTRUMENT_PRE_POSTCONDITIONS_TO_CONTRACTS_H
#define CPROVER_GOTO_INSTRUMENT_PRE_POSTCONDITIONS_TO_CONTRACTS_H

#include <string>

class goto_modelt;

void pre_postconditions_to_contracts(goto_modelt &);

#endif // CPROVER_GOTO_INSTRUMENT_PRE_POSTCONDITIONS_TO_CONTRACTS_H
