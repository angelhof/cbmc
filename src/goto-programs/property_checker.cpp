/*******************************************************************\

Module: Property Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Property Checker Interface

#include "property_checker.h"

std::string property_resultst::as_string(resultt result)
{
  switch(result)
  {
  case property_resultst::resultt::PASS:
    return "OK";
  case property_resultst::resultt::FAIL:
    return "FAILURE";
  case property_resultst::resultt::ERROR:
    return "ERROR";
  case property_resultst::resultt::UNKNOWN:
    return "UNKNOWN";
  }

  return "";
}

void property_resultst::initialize(const goto_functionst &goto_functions)
{
  forall_goto_functions(it, goto_functions)
    if(!it->second.is_inlined() ||
       it->first==goto_functions.entry_point())
    {
      const goto_programt &goto_program=it->second.body;

      forall_goto_program_instructions(i_it, goto_program)
      {
        if(!i_it->is_assert())
          continue;

        const source_locationt &source_location=i_it->source_location;

        irep_idt property_id=source_location.get_property_id();

        property_statust &property_status=property_map[property_id];
        property_status.result=resultt::UNKNOWN;
        property_status.location=i_it;
      }
    }
}

property_checkert::property_checkert(message_handlert &_message_handler)
  : messaget(_message_handler)
{
}
