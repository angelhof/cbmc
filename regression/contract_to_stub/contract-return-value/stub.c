#include <stub_header.h>

// __stub_stub_impl
// 
signed int __stub_stub_impl();

// stub
// file function.c line 4
signed int stub()
{
  signed int ret_val=__stub_stub_impl();
  __CPROVER_assume(ret_val == 42);
  return ret_val;
}

