#include <stub_header.h>

// __stub_stub_impl
// 
void __stub_stub_impl(signed int *x);

// stub
// file function.c line 2
void stub(signed int *x)
{
  assert(*x == 1);
  __stub_stub_impl(x);
  __CPROVER_assume(*x == 5);
}

