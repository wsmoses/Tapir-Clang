// RUN: %clang_cc1 -std=c++1z -verify %s
// expected-no-diagnostics

int null();

int Cilk_for_tests(int n) {
  /* int n = 10; */
  /* _Cilk_for(int i = 0; i < n; i += 2); */
  /* _Cilk_for(int j = 0, __begin = 0, __end = n/2; __begin < __end; j += 2, __begin++); */
  _Cilk_for (int i = 0; i < n; ++i) null();
  _Cilk_for (int i = 0, __end = n; i < __end; ++i) null();
  unsigned long long m = 10;
  _Cilk_for (int i = 0; i < m; ++i) null();
  _Cilk_for (int i = 0, __end = m; i < __end; ++i) null();
  return 0;
}

int pragma_tests(int n) {
#pragma clang loop unroll_count(4)
  _Cilk_for (int i = 0; i < n; ++i) null();

  return 0;
}

int scope_tests(int n) {
  int A[5];
  _Cilk_for(int i = 0; i < n; ++i) {
    int A[5];
    A[i%5] = i;
  }
  for(int i = 0; i < n; ++i) {
    A[i%5] = i%5;
  }
  return 0;
}
