# Cilk-Clang

This version of Clang supports the '_Cilk_spawn' and '_Cilk_sync'
keywords.  These keywords don't quite work the same way as they do in
Cilk.  In particular, the '_Cilk_spawn' keyword supports spawning a
statement.  Suppose, for example, that you wrote the following in Cilk
proper:

x = _Cilk_spawn fib(n-1);

In this version of Clang, you would write this:

_Cilk_spawn x = fib(n-1);

Alternatively, you could write this:

_Cilk_spawn { x = fib(n-1); }

In the future, we'll add support for _Cilk_for and spawning of
declarations.  For now, however, this version of Clang should allow us
to compile Cilk code into parallel LLVM IR with relatively little
modification to that Cilk code.