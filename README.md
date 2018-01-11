Tapir-Clang
================================

This version of Clang enables compilation of various parallel languages to the Tapir extension to LLVM (https://github.com/wsmoses/Tapir-LLVM).

## Cilk
This repository provides an implementation of Cilk's front-end (which is compiled to Tapir). It supports the `_Cilk_spawn`, `_Cilk_sync`, and `_Cilk_for` keywords from Cilk. In a traditional `_Cilk_spawn` (as in the following example), the call arguments and function
arguments are evaluated before the spawn occurs.

```
int x = _Cilk_spawn foo(n);
```

For convenience, we also implemented a variant of `_Cilk_spawn` that spawns arbitrary blocks of code as follows. In a statement written this way, all variables and statements are evaluated after the spawn occurs.

```
_Cilk_spawn { x = foo(n); }
```

Please use this syntax with caution!  When spawning an arbitrary statement, the spawn occurs before the evaluation of any part of the
spawned statement.  Furthermore, some statements, such as `goto`, are not legal to spawn.
