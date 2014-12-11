loop
====
François Pottier, INRIA Paris-Rocquencourt.

Compiled with Coq 8.4pl2.

This little library is supposed to help define a simple do/while loop in Coq
(that is, a simple tail-recursive function), in such a way that the extracted
OCaml code is also a clean loop.

The user provides the loop body. The body must have type `S -> S + T`, which
means that, given a current state of type S, the loop body either produces a
new state (and the loop will continue) or produces a final result (and the
loop will stop).

The user must also provide a well-founded ordering on the type S and a proof
that the loop body respects this ordering.

The library constructs the loop, a total function of type S -> T, and
establishes several properties of this function, including a fixed point
equation and a Hoare-style rasoning rule.

The file Loop.v contains the library. It is organized in three parts:

  1. Part 1 covers the simple case (described above) where the loop is total,
     i.e., for every initial state of type S, termination is guaranteed.

  2. Part 2 covers the more complex case where the loop is partial, i.e., an
     invariant I must be imposed on the current state in order to guarantee
     termination. In that case, a loop can still be constructed, but it is a
     function of type { s | I s } -> T.

  3. Part 3 offers a facility to define a new loop as a refinement of an
     existing loop, without being forced to re-establish the termination of
     the new loop.

The file MyWf.v contains a few lemmas about well-foundedness, which the end
user does not need to worry about.

The file LoopDemo.v contains demos of parts 1 and 2. (There is no demo of
part 3 for the moment.)

The second demo, in particular, is still rather clumsy. Suggestions for
improvement are welcome!
