(* ============================================================================
   PutnamBench 1966 A1 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: let a_n = n/2 for n even and (n-1)/2 for n odd (the sequence 0, 1, 1, 2, 2, 3, ...)
   and let f(n) be the sum of its first n terms, f(n) = a_1 + ... + a_n = a_0 + ... + a_n;
   show that x y = f(x+y) - f(x-y) for all positive integers x > y.
   Source: coq/src/putnam_1966_a1.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: the terms of the sequence are written "(m%:Z)/2" and
   "(m%:Z-1)/2" in ring_scope on int, where "x / y" is x * y^-1 and the inverse of MathComp's
   int is the identity function ("Definition invz n : int := n." in ssrint.v: the only units
   are 1 and -1). So "/ 2" multiplies by 2, the encoded sequence is 0, 0, 4, 4, 8, 8, ...
   (four times the intended 0, 0, 1, 1, 2, 2, ...), the encoded f is four times the intended f,
   and the theorem claims x y = 4 x y: at x = 2, y = 1 it asserts 2 = f 3 - f 1 = 8 - 0, so it
   is FALSE (putnam_1966_a1_statement_is_false.v derives False from it).
   Fix: apart from this header comment, this file differs from putnam_1966_a1.v (the upstream
   statement) in the two divisions inside the definition of f only:
     "(m%:Z)/2"    ->  "(m %/ 2)%:Z"        (Euclidean division of the natural number m by 2,
                                             then the cast to int)
     "(m%:Z-1)/2"  ->  "((m - 1) %/ 2)%:Z"  (the same for m - 1; m is odd in this branch, so
                                             m - 1 is an exact natural-number subtraction)
   "%/" is MathComp's division of natural numbers (divn), which is exactly what n/2 for even n
   and (n-1)/2 for odd n mean in the problem; the encoded terms are now 0, 0, 1, 1, 2, 2, 3, 3,
   ... as intended. Everything else is upstream's and faithful: f n sums the terms of index
   0 <= m <= n (the Lean statement's Finset.Icc 0 n), which is a_1 + ... + a_n because a_0 = 0,
   i.e. the sum of the first n terms of the sequence 0, 1, 1, 2, 2, 3, ... of the problem (the
   alternative reading a_0 + ... + a_(n-1) would make the identity false already at x = 2,
   y = 1); x and y are natural numbers with x > 0, y > 0, x > y (Coq's gt); x + y and x - y
   are Nat.add and Nat.sub, exact since x > y. The Lean statement divides in the integers
   (Int "/", floor division on nonnegative arguments); dividing the natural number before
   the cast is the same function on 0 <= m and needs no additional import (intdiv, which
   provides "%/" on int, is not among the upstream imports).
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the import line below triggers library warnings emitted by MathComp
   itself (overridden notations, ambiguous coercion paths). They are library warnings, not
   warnings about this file: none of this file's own lines produce any. The import line is
   kept exactly as upstream wrote it so that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_ssreflect ssrnum ssralg ssrint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Theorem putnam_1966_a1
    (f : nat -> int := fun n => \sum_(0 <= m < n + 1) (if (~~odd m) then (m %/ 2)%:Z else ((m - 1) %/ 2)%:Z))
    : forall x y : nat, (gt x 0) -> (gt y 0) -> gt x y -> (x * y)%:Z = f (Nat.add x y) - f (Nat.sub x y).
Proof. Admitted.
