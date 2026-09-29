(* ============================================================================
   PutnamBench 1966 A1 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1966_a1.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim (no compat lines were needed:
   the file declares no Variable outside a Section, imports ssralg after all_ssreflect,
   and uses no derivative notation).
   Problem: let a_n = n/2 for n even and (n-1)/2 for n odd (the sequence 0, 1, 1, 2, 2, 3, ...)
   and let f(n) be the sum of its first n terms, f(n) = a_1 + ... + a_n = a_0 + ... + a_n;
   show that x y = f(x+y) - f(x-y) for all positive integers x > y.
   Defect (audit verdict: false, machine-checked): the terms of the sequence are written
   "(m%:Z)/2" and "(m%:Z-1)/2" in ring_scope on int, where "x / y" is x * y^-1 and the
   inverse of MathComp's int is the identity function ("Definition invz n : int := n." in
   ssrint.v: the only units are 1 and -1). So "/ 2" multiplies by 2, the encoded sequence
   is 0, 0, 4, 4, 8, 8, 12, 12, ... (four times the intended 0, 0, 1, 1, 2, 2, 3, 3, ...),
   the encoded f is four times the intended f, and the theorem claims x y = 4 x y. At
   x = 2, y = 1 it asserts 2 = f 3 - f 1 = 8 - 0. Proof: putnam_1966_a1_statement_is_false.v.
   Proposed fix (two subterms of the definition of f): putnam_1966_a1_corrected.v.
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
    (f : nat -> int := fun n => \sum_(0 <= m < n + 1) (if (~~odd m) then (m%:Z)/2 else (m%:Z-1)/2))
    : forall x y : nat, (gt x 0) -> (gt y 0) -> gt x y -> (x * y)%:Z = f (Nat.add x y) - f (Nat.sub x y).
Proof. Admitted.