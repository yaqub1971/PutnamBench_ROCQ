(* ============================================================================
   PutnamBench 1965 B4 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: for real x and integers n >= 1 let
   f(x, n) = (C(n,0) + C(n,2) x + C(n,4) x^2 + ...) / (C(n,1) + C(n,3) x + C(n,5) x^2 + ...);
   express f(x, n+1) as a rational function of f(x, n) and x, and find lim_{n -> oo} f(x, n)
   for every x at which the limit exists. Answer: f(x, n+1) = (f(x, n) + x) / (f(x, n) + 1);
   the limit exists exactly for x >= 0 and equals sqrt x.
   Source: coq/src/putnam_1965_b4.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: (1) the sum bounds "n%/2 .+1" and "(n.-1)%/2 .+1" of hu
   and hv parse as n %/ (2.+1) = n %/ 3 and (n.-1) %/ 3 (the postfix ".+1" binds tighter than
   "%/"), so u n x is the empty sum 0 for n <= 2, v n x is 0 for n <= 3, and both are
   truncated sums for larger n; (2) the denominator uses the even binomial coefficients
   "'C(n, 2 * (i.+1))" = C(n, 2i+2) where the problem has the odd ones C(n, 2i+1). At n = 5,
   x = 1 the encoded recurrence claims 16/15 = 1, so the upstream theorem is FALSE
   (derivation in putnam_1965_b4_statement_is_false.v).
   Fix (apart from this header, exactly two lines differ from putnam_1965_b4.v):
     hu: "\sum_(0 <= i < n%/2 .+1) ('C(n, 2 * i)%:R * x^i)"
      -> "\sum_(0 <= i < (n%/2).+1) ('C(n, 2 * i)%:R * x^i)"
         i.e. i = 0, ..., n %/ 2 with the even binomials C(n, 0), C(n, 2), ..., C(n, 2 (n %/ 2)):
         the numerator of the problem, and the Lean statement's "Finset.Icc 0 (n / 2)" with
         "n.choose (2 * i)";
     hv: "\sum_(0 <= i < (n.-1)%/2 .+1) ('C(n, 2 * (i.+1))%:R * x^i)"
      -> "\sum_(0 <= i < ((n.-1)%/2).+1) ('C(n, 2 * i + 1)%:R * x^i)"
         i.e. i = 0, ..., (n-1) %/ 2 with the odd binomials C(n, 1), C(n, 3), ...: the
         denominator of the problem, and the Lean statement's "Finset.Icc 0 ((n - 1) / 2)"
         with "n.choose (2 * i + 1)".
   With these definitions Pascal's rule gives u n.+1 x = u n x + x * v n x and
   v n.+1 x = u n x + v n x, hence the recurrence f n.+1 x = (f n x + x) / (f n x + 1) of the
   first conjunct wherever its guards hold, and the two limit conjuncts state the textbook
   answer (the limit exists exactly for x >= 0 and is sqrt x). Everything else -- the
   solution tuple, the recurrence conjunct with its three non-vanishing guards, the limit
   set, the limit function, and "x^i" (exprz with the exponent Posz i, i.e. x ^+ i) -- is
   upstream's, is faithful, and agrees with the Lean statement; as there, a division by
   zero is the library's 0 and the guards keep the recurrence away from it.
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a
   Section is an error since Rocq 9.0; (2) with MathComp 2.5, importing all_ssreflect
   after all_algebra (upstream's order) overrides the ring notations 1 and %:R, so
   ssralg is re-imported. Neither changes the meaning of the statement.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. The first "From mathcomp Require Import" line below triggers warnings
   emitted by MathComp itself (30 on Rocq 9.1.1 / MathComp 2.5.0: all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations;
   23 on Coq 8.18.0 / MathComp 2.1.0). They are library warnings, not warnings about this
   file: none of this file's own lines produce any. The import lines are kept exactly as
   upstream wrote them so that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals normedtype sequences topology.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Definition putnam_1965_b4_solution : ((((R -> R) -> (R -> R)) * ((R -> R) -> (R -> R))) * ((set R) * (R -> R))) := 
((fun h : R -> R => (fun x : R => h x + x), fun h : R -> R => (fun x => h x + 1)), ([set x : R | x >= 0], @Num.sqrt R)).
Theorem putnam_1965_b4
    (f u v : nat -> R -> R)
    (hu : forall n : nat, gt n 0 -> forall x : R, u n x = \sum_(0 <= i < (n%/2).+1) ('C(n, 2 * i)%:R * x^i))
    (hv : forall n : nat, gt n 0 -> forall x : R, v n x = \sum_(0 <= i < ((n.-1)%/2).+1) ('C(n, 2 * i + 1)%:R * x^i))
    (hf : forall n : nat, gt n 0 -> forall x : R, f n x = u n x / v n x)
    (n : nat)
    (hn : gt n 0)
    (f_seq : R -> (nat -> R) := fun (x : R) => fun (m : nat) => f m x) :
    let '((p, q), (s, g)) := putnam_1965_b4_solution in
        (forall x : R, v n x <> 0 -> v (n.+1) x <> 0 -> q (f n) x <> 0 -> f (n.+1) x = p (f n) x / q (f n) x) /\
        s = [set x : R | exists l : R, f_seq x @ \oo --> l] /\
        (forall x : R, x \in s -> (f_seq x) @ \oo --> g x).
Proof. Admitted.