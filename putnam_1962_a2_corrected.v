(* ============================================================================
   PutnamBench 1962 A2 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof). Proved in putnam_1962_a2_corrected_proof.v.
   Apart from this header comment and the marked compat lines, differs from
   putnam_1962_a2.v (the upstream statement) only in the definition of
   putnam_1962_a2_solution: the one-case answer a / (1 - c x)^2 is replaced by the
   four-case solution set of PutnamBench's Lean statement of the same problem,
   transcribed to Rocq (the textbook family; its truncation past x = 1/c, where the
   integral becomes infinite and the average therefore 0; the functions vanishing on
   (0, +oo) with an arbitrary nonnegative value at 0; and the functions with f 0 = 0
   whose integral over [0, x] vanishes on an initial interval). With the one-case
   answer the theorem is false: see putnam_1962_a2_statement_is_false.v.
   Reading the statement: "\int[mu]_(t in D) f t" in ring_scope is MathComp-Analysis'
   real-valued integral (Rintegral), i.e. the finite part of the Lebesgue integral,
   which is 0 when the integral is infinite; mu is Lebesgue measure.
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp 2.5: (1) a Variable outside a
   Section is an error since Rocq 9.0; (2) with MathComp 2.5, importing all_ssreflect
   after all_algebra (upstream's order) overrides the ring notations 1 and %:R, so
   ssralg is re-imported. Neither changes the meaning of the statement.
   Verified: compiles on Rocq 9.1.0 / MathComp 2.5 / MathComp-Analysis 1.16.0 (Rocq Platform 2026.07, macOS) and Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1 / MathComp 2.5 (Rocq Platform 2026.07) the import lines
   below trigger ~30 warnings emitted by MathComp itself (all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations). They are library
   warnings, not warnings about this file: none of this file's own lines produce any.
   The import lines are kept exactly as upstream wrote them so that the statement stays
   identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals normedtype sequences topology derive measure lebesgue_measure lebesgue_integral.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
From mathcomp Require Import classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Definition mu := [the measure _ _ of @lebesgue_measure R].
(* Proposed fix: the solution set of the Lean statement of this problem, transcribed.
   The upstream set (the first disjunct alone) misses three families of solutions:
   the truncated functions (integral +oo, hence average 0, past x = 1/c), the functions
   that vanish on (0, +oo) with an arbitrary nonnegative value at 0, and the functions
   with f 0 = 0 whose integral over [0, x] vanishes on an initial interval. *)
Definition putnam_1962_a2_solution : set (R -> R) := [set f |
     (exists a c : R, a >= 0 /\ f = (fun x : R => a / (1 - c * x) ^ 2))
  \/ (exists a c : R, a >= 0 /\ 0 < c /\ f = (fun x : R => if x < 1 / c then a / (1 - c * x) ^ 2 else 0))
  \/ ((forall x, f x >= 0) /\ forall x : R, 0 < x -> f x = 0)
  \/ (exists e : R, 0 < e /\ f 0 = 0 /\ (forall x, f x >= 0) /\
        forall x : R, 0 < x < e -> \int[mu]_(t in [set t | 0 <= t <= x]) f t = 0)].
Theorem putnam_1962_a2
    (P : (set R) -> (R -> R) -> Prop)
    (P_def : forall s f, P s f <-> ((forall x, f x >= 0) /\ forall x, x \in s -> 
                1/x * \int[mu]_(t in [set t | 0 <= t <= x]) f t = Num.sqrt (f 0 * f x)))
    : (forall f,
        (P [set t | 0 < t] f -> exists g, g \in putnam_1962_a2_solution /\ (forall x : R, x > 0 -> f x = g x)) /\
        (forall e, 0 < e -> P [set t | 0 < t < e] f -> exists g, g \in putnam_1962_a2_solution /\ (forall x : R, 0 <= x < e -> f x = g x))) /\
        forall f, f \in putnam_1962_a2_solution -> P [set t | 0 < t] f \/ exists e, 0 < e /\ P [set t | 0 < t < e] f.
Proof. Admitted.
