(* ============================================================================
   PutnamBench 1967 B3 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: if f and g are continuous and periodic with period 1 on the real line, then
   lim_{n -> oo} int_0^1 f(x) g(n x) dx = (int_0^1 f(x) dx) (int_0^1 g(x) dx).
   Source: coq/src/putnam_1967_b3.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: it does not compile (see putnam_1967_b3.v). "-->" is
   applied directly to the sequence (fun n : nat => \int[mu]_(...) ...), a function
   nat -> R, where a filter is expected, so elaboration fails with
     The term "fun n : nat => ..." has type "nat -> R"
     while it is expected to have type "Filtered.sort ?s".
   The mathematics of the upstream statement is faithful; nothing else needed a change.
   Fix: exactly one change, in the conclusion, where "@ \oo" is inserted before "-->":
     : (fun n : nat => \int[mu]_(x in [set y | 0 < y < 1]) (f x * g (n%:~R * x))) -->
   becomes
     : (fun n : nat => \int[mu]_(x in [set y | 0 < y < 1]) (f x * g (n%:~R * x))) @ \oo -->
   "u @ \oo --> l" is MathComp-Analysis' "u n tends to l as n -> oo" (it unfolds, by
   reflexivity, to cvg_to (fmap u eventually) (nbhs l), convergence to the real number
   l), which is the limit the problem asks for and what PutnamBench's Lean statement
   says (Tendsto (fun n : Z => ...) atTop (nhds (...)); Lean lets n run through the
   integers, here n : nat as upstream wrote it: the same limit at +oo). Everything else
   is upstream's text and matches the problem: f, g : R -> R; "continuous f" is
   continuity at every point; "periodic f 1" is forall u, f (u + 1) = f u; in ring_scope
   "\int[mu]_(x in [set y | 0 < y < 1]) h x" is MathComp-Analysis' real-valued integral
   (Rintegral, the finite part of the Lebesgue integral) of h over the open interval
   (0, 1) for Lebesgue measure mu, which for the continuous integrands here is the
   ordinary int_0^1 h (the endpoints have measure 0); "n%:~R * x" is the real number n x.
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   text has constructs that the repository README documents as fatal or risky on
   Rocq 9.1 / MathComp 2.5: (1) a Variable outside a Section is an error since Rocq 9.0;
   (2) the ssralg re-import that protects the ring notations 1 and %:R. This file imports
   all_ssreflect BEFORE all_algebra (the reverse of the root files), so here the re-import
   is a no-op on MathComp 2.5 as well (checked: the theorem's type prints identically
   under Set Printing All with and without it); it is kept for uniformity with the
   repository. Neither line changes the meaning of the statement.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1; the first import line below triggers warnings emitted by MathComp itself
   (all_ssreflect deprecated since MathComp 2.5, ambiguous coercion paths, overridden
   notations). They are library warnings, not warnings about this file: none of this
   file's own lines produce any. The import lines are kept exactly as upstream wrote them
   so that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals normedtype trigo measure lebesgue_measure lebesgue_integral topology.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Definition mu := [the measure _ _ of @lebesgue_measure R].
Theorem putnam_1967_b3
    (f g : R -> R)
    (fgcont : continuous f /\ continuous g)
    (fgperiod : periodic f 1 /\ periodic g 1)
    : (fun n : nat => \int[mu]_(x in [set y | 0 < y < 1]) (f x * g (n%:~R * x))) @ \oo --> 
        (\int[mu]_(x in [set y | 0 < y < 1]) f x) * (\int[mu]_(x in [set y | 0 < y < 1]) g x).
Proof. Admitted.