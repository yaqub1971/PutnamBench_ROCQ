(* ============================================================================
   PutnamBench 1962 B2 -- Rocq/MathComp proof.
   Problem: prove that there is a function f from the reals to the subsets of the
   natural numbers such that f(a) is a proper subset of f(b) whenever a < b.
   Statement: coq/src/putnam_1962_b2.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   The Theorem below is byte-identical to upstream; only one Import line, the
   definition of the witness and the proof script were added.
   Compat line: the line marked "(* compat: ... *)" was added because the upstream
   file does not compile at all on Rocq 9.1: a Variable outside a Section is an error
   since Rocq 9.0 (Coq 8.x only warns), and the upstream statement declares R this
   way. It does not change the meaning of the statement.
   The witness: f(a) is the set of codes (MathComp's pickle/unpickle encoding of the
   countable type rat) of the rationals q with q < a. It is monotone in a, and a
   rational strictly between a and b (rat_in_itvoo) makes the inclusion proper.
   Produced with Claude Fable 5.1 (Anthropic), September 2026; all checks run by the repository author.
   Verified on Rocq 9.1.0 / MathComp 2.5 (Rocq Platform 2026.07, macOS) and Coq 8.18.0 / MathComp 2.1.0 (Ubuntu 24.04):
   compiles; Print Assumptions putnam_1962_b2 lists only R (the Variable declared by
   the statement itself) and the three classical axioms that mathcomp.reals is built on
   (propositional_extensionality, functional_extensionality_dep,
   constructive_indefinite_description) -- nothing from the proof;
   rocqchk / coqchk: "Modules were successfully checked".
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1 / MathComp 2.5 (Rocq Platform 2026.07) the import line
   below triggers ~30 warnings emitted by MathComp itself (all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations). They are library
   warnings, not warnings about this file: none of this file's own lines produce any.
   The import line is kept exactly as upstream wrote it so that the statement stays
   identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals.
From mathcomp Require Import classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.
Open Scope classical_set_scope.

Import Order.Theory.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.

(* The witness: f a is the set of codes (via MathComp's countability of rat)
   of the rationals strictly below a. *)
Definition putnam_1962_b2_witness (a : R) : set nat :=
  [set n | exists q : rat, unpickle n = Some q /\ ratr q < a].

Theorem putnam_1962_b2
    : exists f : R -> set nat, forall a b : R, a < b -> f a `<` f b.
Proof.
exists putnam_1962_b2_witness => a b ab; split.
  (* monotone: a rational below a is below b *)
  by move=> n [q [nq qa]]; exists q; split => //; exact: lt_trans qa ab.
(* proper: a rational q with a < q < b is coded in f b but not in f a *)
have [q] := rat_in_itvoo ab; rewrite in_itv/= => /andP[aq qb].
move=> /(_ (pickle q) (ex_intro _ q (conj (pickleK q) qb))) [q' [+ q'a]].
rewrite pickleK => -[qq']; move: q'a; rewrite -qq' => qa.
by move: (lt_trans aq qa); rewrite ltxx.
Qed.
