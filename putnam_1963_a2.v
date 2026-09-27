(* ============================================================================
   PutnamBench 1963 A2 -- Rocq/MathComp proof.
   Problem: if f : nat -> nat is positive, strictly increasing on positive arguments,
   multiplicative on coprime arguments, and f 2 = 2, then f n = n for all n > 0.
   Statement: coq/src/putnam_1963_a2.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   The Theorem below is byte-identical to upstream; only the proof script and one
   import line ("From mathcomp Require Import zify.", a tactic library used by the
   proof) were added.
   Produced with Claude Fable 5.1 (Anthropic), September 2026; all checks run by the repository author.
   Verified on Rocq 9.1.0 / MathComp 2.5 (Rocq Platform 2026.07, macOS) and Coq 8.18.0 / MathComp 2.1.0 (Ubuntu 24.04):
   compiles; Print Assumptions putnam_1963_a2 = "Closed under the global context"
   (no axioms); rocqchk / coqchk: "Modules were successfully checked".
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1 / MathComp 2.5 (Rocq Platform 2026.07) the import line
   below triggers ~30 warnings emitted by MathComp itself (all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations). They are library
   warnings, not warnings about this file: none of this file's own lines produce any.
   The import line is kept exactly as upstream wrote it so that the statement stays
   identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope nat_scope.

Theorem putnam_1963_a2
    (f : nat -> nat)
    (hfpos : forall n : nat, 0 < f n)
    (hfinc : forall i j : nat, 0 < i -> i < j -> f i < f j)
    (hf2 : f 2 = 2)
    (hfmn : forall m n : nat, 0 < m -> 0 < n -> coprime m n -> f (m * n) = f m * f n)
    : forall n : nat, 0 < n -> f n = n.
Proof.
(* consecutive values differ by at least 1 *)
have hstep a : 0 < a -> f a + 1 <= f (a + 1).
  by move=> ha; have := hfinc a (a + 1) ha; lia.
have hf1 : f 1 = 1.
  by have := hfinc 1 2 isT isT; have := hfpos 1; lia.
(* slope at least 1: f a + d <= f (a + d) *)
have hslope a d : 0 < a -> f a + d <= f (a + d).
  move=> ha; elim: d => [|d ih]; first by rewrite !addn0.
  have := hstep (a + d).
  have -> : a + d.+1 = a + d + 1 by lia.
  by lia.
have hge n : 0 < n -> n <= f n.
  move=> hn; have := hslope 1 (n - 1) isT.
  have -> : 1 + (n - 1) = n by lia.
  by rewrite hf1; lia.
(* a fixed point b pins down every value below it *)
have hend n b : 0 < n -> n <= b -> f b = b -> f n = n.
  move=> hn hnb hb; have := hslope n (b - n) hn; have := hge n hn.
  have -> : n + (b - n) = b by lia.
  by rewrite hb; lia.
(* the arithmetic heart: f 3 = 3 *)
have hf3 : f 3 = 3.
  have h23 : f 2 < f 3 := hfinc 2 3 isT isT.
  have h15 : f 15 = f 3 * f 5 := hfmn 3 5 isT isT isT.
  have h18 : f 18 = f 2 * f 9 := hfmn 2 9 isT isT isT.
  have h10 : f 10 = f 2 * f 5 := hfmn 2 5 isT isT isT.
  have h1518 : f 15 < f 18 := hfinc 15 18 isT isT.
  have h910 : f 9 < f 10 := hfinc 9 10 isT isT.
  have h5 := hfpos 5.
  by rewrite hf2 in h23 h18 h10; nia.
(* doubling an odd fixed point gives a fixed point *)
have hodd N : 0 < N -> odd N -> f N = N -> f (2 * N) = 2 * N.
  by move=> hN ho hfN; rewrite hfmn ?coprime2n // hf2 hfN.
(* strong induction *)
elim/ltn_ind => n ih hn.
case: (ltnP n 4) => hn4.
  have : n = 1 \/ n = 2 \/ n = 3 by lia.
  by case=> [->|[->|->]].
case ho: (odd n).
- have hN : f (n - 2) = n - 2 by apply: ih; lia.
  have hNo : odd (n - 2) by rewrite oddB ?ho //; lia.
  apply: (hend n (2 * (n - 2))) => //; first by lia.
  by apply: hodd => //; lia.
- have hN : f (n - 1) = n - 1 by apply: ih; lia.
  have hNo : odd (n - 1) by rewrite oddB ?ho //; lia.
  apply: (hend n (2 * (n - 1))) => //; first by lia.
  by apply: hodd => //; lia.
Qed.
