(* ============================================================================
   PutnamBench 1962 A2 -- proof that the UPSTREAM statement is false.
   Loads putnam_1962_a2.vo (the upstream statement compiled as published, apart from
   its marked compat lines; it ends in Admitted) and derives False from it.
   The witness is f0 = the indicator of the single point 0 (f0 0 = 1, f0 x = 0
   otherwise): it is nonnegative and its integral over every [0, x] is 0 because the
   point {0} has Lebesgue measure 0, so its average is 0 = sqrt (f0 0 * f0 x) for all
   x <> 0, i.e. f0 satisfies the benchmark's condition P on (0, 1).  The theorem then
   promises some g = a / (1 - c x)^2 agreeing with f0 on [0, 1); but f0 0 = 1 forces
   a = 1, and 1 / (1 - c x)^2 = 0 forces 1 - c x = 0, impossible at both x = 1/2 and
   x = 1/3.
   Compile with:  rocq compile -R . "" putnam_1962_a2_statement_is_false.v
   (after compiling putnam_1962_a2.v).
   Print Assumptions at the end shows the derivation depends only on the admitted
   theorem putnam_1962_a2 itself, the Variable R declared by the statement, and the
   three classical axioms that mathcomp.reals is built on.
   Produced with Claude Fable 5.1 (Anthropic), September 2026; all checks run by the repository author.
   Verified on Rocq 9.1.0 / MathComp 2.5 / MathComp-Analysis 1.16.0 (Rocq Platform 2026.07, macOS) and Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (Ubuntu 24.04):
   compiles and prints the assumption list described above.
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
From mathcomp Require Import classical_sets numfun set_interval constructive_ereal lra.
(* The benchmark statement putnam_1962_a2.v, compiled as published (it ends in Admitted). *)
Require putnam_1962_a2.
Import putnam_1962_a2.
Local Notation R := putnam_1962_a2.R.

Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* Counterexample: f0 = indicator of the single point 0, i.e. f0 0 = 1 and f0 x = 0 for
   x <> 0.  It is nonnegative and, for every x, its integral over [0, x] is 0 because {0}
   has Lebesgue measure 0; so its average over [0, x] is 0 = sqrt (f0 0 * f0 x) for every
   x <> 0.  Hence f0 satisfies the benchmark's P on (0, 1).  But no a / (1 - c x)^2
   agrees with f0 on [0, 1): f0 0 = 1 forces a = 1, and then 1 / (1 - c x)^2 = 0 forces
   1 - c x = 0, which cannot hold both at x = 1/2 and at x = 1/3. *)

Definition f0 : R -> R := \1_[set 0].

Lemma f0_ge0 x : f0 x >= 0.
Proof. by rewrite /f0 /indic ler0n. Qed.

Lemma f00 : f0 0 = 1.
Proof. by rewrite /f0 /indic mem_set. Qed.

Lemma f0N0 x : x != 0 -> f0 x = 0.
Proof. by move=> x0; rewrite /f0 /indic memNset// => /eqP; rewrite (negbTE x0). Qed.

Lemma measurable_Icc (x : R) : measurable [set t : R | 0 <= t <= x].
Proof. by rewrite -set_itvcc; apply: (@measurable_itv R `[0, x]%R). Qed.

(* the real-valued integral of f0 over [0, x] vanishes *)
Lemma int_f0 (x : R) : \int[mu]_(t in [set t | 0 <= t <= x]) f0 t = 0.
Proof.
rewrite /Rintegral integral_indic; [ | exact: measurable_Icc | exact: measurable_set1].
have mu0 : mu [set 0] = 0%E by exact: lebesgue_measure_set1.
have -> : mu ([set 0] `&` [set t | 0 <= t <= x]) = 0%E.
  apply: (subset_measure0 _ _ _ mu0).
  - exact: measurableI (measurable_set1 _) (measurable_Icc _).
  - exact: measurable_set1.
  - exact: subIsetl.
by [].
Qed.

Lemma putnam_1962_a2_rocq_statement_is_false : False.
Proof.
pose Q := fun (s : set R) (f : R -> R) => (forall x, f x >= 0) /\
  forall x, x \in s -> 1/x * \int[mu]_(t in [set t | 0 <= t <= x]) f t = Num.sqrt (f 0 * f x).
have Q_def : forall s f, Q s f <-> Q s f by [].
have [hall _] := putnam_1962_a2 Q_def.
have [_ hloc] := hall f0.
have Qf0 : Q [set t | 0 < t < 1] f0.
  split; first exact: f0_ge0.
  move=> x /set_mem /= /andP[x0 _].
  by rewrite int_f0 mulr0 f00 mul1r (f0N0 _ (negbT (gt_eqF x0))) sqrtr0.
have [g [/set_mem /= [a [c [_ gE]]] fg]] := hloc 1 ltr01 Qf0.
have h0 : 0 <= (0 : R) < 1 by rewrite lexx ltr01.
have a1 : 1 = a by have := fg 0 h0; rewrite f00 gE /= mulr0 subr0 exp1rz divr1.
have hz (x : R) : 0 < x < 1 -> 1 - c * x = 0.
  case/andP=> x0 x1.
  have hx : 0 <= x < 1 by rewrite (ltW x0) x1.
  have := fg x hx; rewrite (f0N0 _ (negbT (gt_eqF x0))) gE /= -a1 div1r => /esym/eqP.
  by rewrite invr_eq0 expfz_eq0 /= => /eqP.
have h2 : 1 - c * 2^-1 = 0 by apply: hz; apply/andP; split; lra.
have h3 : 1 - c * 3^-1 = 0 by apply: hz; apply/andP; split; lra.
by clear - h2 h3; lra.
Qed.

Print Assumptions putnam_1962_a2_rocq_statement_is_false.
