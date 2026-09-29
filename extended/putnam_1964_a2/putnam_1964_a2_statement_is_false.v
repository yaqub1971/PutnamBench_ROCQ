(* ============================================================================
   PutnamBench 1964 A2 -- proof that the UPSTREAM statement is false.
   Loads putnam_1964_a2.vo (the upstream statement compiled as published, apart from
   its marked compat lines; it ends in Admitted) and derives False from it. The upstream
   set omits the condition int_0^1 f(x) dx = 1, so it contains a positive constant
   function for a suitable alpha: with i1 = int_0^1 x dx and i2 = int_0^1 x^2 dx, the
   constant c = i2 / i1^2 and alpha = c * i1 give int_0^1 x c dx = c * i1 = alpha and
   int_0^1 x^2 c dx = c * i2 = (c * i1)^2 = alpha^2, so (fun _ => c) is in the set the
   theorem declares equal to set0. (By calculus i1 = 1/2 and i2 = 1/3, so this is the
   constant 4/3 with alpha = 2/3; the proof does not need these values.)
   What is proved about i1, i2 is only what the argument needs, without evaluating any
   integral in closed form: x^n is integrable on [0, 1] (continuous on a compact set);
   0 <= int_0^1 x^n dx <= int_0^1 1 dx = mu [0, 1] = 1, so the integrals are finite;
   i2 <= i1 (x^2 <= x on [0, 1]); i2 >= 1/8 by Markov's inequality (le_integral_abse)
   with the level 1/4, whose superlevel set in [0, 1] is [1/2, 1], of measure 1/2;
   hence i1, i2, c > 0. The two moment integrals of the constant c are computed by
   integralZl.
   Compile with:  rocq compile -R . "" putnam_1964_a2_statement_is_false.v
   (after compiling putnam_1964_a2.v; with Coq 8.18 use coqc instead of rocq compile).
   Print Assumptions at the end shows the derivation depends only on the admitted
   theorem putnam_1964_a2 itself, the Variable R declared by the statement, and the
   three classical axioms of mathcomp.classical (boolp.propositional_extensionality,
   boolp.functional_extensionality_dep, boolp.constructive_indefinite_description).
   Verified on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04):
   compiles and prints the assumption list described above. MathComp-Analysis 1.16.0
   dropped one hypothesis of ge0_le_integral (nonnegativity of the larger function) that
   1.0.0 has, so its side conditions are discharged by a "first [...]" that does not
   depend on their number and order.
   About the warnings: the first import line below triggers the MathComp library
   warnings described in putnam_1964_a2.v, and under Rocq 9.1.1 the import line that
   loads realfun triggers one more library warning (incompatible notation prefixes).
   None of this file's own lines produce any warning.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals topology normedtype measure lebesgue_measure lebesgue_integral.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
From mathcomp Require Import classical_sets functions set_interval constructive_ereal realfun lra.
Import numFieldNormedType.Exports.
(* The benchmark statement putnam_1964_a2.v, compiled as published apart from its marked
   compat lines (it ends in Admitted). *)
Require putnam_1964_a2.
Import putnam_1964_a2.
Local Notation R := putnam_1964_a2.R.

Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* [0, 1], written as in the statement, is measurable and compact. *)
Lemma measurable_D01 : measurable [set x : R | 0 <= x <= 1].
Proof. by rewrite -set_itvcc; exact: measurable_itv. Qed.

Lemma compact_D01 : compact [set x : R | 0 <= x <= 1].
Proof. by rewrite -set_itvcc; exact: segment_compact. Qed.

(* Lebesgue measure of a closed interval. *)
Lemma measure_itvcc (a b : R) : a <= b -> mu (`[a, b]%classic : set R) = (b - a)%:E.
Proof.
move=> ab; rewrite (_ : mu _ = lebesgue_measure (`[a, b]%classic : set R))//.
rewrite lebesgue_measure_itv/= lte_fin.
have [_|ba] := ltP a b; first by rewrite -EFinB.
have -> : b = a by apply/eqP; rewrite eq_le ba ab.
by rewrite subrr.
Qed.

(* x^n is integrable on [0, 1] and its integral there is finite (between 0 and 1). *)
Lemma integrable_exprn n :
  mu.-integrable [set x : R | 0 <= x <= 1] (fun x : R => (x ^+ n)%:E).
Proof.
apply: (@continuous_compact_integrable R (fun x : R => x ^+ n)); first exact: compact_D01.
by apply: continuous_subspaceT; exact: exprn_continuous.
Qed.

Lemma integral_exprn_fin n :
  (\int[mu]_(x in [set x : R | (0 <= x <= 1)%R]) ((x ^+ n)%R)%:E)%E \is a fin_num.
Proof.
rewrite ge0_fin_numE; last by apply: integral_ge0 => x /andP[x0 _]; rewrite lee_fin exprn_ge0.
apply: (@le_lt_trans _ _ (\int[mu]_(x in [set x : R | (0 <= x <= 1)%R]) (cst 1%:E x))%E).
  (* the side conditions of ge0_le_integral are discharged whatever their number and order *)
  apply: ge0_le_integral; first [ exact: measurable_D01 | exact: measurable_cst
    | exact: measurable_int (integrable_exprn n)
    | by move=> x /= /andP[x0 x1]; rewrite lee_fin ?exprn_ge0 ?exprn_ile1 ].
rewrite integral_cst; last exact: measurable_D01.
by rewrite -set_itvcc measure_itvcc// subr0 mule1 ltry.
Qed.

(* int_0^1 x^2 dx >= 1/8, by Markov's inequality at the level 1/4. *)
Lemma integral_sqr_ge :
  ((4^-1 * 2^-1)%:E <= \int[mu]_(x in [set x : R | (0 <= x <= 1)%R]) ((x ^+ 2)%R)%:E)%E.
Proof.
have -> : (\int[mu]_(x in [set x : R | (0 <= x <= 1)%R]) ((x ^+ 2)%R)%:E =
           \int[mu]_(x in [set x : R | (0 <= x <= 1)%R]) `|((x ^+ 2)%R)%:E|)%E.
  by apply: eq_integral => x _; rewrite gee0_abs// lee_fin sqr_ge0.
rewrite EFinM.
have <- : mu ([set x : R | 0 <= x <= 1] `&` [set x | ((4^-1)%:E <= `|(x ^+ 2)%:E|)%E])
          = (2^-1)%:E.
  rewrite (_ : _ `&` _ = `[2^-1, 1]%classic); last first.
    apply/seteqP; split => x /=.
      move=> [/andP[x0 x1]]; rewrite ger0_norm ?sqr_ge0// lee_fin in_itv/= => h.
      by apply/andP; split => //; nra.
    rewrite in_itv/= => /andP[hx x1]; split; first by apply/andP; split => //; lra.
    by rewrite ger0_norm ?sqr_ge0// lee_fin; nra.
  by rewrite measure_itvcc; [congr EFin; lra | lra].
apply: le_integral_abse.
- exact: measurable_D01.
- exact: measurable_int (integrable_exprn 2).
- by rewrite invr_gt0.
Qed.

(* Assuming the benchmark's Rocq statement of 1964 A2, False follows: the constant
   c = i2 / i1^2 belongs to its right-hand side for alpha = c * i1, whereas the
   left-hand side is set0. The informal problem (and PutnamBench's Lean statement) also
   requires int_0^1 f(x) dx = 1, which this constant violates. *)
Lemma putnam_1964_a2_rocq_statement_is_false : False.
Proof.
have mD := measurable_D01.
set I1 := (\int[mu]_(x in [set x : R | (0 <= x <= 1)%R]) ((x ^+ 1)%R)%:E)%E.
set I2 := (\int[mu]_(x in [set x : R | (0 <= x <= 1)%R]) ((x ^+ 2)%R)%:E)%E.
have I1E : I1 = (fine I1)%:E by rewrite fineK //; exact: integral_exprn_fin.
have I2E : I2 = (fine I2)%:E by rewrite fineK //; exact: integral_exprn_fin.
set i1 := fine I1; set i2 := fine I2.
have i2ge : 4^-1 * 2^-1 <= i2 by rewrite -lee_fin -I2E; exact: integral_sqr_ge.
have i21 : i2 <= i1.
  (* the side conditions of ge0_le_integral are discharged whatever their number and order *)
  rewrite -lee_fin -I1E -I2E; apply: ge0_le_integral; first [ exact: mD
    | exact: measurable_int (integrable_exprn 2) | exact: measurable_int (integrable_exprn 1)
    | by move=> x /= /andP[x0 x1]; rewrite lee_fin ?exprn_ge0// expr1 expr2 ler_piMl ].
have i2gt0 : 0 < i2 by apply: lt_le_trans i2ge; rewrite mulr_gt0// invr_gt0.
have i1gt0 : 0 < i1 by exact: lt_le_trans i21.
pose c := i2 / i1 ^+ 2.
have cgt0 : 0 < c by rewrite divr_gt0// exprn_gt0.
have ci1 : c * i1 ^+ 2 = i2 by rewrite /c divfK// expf_neq0// gt_eqF.
have e1 : \int[mu]_(x in [set x | 0 <= x <= 1]) (x * c) = c * i1.
  rewrite /Rintegral -[c * i1]/(fine (c * i1)%:E) EFinM -I1E.
  rewrite -(integralZl _ (integrable_exprn 1)); last exact: mD.
  congr fine.
  by apply: eq_integral => x _; rewrite -EFinM expr1 mulrC.
have e2 : \int[mu]_(x in [set x | 0 <= x <= 1]) (x ^+ 2 * c) = c * i2.
  rewrite /Rintegral -[c * i2]/(fine (c * i2)%:E) EFinM -I2E.
  rewrite -(integralZl _ (integrable_exprn 2)); last exact: mD.
  congr fine.
  by apply: eq_integral => x _; rewrite -EFinM mulrC.
have hc : [set f : R -> R |
        (forall x : R, 0 <= x <= 1 -> (f x > 0)
        /\ {within [set x | 0 <= x <= 1], continuous f})
        /\ \int[mu]_(x in [set x | 0 <= x <= 1]) (x * f x) = c * i1
        /\ \int[mu]_(x in [set x | 0 <= x <= 1]) (x ^+ 2 * f x) = (c * i1) ^+ 2]
        (fun _ : R => c).
  split; first by move=> x _; split; [exact: cgt0 | exact: cst_continuous].
  split; first exact: e1.
  by rewrite e2 exprMn -ci1 [c ^+ 2]expr2 mulrA.
by rewrite -(putnam_1964_a2 (c * i1)) in hc.
Qed.

Print Assumptions putnam_1964_a2_rocq_statement_is_false.
