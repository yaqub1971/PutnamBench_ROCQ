(* ============================================================================
   PutnamBench 1964 A6 -- proof that the UPSTREAM statement is false.
   Loads putnam_1964_a6.vo (the upstream statement compiled as published, apart from
   its marked compat lines; it ends in Admitted) and derives False from it. The
   statement does not assume the point set T finite. With T = [set: R] (the whole
   line) its hypothesis hrepdist holds: for any pair p the translate
   (p.1 + 1, p.2 + 1) is a second pair at the same distance. Its conclusion for the
   pairs (0, sqrt 2) and (0, 1) then says sqrt 2 = n / d for some integers n, d with
   d <> 0. Taking absolute values and squaring gives 2 * b^2 = a^2 in nat with
   a = |n|, b = |d| > 0, and the exponent of 2 (logn 2) of the left side is odd while
   that of the right side is even.
   Compile with:  rocq compile -R . "" putnam_1964_a6_statement_is_false.v
   (Coq 8.18: coqc -R . "" ...; after compiling putnam_1964_a6.v).
   Print Assumptions at the end shows the derivation depends only on the admitted
   theorem putnam_1964_a6 itself, the Variable R declared by the statement, and the
   three classical axioms of mathcomp.classical (boolp) that mathcomp.reals is built on.
   Compat lines: the three lines marked "(* compat: ... *)" re-import ssralg after the
   upstream imports, as in putnam_1964_a6.v (with MathComp 2.5, importing all_ssreflect
   after all_algebra overrides the ring notations 1 and %:R). This file's own proof
   uses 1 on R, and on MathComp 2.5 it does not compile without them (checked). They
   change nothing mathematically.
   Verified on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04):
   compiles and prints the assumption list described above.
   About the warnings: on both toolchains the first import line emits library warnings
   (ambiguous coercion paths, overridden notations; on MathComp 2.5 also the
   deprecation of all_ssreflect) that come from MathComp itself; none of this file's
   own lines produce any. The import lines are kept exactly as upstream wrote them.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals topology normedtype.
From mathcomp Require Import classical_sets.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)
(* The benchmark statement putnam_1964_a6.v, compiled as published apart from its marked
   compat lines (it ends in Admitted). *)
Require putnam_1964_a6.
Import putnam_1964_a6.
Local Notation R := putnam_1964_a6.R.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* sqrt 2 is not a ratio of two integers: from sqrt 2 = n / d one gets
   2 * b ^ 2 = a ^ 2 in nat with a = |n| and b = |d| > 0, and the exponent of 2 in the
   left side, 1 + 2 * logn 2 b, is odd while that of the right side, 2 * logn 2 a, is even. *)
Lemma sqrt2_irrational (n d : int) : d <> 0 -> Num.sqrt (2 : R) <> n%:~R / d%:~R.
Proof.
move=> d0 h.
pose a := `|n|%N; pose b := `|d|%N.
have b0 : (0 < b)%N by rewrite /b absz_gt0; apply/eqP.
have hb : b%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
have h1 : Num.sqrt 2 = a%:R / b%:R :> R.
  rewrite -[LHS]ger0_norm ?sqrtr_ge0 // h normrM normfV -!intr_norm -!natr_absz.
  done.
have h2 : 2 * b%:R ^+ 2 = a%:R ^+ 2 :> R.
  by rewrite -{1}(sqr_sqrtr (ler0n R 2)) h1 expr_div_n mulfVK // expf_neq0.
have h3 : (2 * b ^ 2 = a ^ 2)%N.
  by apply/eqP; rewrite -(eqr_nat R) natrM !natrX h2.
have a0 : (0 < a)%N.
  by rewrite -(ltn_exp2r _ _ (ltn0Sn 1)) -h3 muln_gt0 expn_gt0 b0.
have := congr1 (logn 2) h3.
rewrite lognM // ?expn_gt0 ?b0 // !lognX.
have -> : logn 2 2 = 1 by [].
by move/(congr1 odd); rewrite oddD !oddM /=.
Qed.

(* Assuming the benchmark's Rocq statement of 1964 A6, False follows: with T = [set: R]
   the hypothesis hrepdist holds (translate the pair by 1), and the conclusion for the
   pairs (0, sqrt 2) and (0, 1) makes sqrt 2 a ratio of integers. The problem and the
   Lean statement (S : Finset) require the point set to be finite. *)
Lemma putnam_1964_a6_rocq_statement_is_false : False.
Proof.
suff [n [d [d0 hnd]]] : exists n d : int,
    d <> 0 /\ (Num.sqrt 2 - 0) / (1 - 0) = n%:~R / d%:~R :> R.
  apply: (sqrt2_irrational d0); move: hnd; rewrite !subr0 divr1; exact: id.
have H := putnam_1964_a6 (T := [set: R]); cbv zeta beta in H.
apply: (H _ (0, Num.sqrt 2) (0, 1)).
- move=> p; rewrite inE /= => -[_ [_ hp]] _.
  exists (p.1 + 1, p.2 + 1); split; [|split].
  + by rewrite inE /=; split; [exact: in_setT | split; [exact: in_setT | rewrite ltrD2r]].
  + by move/(congr1 fst) => /= /eqP; rewrite -subr_eq0 addrAC subrr add0r oner_eq0.
  + by rewrite /= opprD addrACA subrr addr0.
- rewrite !inE /=; split; [|split].
  + by split; [exact: in_setT | split; [exact: in_setT | rewrite sqrtr_gt0 ltr0n]].
  + by split; [exact: in_setT | split; [exact: in_setT | rewrite ltr01]].
  + move=> [] h.
    have := sqr_sqrtr (ler0n R 2); rewrite -h expr1n => /eqP.
    by rewrite (eqr_nat R 1 2).
Qed.

Print Assumptions putnam_1964_a6_rocq_statement_is_false.
