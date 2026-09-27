(* ============================================================================
   PutnamBench 1962 A6 -- Rocq proof of the CORRECTED statement.
   Problem: a set A of rationals is closed under addition and multiplication, and for
   every rational r exactly one of  r in A,  -r in A,  r = 0  holds; show that A is
   the set of positive rationals.
   Statement: coq/src/putnam_1962_a6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20), with the
   two changes of putnam_1962_a6_corrected.v: in hSScond, "~(A r \/ A (-r))" becomes
   "~(A r /\ A (-r))" (the upstream text makes the hypotheses contradictory, see
   putnam_1962_a6_statement_is_vacuous.v) and every "r = 0" becomes "r == 0" (Qeq;
   Coq's Q has non-canonical fractions, 0#2 <> 0 although 0#2 == 0). The Theorem
   block below is byte-identical to putnam_1962_a6_corrected.v; only the auxiliary
   lemmas and the proof script were added.
   Proof idea, on Coq's concrete fractions n#d (the statement quantifies A over all of
   them, not over rationals up to ==): squares of nonzero fractions are in A, so 1 is;
   adding 1 repeatedly gives every positive integer p#1; if -1#q were in A then
   q#1 * (-1#q) + 1 = 0#q would be, contradicting "~(A r /\ r == 0)", so 1#q is in A;
   hence every p#q with p > 0 is in A, by hSSprod. Fractions with numerator 0 are
   excluded by the same conjunct, and those with negative numerator by
   "~(A r /\ A (-r))". So A and (fun r => r > 0) agree on every fraction, and
   Extensionality_Ensembles turns that into the equality of Ensembles that the
   conclusion asks for.
   Produced with Claude Fable 5.1 (Anthropic), September 2026; all checks run by the repository author.
   Verified on Rocq 9.1.0 (Rocq Platform 2026.07, macOS) and Coq 8.18.0 (Ubuntu 24.04):
   compiles; Print Assumptions putnam_1962_a6 lists exactly one axiom,
   Extensionality_Ensembles, the standard library's own axiom for equality of
   Ensembles (the conclusion is an equality of Ensembles, so no proof can avoid it);
   rocqchk / coqchk: "Modules were successfully checked".
   About the warnings: the file is written for Coq 8.x. Rocq 9.1 warns "Loading Stdlib
   without prefix is deprecated" on the Require line and would prefer
   "From Stdlib Require Import Ensembles QArith"; the line is kept as upstream wrote it.
   None of this file's own lines produce any warning.
   ============================================================================ *)

Require Import Ensembles QArith.

(* ------------------------------------------------------------------ *)
(* Auxiliary lemmas, with the hypotheses of the statement as section    *)
(* hypotheses. Everything is done on Coq's concrete fractions (Qmake),  *)
(* because the statement quantifies A over all of them.                 *)
(* ------------------------------------------------------------------ *)
Section Aux.
Variable A : Ensemble Q.
Hypothesis hadd : forall a b : Q, (A a /\ A b) -> A (a + b).
Hypothesis hprod : forall a b : Q, (A a /\ A b) -> A (a * b).
Hypothesis hcond : forall r : Q, (A r \/ A (-r) \/ r == 0) /\ ~(A r /\ A (-r)) /\ ~(A r /\ r == 0) /\ ~(A (-r) /\ r == 0).

(* a fraction is == 0 exactly when its numerator is 0 *)
Lemma Qeq0_num (n : Z) (d : positive) : (n # d) == 0 <-> n = 0%Z.
Proof.
cbv beta iota delta [Qeq Qnum Qden]; rewrite Z.mul_1_r, Z.mul_0_l.
reflexivity.
Qed.

Lemma A_not0 (r : Q) : A r -> ~ r == 0.
Proof. intros h h0; destruct (hcond r) as [_ [_ [h3 _]]]; exact (h3 (conj h h0)). Qed.

(* a fraction with nonzero numerator: it or its opposite is in A *)
Lemma A_or_opp (n : Z) (d : positive) : n <> 0%Z -> A (n # d) \/ A ((- n) # d).
Proof.
intros hn; destruct (hcond (n # d)) as [[h|[h|h]] _].
- left; exact h.
- right; exact h.
- exfalso; apply hn; exact (proj1 (Qeq0_num n d) h).
Qed.

(* squares of nonzero fractions are in A *)
Lemma A_sq (n : Z) (d : positive) : n <> 0%Z -> A ((n * n) # (d * d)).
Proof.
intros hn; destruct (A_or_opp n d hn) as [h|h].
- exact (hprod _ _ (conj h h)).
- generalize (hprod _ _ (conj h h)).
  cbv beta iota delta [Qmult Qnum Qden]; rewrite Z.mul_opp_opp; exact (fun x => x).
Qed.

Lemma A_one : A 1.
Proof. assert (h : (1 <> 0)%Z) by discriminate; exact (A_sq 1 1 h). Qed.

(* positive integers *)
Lemma A_posint (p : positive) : A (Z.pos p # 1).
Proof.
induction p using Pos.peano_ind.
- exact A_one.
- replace (Z.pos (Pos.succ p) # 1) with ((Z.pos p # 1) + 1).
  + exact (hadd _ _ (conj IHp A_one)).
  + cbv beta iota delta [Qplus Qnum Qden]; f_equal.
    rewrite Pos2Z.inj_succ; unfold Z.succ; ring.
Qed.

(* reciprocals of positive integers: if -1/q were in A, then q * (-1/q) + 1 = 0/q
   would be in A, but it is == 0 *)
Lemma A_inv (q : positive) : A (1 # q).
Proof.
assert (h1 : (1 <> 0)%Z) by discriminate.
destruct (A_or_opp 1 q h1) as [h|h]; [exact h|].
exfalso.
pose proof (hadd _ _ (conj (hprod _ _ (conj (A_posint q) h)) A_one)) as h3.
apply (A_not0 _ h3).
cbv beta iota delta [Qeq Qplus Qmult Qopp Qnum Qden].
repeat rewrite Pos2Z.inj_mul; ring.
Qed.

(* every positive fraction *)
Lemma A_pos (p q : positive) : A (Z.pos p # q).
Proof.
replace (Z.pos p # q) with ((Z.pos p # 1) * (1 # q)).
- exact (hprod _ _ (conj (A_posint p) (A_inv q))).
- cbv beta iota delta [Qmult Qnum Qden]; f_equal; ring.
Qed.

(* the characterisation, fraction by fraction *)
Lemma A_iff (r : Q) : A r <-> 0 < r.
Proof.
destruct r as [n d]; cbv beta iota delta [Qlt Qnum Qden].
destruct n as [|p|p]; split; intro h.
- exfalso; exact (A_not0 _ h (proj2 (Qeq0_num 0 d) eq_refl)).
- exfalso; rewrite Z.mul_0_l, Z.mul_0_l in h; exact (Z.lt_irrefl _ h).
- rewrite Z.mul_0_l, Z.mul_1_r; exact (Pos2Z.is_pos p).
- exact (A_pos p d).
- exfalso; destruct (hcond (Z.neg p # d)) as [_ [h2 _]].
  exact (h2 (conj h (A_pos p d))).
- exfalso; rewrite Z.mul_0_l, Z.mul_1_r in h.
  exact (Z.lt_irrefl _ (Z.lt_trans _ _ _ h (Pos2Z.neg_is_neg p))).
Qed.

End Aux.


Theorem putnam_1962_a6
    (A : Ensemble Q)
    (hSSadd : forall a b : Q, (A a /\ A b) -> A (a + b))
    (hSSprod : forall a b : Q, (A a /\ A b) -> A (a * b))
    (hSScond : forall r : Q, (A r \/ A (-r) \/ r == 0) /\ ~(A r /\ A (-r)) /\ ~(A r /\ r == 0) /\ ~(A (-r) /\ r == 0))
    : A = (fun r : Q => r > 0).
Proof.
apply Extensionality_Ensembles; split; intros r hr; unfold In in *.
- exact (proj1 (A_iff A hSSadd hSSprod hSScond r) hr).
- exact (proj2 (A_iff A hSSadd hSSprod hSScond r) hr).
Qed.

Print Assumptions putnam_1962_a6.
