(* ============================================================================
   PutnamBench 1962 B6 -- Rocq proof (standard-library reals, Coquelicot, MathComp).
   Problem: let f(x) = sum_{k=0}^{n} (a_k sin kx + b_k cos kx) with real coefficients.
   If |f(x)| <= 1 for all x and |f(x)| = 1 at 2n distinct points of [0, 2 pi), then
   either f is constant or f(x) = cos(nx + a) for some real a.
   Statement: coq/src/putnam_1962_b6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   The upstream file is reproduced verbatim: its first three lines (the Require Import
   line and the coercion) and the Theorem below are byte-identical to upstream, and no
   compat line was needed (the upstream file compiles unchanged on the current
   toolchain). Between the coercion and the Theorem this file adds the proof's extra
   imports and the auxiliary definitions and lemmas it needs (Parts A-E); nothing in
   them redefines a name used by the statement. ci/verify.sh checks the textual
   identity of the preamble and of the Theorem block, and, in addition, compiles the
   upstream file itself and lets the kernel check that the theorem proved here has
   exactly the type of the upstream (admitted) theorem.
   Proof idea (no multiplicity argument, only zero counting):
   (1) f is 2 pi-periodic; |f| <= 1 on [0, 2 pi] and |f(x_i)| = 1 at the 2n points make
       each x_i an extremum, so f'(x_i) = 0 (Fermat, Part A).
   (2) Counting lemma (Part C): a trigonometric sum of degree m that vanishes at 2m+1
       distinct points of [0, 2 pi) has all its coefficients zero. Proof: the complex
       polynomial P(z) = sum_k ((b_k - i a_k)/2 z^(m+k) + (b_k + i a_k)/2 z^(m-k)) has
       degree <= 2m and satisfies P(e^(ix)) = e^(imx) f(x); the points e^(ix_j) are
       distinct roots, so P = 0 (MathComp's max_poly_roots, over Coquelicot's complex
       numbers made a MathComp field in Part B), and the coefficients of P are read off.
   (3) f is not constant, so some harmonic is present, f' is not identically zero, and by
       (2) f' has at most 2n zeros in [0, 2 pi): one of the 2n+1 points j pi/(2n+1) is a
       point y with f'(y) <> 0, hence |f(y)| < 1. Put K = f'(y)^2 / (1 - f(y)^2) and
       S = f'^2 - K (1 - f^2). S vanishes at y and at the 2n points x_i. Rolle's theorem
       between consecutive zeros (Part D) and once more across the gap from the last
       zero to the first zero + 2 pi (periodicity) gives 2n+1 distinct zeros of
       S' = 2 f' (f'' + K f) in [0, 2 pi), none of them a zero of f' (f' cannot vanish at
       2n+1 points), so f'' + K f vanishes at 2n+1 points and, by (2), (K - k^2) a_k =
       (K - k^2) b_k = 0 for 1 <= k <= n and K b_0 = 0.
   (4) With a harmonic j present, K = j^2, every other harmonic vanishes, and j = n
       (otherwise f' would have degree j < n and 2n >= 2j+1 zeros). At any of the 2n
       points, f = +-1 and f' = 0 give a_n^2 + b_n^2 = 1; an angle a with
       (cos a, sin a) = (b_n, -a_n) exists (intermediate value theorem), and then
       f(x) = a_n sin nx + b_n cos nx = cos(nx + a).
   Produced with Claude Fable 5.1 (Anthropic), September 2026; all checks run by the repository author.
   Verified on Rocq 9.1.0 / MathComp 2.5 / Coquelicot 3.4.4 (Rocq Platform 2026.07, macOS):
   compiles; Print Assumptions putnam_1962_b6 lists only the axioms the standard
   library's real numbers are built on (ClassicalDedekindReals.sig_not_dec,
   ClassicalDedekindReals.sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep),
   Classical_Prop.classic (used by the standard library's Rolle), and the three
   classical axioms of mathcomp.classical (boolp.propositional_extensionality,
   boolp.functional_extensionality_dep, boolp.constructive_indefinite_description, needed
   to make the complex numbers a MathComp choice type) -- no axiom of this file's own;
   rocqchk: "Modules were successfully checked".
   About the warnings: the upstream import line (line 1 below, kept exactly as upstream
   wrote it) triggers Rocq's "Loading Stdlib without prefix is deprecated" warnings, and
   the MathComp import line triggers warnings emitted by MathComp itself (ambiguous
   coercion paths, overridden notations). None of this file's own lines produces a
   warning: the three instance declarations of Part B carry the attribute
   #[warnings="-redundant-canonical-projection"], because in MathComp 2.5 the Z-module
   and ring factories are visible under two module paths (Algebra and its alias GRing),
   so Hierarchy Builders registers the resulting mixin instances twice and Rocq reports
   the second registration as a redundant canonical projection (an informational
   message: the duplicate is ignored); the attribute silences exactly that message on
   those three lines and nothing else.
   ============================================================================ *)

Require Import Reals Ensembles Coquelicot.Hierarchy Finite_sets.

Local Coercion INR : nat >-> R.

(* Extra imports for the proof (they add nothing to the statement). *)
From Stdlib Require Import Lra Lia Constructive_sets Sorted.
From Coquelicot Require Import Rcomplements Derive ElemFct Complex.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop ssralg poly.
From mathcomp Require Import boolp zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope R_scope with coqR.

(* ------------------------------------------------------------------ *)
(* Part A: real analysis of trigonometric sums.                        *)
(* ------------------------------------------------------------------ *)
Section TrigSums.

(* the trigonometric sum of the statement, with its coefficient sequences *)
Definition tp (a b : nat -> R) (m : nat) (x : R) : R :=
  sum_n (fun k : nat => a k * sin (k * x) + b k * cos (k * x)) m.

(* the coefficient sequences of its derivative *)
Definition da (a b : nat -> R) (k : nat) : R := - k * b k.
Definition db (a b : nat -> R) (k : nat) : R := k * a k.

Lemma tp_derive a b m x : is_derive (tp a b m) x (tp (da a b) (db a b) m x).
Proof.
rewrite /tp; apply: is_derive_sum_n => k _.
have -> : da a b k * sin (k * x) + db a b k * cos (k * x)
        = a k * (k * cos (k * x)) + b k * (k * - sin (k * x)).
  by rewrite /da /db; ring.
apply: is_derive_plus; apply: is_derive_scal.
- apply: (is_derive_comp sin (fun y => k * y)); first exact: is_derive_sin.
  by have := is_derive_scal (fun y => y) x k 1 (is_derive_id x); rewrite Rmult_1_r.
- apply: (is_derive_comp cos (fun y => k * y)); first exact: is_derive_cos.
  by have := is_derive_scal (fun y => y) x k 1 (is_derive_id x); rewrite Rmult_1_r.
Qed.

Lemma tp_derivable a b m x : derivable_pt (tp a b m) x.
Proof. by exists (tp (da a b) (db a b) m x); apply/is_derive_Reals; exact: tp_derive. Qed.

Lemma tp_derive_pt a b m x (pr : derivable_pt (tp a b m) x) :
  derive_pt (tp a b m) x pr = tp (da a b) (db a b) m x.
Proof. by apply: derive_pt_eq_0; apply/is_derive_Reals; exact: tp_derive. Qed.

(* periodicity *)
Lemma tp_period a b m x : tp a b m (x + 2 * PI) = tp a b m x.
Proof.
rewrite /tp; apply: sum_n_ext => k.
have -> : k * (x + 2 * PI) = k * x + 2 * INR k * PI by ring.
by rewrite sin_period cos_period.
Qed.

(* the value at a point where a bounded sum reaches its bound is an extremum,
   so the derivative vanishes there; the bound is only assumed on [0, 2 pi] *)
Lemma tp_extremum a b m x0 :
  (forall x, 0 <= x <= 2 * PI -> Rabs (tp a b m x) <= 1) ->
  0 <= x0 < 2 * PI -> Rabs (tp a b m x0) = 1 ->
  tp (da a b) (db a b) m x0 = 0.
Proof.
move=> bnd [x0_ge0 x0_lt] fx0; have pi0 := PI_RGT_0.
have bnd' x : - (2 * PI) < x < 2 * PI -> Rabs (tp a b m x) <= 1.
  move=> [xl xu]; case: (Rle_dec 0 x) => [xge0|/Rnot_le_lt xneg].
    by apply: bnd; split; [exact: xge0 | exact: Rlt_le].
  by rewrite -(tp_period a b m x); apply: bnd; lra.
have x0l : - (2 * PI) < x0 by lra.
have pr := tp_derivable a b m x0.
rewrite -(tp_derive_pt pr).
have [fx0_1 | fx0_m1] : tp a b m x0 = 1 \/ tp a b m x0 = -1.
  by move: fx0; rewrite /Rabs; case: Rcase_abs => _ H; [right | left]; lra.
- apply: (@deriv_maximum (tp a b m) (- (2 * PI)) (2 * PI) x0 pr x0l x0_lt) => x xl xu.
  by have := bnd' x (conj xl xu); rewrite fx0_1 => /Rabs_le_between; lra.
- apply: (@deriv_minimum (tp a b m) (- (2 * PI)) (2 * PI) x0 pr x0l x0_lt) => x xl xu.
  by have := bnd' x (conj xl xu); rewrite fx0_m1 => /Rabs_le_between; lra.
Qed.

(* a sum whose terms vanish except the j-th *)
Lemma sum_n_single (g : nat -> R) (m j : nat) : (j <= m)%nat ->
  (forall k, (k <= m)%nat -> k <> j -> g k = 0) -> sum_n g m = g j.
Proof.
elim: m => [|m IH] jm g0.
  by rewrite sum_O; have -> : j = 0%nat by lia.
rewrite sum_Sn /plus/=; case: (Nat.eq_dec j (S m)) => [jSm | jSm].
  rewrite jSm in g0 *.
  have -> : sum_n g m = sum_n (fun _ => 0) m by apply: sum_n_ext_loc => k km; apply: g0; lia.
  suff -> : sum_n (fun _ : nat => 0) m = 0 by rewrite Rplus_0_l.
  by elim: m {IH jm g0 jSm} => [|m IH]; [rewrite sum_O | rewrite sum_Sn IH /plus/= Rplus_0_l].
rewrite (g0 (S m)) ?Rplus_0_r//; last by lia.
by apply: IH => [|k km kj]; [lia | apply: g0 => //; lia].
Qed.

(* a trigonometric sum whose coefficients vanish except at index j *)
Lemma tp_single a b m j : (1 <= j <= m)%nat -> b 0%nat = 0 ->
  (forall k, (1 <= k <= m)%nat -> k <> j -> a k = 0 /\ b k = 0) ->
  forall x, tp a b m x = a j * sin (j * x) + b j * cos (j * x).
Proof.
move=> jm b0 ab0 x; rewrite /tp (sum_n_single (j := j)) //; first by lia.
move=> k km kj; case: (Nat.eq_dec k 0) => [->|k0].
  by rewrite b0 !Rmult_0_l sin_0 Rmult_0_r; ring.
by have [-> ->] := ab0 k (ltac:(lia) : (1 <= k <= m)%nat) kj; ring.
Qed.

(* a trigonometric sum with no harmonic is constant *)
Lemma tp_const a b m : (forall k, (1 <= k <= m)%nat -> a k = 0 /\ b k = 0) ->
  forall x, tp a b m x = b 0%nat.
Proof.
move=> ab0 x; rewrite /tp (sum_n_single (j := 0%nat)).
- by rewrite !Rmult_0_l sin_0 cos_0; ring.
- by lia.
- by move=> k km k0; have [-> ->] := ab0 k (ltac:(lia) : (1 <= k <= m)%nat); ring.
Qed.

(* every point of the unit circle is (cos phi, sin phi) *)
Lemma angle_exists (c s : R) : c * c + s * s = 1 -> exists phi, cos phi = c /\ sin phi = s.
Proof.
move=> cs; have pi0 := PI_RGT_0.
have cont : continuity (fun t => cos t - c).
  by apply: continuity_minus; [exact: continuity_cos | exact: continuity_const].
have prod : (cos 0 - c) * (cos PI - c) <= 0 by rewrite cos_0 cos_PI; nra.
have [phi0 [[phi0_ge0 phi0_le] cphi0]] := IVT_cor (fun t => cos t - c) 0 PI cont (Rlt_le _ _ pi0) prod.
have cphi0' : cos phi0 = c by lra.
have sphi0 : Rsqr (sin phi0) = Rsqr s.
  by have := sin2_cos2 phi0; rewrite cphi0' /Rsqr; nra.
case: (Rsqr_eq _ _ sphi0) => sphi.
- by exists phi0.
- by exists (- phi0); rewrite cos_neg sin_neg sphi; split => //; ring.
Qed.

End TrigSums.

(* ------------------------------------------------------------------ *)
(* Part B: the reals as an eqType, and Coquelicot's complex numbers    *)
(* as a MathComp field, so that MathComp's polynomials over them can   *)
(* be used (a polynomial has no more roots than its degree).           *)
(* ------------------------------------------------------------------ *)
Definition eqR (x y : R) : bool := if Req_EM_T x y is left _ then true else false.
Lemma eqRP : Equality.axiom eqR.
Proof. by move=> x y; rewrite /eqR; case: Req_EM_T => H; apply: (iffP idP). Qed.
HB.instance Definition _ := hasDecEq.Build R eqRP.

Definition Cx : Type := C.
Local Open Scope ring_scope.

Definition eqC (z w : Cx) : bool := if Ceq_dec z w is left _ then true else false.
Lemma eqCP : Equality.axiom eqC.
Proof. by move=> z w; rewrite /eqC; case: Ceq_dec => H; apply: (iffP idP). Qed.
HB.instance Definition _ := hasDecEq.Build Cx eqCP.
HB.instance Definition _ := gen_choiceMixin Cx.

Fact CplusA : associative Cplus. Proof. by move=> *; rewrite Cplus_assoc. Qed.
Fact Cplus0l : left_id (RtoC 0) Cplus. Proof. exact: Cplus_0_l. Qed.
Fact CplusNl : left_inverse (RtoC 0) Copp Cplus.
Proof. by move=> z; rewrite Cplus_comm Cplus_opp_r. Qed.
#[warnings="-redundant-canonical-projection"] HB.instance Definition _ := GRing.isZmodule.Build Cx CplusA Cplus_comm Cplus0l CplusNl.

Fact CmultA : associative Cmult. Proof. by move=> *; rewrite Cmult_assoc. Qed.
Fact Cmult1l : left_id (RtoC 1) Cmult. Proof. exact: Cmult_1_l. Qed.
Fact Cmult1r : right_id (RtoC 1) Cmult. Proof. exact: Cmult_1_r. Qed.
Fact CmultDl : left_distributive Cmult Cplus. Proof. by move=> *; rewrite Cmult_plus_distr_r. Qed.
Fact CmultDr : right_distributive Cmult Cplus. Proof. by move=> *; rewrite Cmult_plus_distr_l. Qed.
Fact C1_neq_0 : (RtoC 1 : Cx) != RtoC 0. Proof. by apply/eqP; exact: C1_nz. Qed.
#[warnings="-redundant-canonical-projection"] HB.instance Definition _ := GRing.Zmodule_isNzRing.Build Cx CmultA Cmult1l Cmult1r CmultDl CmultDr C1_neq_0.
#[warnings="-redundant-canonical-projection"] HB.instance Definition _ := GRing.PzRing_hasCommutativeMul.Build Cx Cmult_comm.

Definition unit_C (z : Cx) := z != RtoC 0.
Fact CmultVl : {in unit_C, left_inverse (RtoC 1) Cinv Cmult}.
Proof. by move=> z; rewrite -topredE /unit_C => /eqP z0; exact: Cinv_l. Qed.
Fact CmultVr : {in unit_C, right_inverse (RtoC 1) Cinv Cmult}.
Proof. by move=> z; rewrite -topredE /unit_C => /eqP z0; exact: Cinv_r. Qed.
Fact unit_CP (z w : Cx) : w * z = 1 /\ z * w = 1 -> unit_C z.
Proof.
move=> [wz _]; apply: contra_eqN wz => /eqP ->.
by rewrite /GRing.mul/= Cmult_0_r eq_sym C1_neq_0.
Qed.
Fact Cinv_out : {in predC unit_C, Cinv =1 id}.
Proof.
move=> z; rewrite inE /unit_C negbK => /eqP ->; rewrite /Cinv /=.
by congr (_, _); rewrite ?Ropp_0 /Rdiv Rmult_0_l.
Qed.
HB.instance Definition _ := GRing.NzRing_hasMulInverse.Build Cx CmultVl CmultVr unit_CP Cinv_out.
Fact C_idomain (z w : Cx) : z * w = 0 -> (z == 0) || (w == 0).
Proof.
move=> zw; apply/orP; case: (z =P 0) => [_|z0]; first by left.
case: (w =P 0) => [_|w0]; first by right.
by have := Cmult_neq_0 z w z0 w0; rewrite -[Cmult z w]/(z * w) zw.
Qed.
HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build Cx C_idomain.
Fact C_field : GRing.field_axiom Cx. Proof. by []. Qed.
HB.instance Definition _ := GRing.UnitRing_isField.Build Cx C_field.
Local Close Scope ring_scope.

(* ------------------------------------------------------------------ *)
(* Part C: a trigonometric sum of degree m as a complex polynomial of  *)
(* degree 2m evaluated on the unit circle.                             *)
(* ------------------------------------------------------------------ *)
(* the point e^(ix) of the unit circle, and the real number r as a complex number *)
Definition e (x : R) : Cx := (cos x, sin x).
Definition RC (r : R) : Cx := (r, 0).

(* injectivity of e on [0, 2 pi) *)
Lemma e_inj (x y : R) : 0 <= x < 2 * PI -> 0 <= y < 2 * PI -> e x = e y -> x = y.
Proof.
wlog yx : x y / y <= x.
  move=> H xr yr exy; case: (Rle_dec y x) => [yx|/Rnot_le_lt/Rlt_le xy]; first exact: H.
  by apply/esym; apply: H.
move=> [x0 x2] [y0 y2] [cxy sxy].
have st : sin (x - y) = 0 by rewrite sin_minus cxy sxy; ring.
have ct : cos (x - y) = 1 by rewrite cos_minus cxy sxy; have := sin2_cos2 y; rewrite /Rsqr; lra.
have t0 : 0 <= x - y by lra.
have t2 : x - y <= 2 * PI by lra.
have [tz|[tpi|t2pi]] := sin_eq_O_2PI_0 (x - y) t0 t2 st.
- by lra.
- by move: ct; rewrite tpi cos_PI; lra.
- by lra.
Qed.

Section TrigPoly.
Local Open Scope ring_scope.
Import GRing.Theory.

(* the ring operations of Cx, componentwise *)
Lemma CmulE (z w : Cx) : z * w = ((fst z * fst w - snd z * snd w)%coqR, (fst z * snd w + snd z * fst w)%coqR).
Proof. by []. Qed.
Lemma CaddE (z w : Cx) : z + w = ((fst z + fst w)%coqR, (snd z + snd w)%coqR).
Proof. by []. Qed.
Lemma C1E : (1 : Cx) = (1%coqR, 0%coqR). Proof. by []. Qed.
Lemma C0E : (0 : Cx) = (0%coqR, 0%coqR). Proof. by []. Qed.

Lemma RC_add (r s : R) : RC (r + s)%coqR = RC r + RC s.
Proof. by rewrite CaddE /RC /= Rplus_0_r. Qed.

(* de Moivre *)
Lemma e_pow (x : R) (k : nat) : e x ^+ k = (cos (k * x), sin (k * x)).
Proof.
elim: k => [|k IH]; first by rewrite expr0 C1E !Rmult_0_l cos_0 sin_0.
rewrite exprS IH S_INR CmulE /e /=.
have -> : ((k + 1) * x = x + k * x)%coqR by ring.
by rewrite cos_plus sin_plus; congr (_, _); ring.
Qed.

Lemma e_neg_pow (x : R) (k : nat) : e (- x) ^+ k = (cos (k * x), (- sin (k * x))%coqR).
Proof. by rewrite e_pow -Ropp_mult_distr_r cos_neg sin_neg. Qed.

Lemma e_mul_neg (x : R) : e x * e (- x) = 1.
Proof.
rewrite CmulE /e /= cos_neg sin_neg C1E; congr (_, _); last by ring.
by have := sin2_cos2 x; rewrite /Rsqr; lra.
Qed.

(* e x ^ (m - k) = e x ^ m * e (- x) ^ k for k <= m *)
Lemma e_pow_sub (x : R) (m k : nat) : (k <= m)%N -> e x ^+ (m - k) = e x ^+ m * e (- x) ^+ k.
Proof.
by move=> km; rewrite -[in RHS](subnK km) exprD -mulrA -exprMn e_mul_neg expr1n mulr1.
Qed.

(* the complex polynomial attached to the coefficient sequences (al, be) and
   the degree m: P(z) = sum_k (cm k z^(m+k) + cp k z^(m-k)); on the unit
   circle it satisfies P(e^(ix)) = e^(imx) * tp al be m x *)
Definition cm (al be : nat -> R) (k : nat) : Cx := ((be k / 2)%coqR, (- (al k / 2))%coqR).
Definition cp (al be : nat -> R) (k : nat) : Cx := ((be k / 2)%coqR, (al k / 2)%coqR).
Definition Pc (al be : nat -> R) (m : nat) : {poly Cx} :=
  \sum_(k < m.+1) (cm al be k *: 'X^(m + k) + cp al be k *: 'X^(m - k)).

Lemma RC_sum_n (g : nat -> R) (m : nat) : RC (sum_n g m) = \sum_(k < m.+1) RC (g k).
Proof.
elim: m => [|m IH]; first by rewrite sum_O big_ord_recl big_ord0 addr0.
by rewrite sum_Sn big_ord_recr /= -IH RC_add.
Qed.

Lemma Pc_eval (al be : nat -> R) (m : nat) (x : R) :
  (Pc al be m).[e x] = e x ^+ m * RC (tp al be m x).
Proof.
rewrite /Pc horner_sum /tp RC_sum_n mulr_sumr; apply: eq_bigr => k _.
have km : (k <= m)%N by rewrite -ltnS.
rewrite hornerD !hornerZ !hornerXn exprD (e_pow_sub _ km).
rewrite !mulrA ![_ * e x ^+ m]mulrC -!mulrA -mulrDr; congr (_ * _).
rewrite e_neg_pow e_pow !CmulE CaddE /cm /cp /RC /=.
by congr (_, _); field.
Qed.

Lemma Pc_size (al be : nat -> R) (m : nat) : (size (Pc al be m) <= (2 * m).+1)%N.
Proof.
apply: (leq_trans (size_sum _ _ _)); apply/bigmax_leqP => k _; have kk := ltn_ord k.
apply: (leq_trans (size_polyD _ _)); rewrite geq_max; apply/andP; split.
- by apply: (leq_trans (size_scale_leq _ _)); rewrite size_polyXn ltnS; lia.
- by apply: (leq_trans (size_scale_leq _ _)); rewrite size_polyXn ltnS; lia.
Qed.

(* the coefficients of X^(m+k), k >= 1, and of X^m *)
Lemma Pc_coef_hi (al be : nat -> R) (m k : nat) : (1 <= k <= m)%N ->
  (Pc al be m)`_(m + k) = cm al be k.
Proof.
move=> /andP[k1 km]; rewrite /Pc coef_sum.
have kord : (k < m.+1)%N by lia.
rewrite (bigD1 (Ordinal kord)) //= big1 ?addr0 => [|i ik].
- rewrite coefD !coefZ !coefXn eqxx mulr1.
  have -> : (m + k == m - k)%N = false by apply/negbTE/negP => /eqP; lia.
  by rewrite mulr0 addr0.
- rewrite coefD !coefZ !coefXn; move: ik; rewrite -val_eqE /= => ik; have ii := ltn_ord i.
  have -> : (m + k == m + i)%N = false by rewrite eqn_add2l eq_sym; exact: negbTE.
  have -> : (m + k == m - i)%N = false by apply/negbTE/negP => /eqP; lia.
  by rewrite !mulr0 addr0.
Qed.

Lemma Pc_coef_m (al be : nat -> R) (m : nat) : (Pc al be m)`_m = RC (be 0%N).
Proof.
rewrite /Pc coef_sum (bigD1 ord0) //= big1 ?addr0 => [|i i0].
- rewrite coefD !coefZ !coefXn addn0 subn0 eqxx !mulr1 CaddE /cm /cp /RC /=.
  by congr (_, _); field.
- rewrite coefD !coefZ !coefXn; move: i0; rewrite -val_eqE /= => i0; have ii := ltn_ord i.
  have -> : (m == m + i)%N = false by apply/negbTE/negP => /eqP; lia.
  have -> : (m == m - i)%N = false by apply/negbTE/negP => /eqP; lia.
  by rewrite !mulr0 addr0.
Qed.

(* the zero-counting lemma: a trigonometric sum of degree m that vanishes at
   2m+1 distinct points of [0, 2 pi) has all its coefficients zero (except the
   irrelevant al 0, the coefficient of sin 0) *)
Lemma tp_zeros (al be : nat -> R) (m : nat) (l : seq R) :
  uniq l -> (forall x, x \in l -> (0 <= x < 2 * PI)%coqR) ->
  (forall x, x \in l -> tp al be m x = 0%coqR) -> ((2 * m).+1 <= size l)%N ->
  be 0%N = 0%coqR /\ forall k, (1 <= k <= m)%N -> al k = 0%coqR /\ be k = 0%coqR.
Proof.
move=> ul lr l0 lsize.
have P0 : Pc al be m = 0.
  apply/eqP; apply: contraLR lsize => Pn0; rewrite -ltnNge.
  have roots : all (root (Pc al be m)) (map e l).
    apply/allP => _ /mapP[x xl ->]; rewrite /root Pc_eval l0 //.
    by rewrite (_ : RC 0%coqR = 0) ?mulr0.
  have uel : uniq (map e l).
    by rewrite map_inj_in_uniq // => x y xl yl; apply: e_inj; [exact: lr | exact: lr].
  have := max_poly_roots Pn0 roots uel; rewrite size_map => /leq_trans; apply.
  exact: Pc_size.
split.
  by have := Pc_coef_m al be m; rewrite P0 coef0 C0E /RC => -[].
move=> k k1m; have := Pc_coef_hi al be k1m; rewrite P0 coef0 C0E /cm => -[b0 a0].
by split; lra.
Qed.

End TrigPoly.

(* ------------------------------------------------------------------ *)
(* Part D: finite sets of reals as sorted lists, and Rolle's theorem    *)
(* applied between consecutive zeros.                                  *)
(* ------------------------------------------------------------------ *)
Section Lists.

Import List.

(* a finite Ensemble of cardinality m is the range of a duplicate-free list *)
Lemma cardinal_list (X : Ensemble R) m : cardinal R X m ->
  exists l : list R, NoDup l /\ length l = m /\ forall x, In x l <-> X x.
Proof.
elim => [|Y p _ [l [ndl [lenl memY]]] x0 x0Y].
  exists nil; split; first exact: NoDup_nil.
  by split => // x; split => // /Noone_in_empty.
exists (x0 :: l); split; [|split].
- by apply: NoDup_cons => // /memY.
- by rewrite /= lenl.
- move=> x; split.
  + by move=> [->|/memY xY]; [exact: Constructive_sets.Add_intro2 | exact: Constructive_sets.Add_intro1].
  + by move=> xAdd; case: (@Constructive_sets.Add_inv R Y x0 x xAdd) => [/memY xl|<-]; [right | left].
Qed.

(* insertion sort, keeping strict sortedness of a duplicate-free list *)
Fixpoint insR (x : R) (l : list R) : list R :=
  match l with
  | nil => x :: nil
  | y :: l' => if Rlt_dec x y then x :: y :: l' else y :: insR x l'
  end.

Lemma insR_in x l z : In z (insR x l) <-> x = z \/ In z l.
Proof.
elim: l => [|y l IH] /=; first by tauto.
case: Rlt_dec => _ /=; first by tauto.
by rewrite IH; tauto.
Qed.

Lemma insR_length x l : length (insR x l) = S (length l).
Proof. by elim: l => [|y l IH] //=; case: Rlt_dec => _ //=; rewrite IH. Qed.

Lemma insR_sorted x l : StronglySorted Rlt l -> ~ In x l -> StronglySorted Rlt (insR x l).
Proof.
elim: l => [|y l IH] sl xl /=; first by apply: SSorted_cons => //; exact: SSorted_nil.
have {sl} [sl fy] := StronglySorted_inv sl; case: Rlt_dec => [xy|nxy].
  apply: SSorted_cons; first exact: SSorted_cons.
  apply/Forall_cons => //; move: fy; rewrite !Forall_forall => fy z zl.
  exact: Rlt_trans (fy z zl).
have yx : y <= x by exact: Rnot_lt_le.
have xy : y < x by case: (Rle_lt_or_eq_dec _ _ yx) => // yx'; exfalso; apply: xl; left.
apply: SSorted_cons; first by apply: IH => // xl'; apply: xl; right.
apply/Forall_forall => z /insR_in [<-|zl] //.
by move: fy; rewrite Forall_forall => fy; exact: fy.
Qed.

Fixpoint sortR (l : list R) : list R :=
  match l with nil => nil | x :: l' => insR x (sortR l') end.

Lemma sortR_in l z : In z (sortR l) <-> In z l.
Proof. by elim: l => [|x l IH] //=; rewrite insR_in IH. Qed.

Lemma sortR_length l : length (sortR l) = length l.
Proof. by elim: l => [|x l IH] //=; rewrite insR_length IH. Qed.

Lemma sortR_sorted l : NoDup l -> StronglySorted Rlt (sortR l).
Proof.
elim: l => [|x l IH] /=; first by move=> _; exact: SSorted_nil.
by move=> /NoDup_cons_iff [xl ndl]; apply: insR_sorted; [exact: IH | rewrite sortR_in].
Qed.

(* the last element of a nonempty strictly increasing list is at least its head *)
Lemma last_in (l : list R) (d : R) : l <> nil -> In (last l d) l.
Proof. by elim: l d => [|x l IH] d //= _; case: l IH => [|y l] IH; [left | right; exact: IH]. Qed.

Lemma last_cons_eq (a d : R) (l : list R) : last (a :: l) d = last l a.
Proof. by elim: l a d => [|x l IH] a d //=; case: l IH => [|y l] IH //; exact: IH. Qed.

Lemma sorted_head_last u0 u' : StronglySorted Rlt (u0 :: u') -> u0 <= last u' u0.
Proof.
case: u' => [|u1 u'] su; first exact: Rle_refl.
have [_ fu] := StronglySorted_inv su; move: fu; rewrite Forall_forall => fu.
by apply: Rlt_le; apply: fu; exact: last_in.
Qed.

(* the last element of a strictly increasing list is its maximum *)
Lemma sorted_le_last u0 u' : StronglySorted Rlt (u0 :: u') ->
  forall x, In x (u0 :: u') -> x <= last u' u0.
Proof.
elim: u' u0 => [|u1 u' IH] u0 su x; first by move=> [<-|//]; exact: Rle_refl.
have [su1 fu0] := StronglySorted_inv su; move: fu0; rewrite Forall_forall => fu0.
rewrite last_cons_eq; move=> [<-|xu]; last exact: IH.
by apply: Rle_trans (IH u1 su1 u1 (or_introl erefl)); apply: Rlt_le; apply: fu0; left.
Qed.

(* a strictly increasing list has no duplicates *)
Lemma sorted_NoDup (w : list R) : StronglySorted Rlt w -> NoDup w.
Proof.
elim: w => [|z w IH] sw; first exact: NoDup_nil.
have [sw' fz] := StronglySorted_inv sw; move: fz; rewrite Forall_forall => fz.
by apply: NoDup_cons; [move=> /fz; exact: Rlt_irrefl | exact: IH].
Qed.

(* Rolle's theorem between consecutive elements of a strictly increasing list
   of zeros of S: one zero of S' in each open gap, hence one fewer than the
   number of points; the new points are pairwise distinct, lie strictly
   between the first and the last point, and are not in the list *)
Lemma rolle_list (S S' : R -> R) (dS : forall x, is_derive S x (S' x)) (u0 : R) (u' : list R) :
  StronglySorted Rlt (u0 :: u') -> (forall x, In x (u0 :: u') -> S x = 0) ->
  exists w : list R, StronglySorted Rlt w /\ length w = length u' /\
    forall z, In z w -> S' z = 0 /\ ~ In z (u0 :: u') /\ u0 < z < last u' u0.
Proof.
elim: u' u0 => [|u1 u' IH] u0 su Su.
  by exists nil; split; [exact: SSorted_nil | split].
have [su1 fu0] := StronglySorted_inv su.
have u01 : u0 < u1 by move: fu0; rewrite Forall_forall; apply; left.
have [w [sw [lenw wP]]] := IH u1 su1 (fun x xu => Su x (or_intror xu)).
(* Rolle on [u0, u1] *)
have pr x : u0 < x < u1 -> derivable_pt S x.
  by move=> _; exists (S' x); apply/is_derive_Reals; exact: dS.
have cont x : u0 <= x <= u1 -> continuity_pt S x.
  by move=> _; apply: derivable_continuous_pt; exists (S' x); apply/is_derive_Reals; exact: dS.
have S01 : S u0 = S u1 by rewrite !Su //; [right; left | left].
have [zeta [[z0 z1] dz]] := Rolle S u0 u1 pr cont u01 S01.
have S'z : S' zeta = 0.
  rewrite -dz; apply/esym.
  exact: (derive_pt_eq_0 S zeta (S' zeta) (pr zeta (conj z0 z1)) (proj1 (is_derive_Reals _ _ _) (dS zeta))).
have [su1' fu1] := StronglySorted_inv su1; move: fu1; rewrite Forall_forall => fu1.
have u1last : u1 <= last u' u1 := sorted_head_last su1.
exists (zeta :: w); split; [|split].
- apply: SSorted_cons => //; apply/Forall_forall => z zw.
  by have [_ [_ [u1z _]]] := wP z zw; lra.
- by rewrite /= lenw.
- move=> z [<- | zw].
  + split=> //; split; last by rewrite last_cons_eq; lra.
    move=> [u0z | [u1z | zu']]; first by lra.
      by lra.
    by have := fu1 _ zu'; lra.
  + have [S'z' [znu [u1z zlast]]] := wP z zw; split => //; split; last by rewrite last_cons_eq; lra.
    by move=> [u0z | zin]; [lra | exact: znu].
Qed.

End Lists.

(* ------------------------------------------------------------------ *)
(* Part E: a few more list and sum lemmas.                             *)
(* ------------------------------------------------------------------ *)
Section MoreLemmas.

Lemma In_mem (l : seq R) (x : R) : x \in l <-> List.In x l.
Proof.
elim: l => [|y l IH] /=; first by rewrite in_nil.
rewrite in_cons; split.
- by case/orP => [/eqP ->|/IH]; [left | right].
- by case=> [->|/IH yl]; apply/orP; [left | right].
Qed.

Lemma size_length (l : seq R) : size l = List.length l.
Proof. by elim: l => [|x l IH] //=; rewrite IH. Qed.

Lemma list_nonempty (l : seq R) : List.length l <> O -> exists x, List.In x l.
Proof. by case: l => [|x l] // _; exists x; left. Qed.

Lemma NoDup_uniq (l : seq R) : List.NoDup l -> uniq l.
Proof.
elim: l => [|y l IH] //= /List.NoDup_cons_iff [yl ndl].
by rewrite IH // andbT; apply/negP => /In_mem.
Qed.

(* on a finite list, either g vanishes everywhere or it does not vanish somewhere *)
Lemma exists_nonzero (g : R -> R) (l : seq R) :
  (forall x, List.In x l -> g x = 0) \/ exists x, List.In x l /\ g x <> 0.
Proof.
elim: l => [|y l [IH|[x [xl gx]]]]; first by left.
- case: (Req_dec (g y) 0) => [gy|gy]; first by left=> x /= [<-|/IH].
  by right; exists y; split => //; left.
- by right; exists x; split => //; right.
Qed.

(* either all harmonics 1..n vanish or one of them does not *)
Lemma exists_harmonic (a b : nat -> R) (n : nat) :
  (forall k, (1 <= k <= n)%N -> a k = 0 /\ b k = 0) \/
  exists k, (1 <= k <= n)%N /\ (a k <> 0 \/ b k <> 0).
Proof.
elim: n => [|n [IH|[k [kn abk]]]]; first by left => k; lia.
- case: (Req_dec (a n.+1) 0) => [an|an]; last by right; exists n.+1; split; [lia | left].
  case: (Req_dec (b n.+1) 0) => [bn|bn]; last by right; exists n.+1; split; [lia | right].
  left => k kn; case: (Nat.eq_dec k n.+1) => [->|kn']; first by [].
  by apply: IH; lia.
- by right; exists k; split => //; lia.
Qed.

(* linear combinations of trigonometric sums *)
Lemma tp_lin (u v w t : nat -> R) (K : R) (m : nat) (x : R) :
  tp (fun k => u k + K * v k) (fun k => w k + K * t k) m x = tp u w m x + K * tp v t m x.
Proof.
rewrite /tp -[K * _]/(@mult R_Ring K _) -sum_n_mult_l -[_ + _]/(@plus R_AbelianGroup _ _) -sum_n_plus.
by apply: sum_n_ext => k; rewrite /mult /plus /=; ring.
Qed.

End MoreLemmas.

(* The statement, byte-identical to upstream. Set Implicit Arguments above was for the
   auxiliary lemmas only; it is switched off so that the theorem's arguments are
   explicit, as in the upstream file. *)
Unset Implicit Arguments.

Theorem putnam_1962_b6
    (n : nat)
    (a b : nat -> R)
    (xs : Ensemble R)
    (f : R -> R := (fun x : R => sum_n (fun k : nat => a k * sin (k * x) + b k * cos (k * x)) n))
    (hf1 : forall x : R, (0 <= x /\ x <= 2 * PI) -> abs (f x) <= 1)
    (hxs : cardinal R xs (2 * n) /\ (forall x : R, xs x -> 0 <= x /\ x < 2 * PI))
    (hfxs : forall x : R, xs x -> abs (f x) = 1)
    : (~exists c : R, f = (fun x : R => c)) -> (exists a : R, f = (fun x : R => cos (n * x + a))).
Proof.
move=> fnc; have pi0 := PI_RGT_0.
have fE x : f x = tp a b n x by [].
set a' := da a b; set b' := db a b.
set a'' := da a' b'; set b'' := db a' b'.
have f'D x : is_derive (tp a b n) x (tp a' b' n x) := tp_derive a b n x.
have f''D x : is_derive (tp a' b' n) x (tp a'' b'' n x) := tp_derive a' b' n x.
(* the bound, the 2n points, and the vanishing of f' there *)
have bnd x : 0 <= x <= 2 * PI -> Rabs (tp a b n x) <= 1.
  by move=> [x0 x2]; have := hf1 x (conj x0 x2).
have [l [ndl [lenl meml]]] := cardinal_list (proj1 hxs).
have lrange x : List.In x l -> 0 <= x < 2 * PI.
  by move=> /meml xl; exact: (proj2 hxs x xl).
have lzero x : List.In x l -> tp a' b' n x = 0.
  by move=> xl; apply: (tp_extremum bnd (lrange x xl)); have := hfxs x (proj1 (meml x) xl).
have ul : uniq l := NoDup_uniq ndl.
(* nonconstancy: some harmonic is present, and f' vanishes at no more than 2n points *)
have nconst : ~ (forall k, (1 <= k <= n)%N -> a k = 0 /\ b k = 0).
  by move=> ab0; apply: fnc; exists (b 0%N); apply: funext => x; rewrite fE; exact: tp_const.
have f'zeros (l' : seq R) : uniq l' -> (forall x, x \in l' -> 0 <= x < 2 * PI) ->
    (forall x, x \in l' -> tp a' b' n x = 0) -> ((2 * n).+1 <= size l')%N -> False.
  move=> ul' lr' l0' ls'; have [_ ab'0] := tp_zeros ul' lr' l0' ls'.
  apply: nconst => k k1n; have [a'k b'k] := ab'0 k k1n; move: a'k b'k.
  rewrite /a' /b' /da /db => a'k b'k.
  have kpos : 0 < INR k by apply: lt_0_INR; lia.
  by split; nra.
(* a point y of [0, 2 pi) where f' does not vanish, hence |f y| < 1 *)
pose c := PI / INR (2 * n).+1.
have c0 : 0 < c by apply: Rdiv_lt_0_compat => //; apply: lt_0_INR; lia.
pose qs := map (fun j : nat => INR j * c) (iota 0 (2 * n).+1).
have uqs : uniq qs.
  rewrite map_inj_uniq ?iota_uniq // => j j' /Rmult_eq_reg_r - /(_ (Rgt_not_eq _ _ c0)).
  exact: INR_eq.
have qsrange x : x \in qs -> 0 <= x < 2 * PI.
  move=> /mapP[j]; rewrite mem_iota add0n => /andP[_ jn] ->.
  have Nc : INR (2 * n).+1 * c = PI by rewrite /c; field; apply/not_0_INR; lia.
  have jc : INR j * c < PI by rewrite -Nc; apply: Rmult_lt_compat_r => //; apply: lt_INR; lia.
  split; [apply: Rmult_le_pos => //; [exact: pos_INR | exact: Rlt_le] | lra].
have qssize : size qs = (2 * n).+1 by rewrite size_map size_iota.
have [y [yqs f'y]] : exists y, List.In y qs /\ tp a' b' n y <> 0.
  case: (exists_nonzero (tp a' b' n) qs) => // allz; exfalso.
  apply: (f'zeros qs uqs qsrange); last by rewrite qssize.
  by move=> x /In_mem; exact: allz.
have yrange : 0 <= y < 2 * PI by apply: qsrange; apply/In_mem.
have ynl : ~ List.In y l by move=> /lzero.
have fy : Rabs (tp a b n y) < 1.
  have := bnd y (conj (proj1 yrange) (Rlt_le _ _ (proj2 yrange))).
  case/Rle_lt_or_eq_dec => // fy1; exfalso; apply: f'y.
  exact: (tp_extremum bnd yrange fy1).
have fy2 : 0 < 1 - tp a b n y * tp a b n y by have := Rabs_def2 _ _ fy; nra.
(* the auxiliary function S = f'^2 - K (1 - f^2), zero at the 2n points and at y *)
pose K := tp a' b' n y * tp a' b' n y / (1 - tp a b n y * tp a b n y).
pose S := fun x => tp a' b' n x * tp a' b' n x - K * (1 - tp a b n x * tp a b n x).
pose S' := fun x => (tp a'' b'' n x * tp a' b' n x + tp a' b' n x * tp a'' b'' n x)
                    - K * (0 - (tp a' b' n x * tp a b n x + tp a b n x * tp a' b' n x)).
have dS x : is_derive S x (S' x).
  apply/is_derive_Reals; rewrite /S /S'.
  apply: derivable_pt_lim_minus.
    by apply: derivable_pt_lim_mult; apply/is_derive_Reals; exact: f''D.
  apply: derivable_pt_lim_scal; apply: derivable_pt_lim_minus; first exact: derivable_pt_lim_const.
  by apply: derivable_pt_lim_mult; apply/is_derive_Reals; exact: f'D.
have S'E x : S' x = 2 * tp a' b' n x * (tp a'' b'' n x + K * tp a b n x) by rewrite /S'; ring.
have fsq x : List.In x l -> tp a b n x * tp a b n x = 1.
  move=> xl; have := hfxs x (proj1 (meml x) xl); rewrite /abs /= fE /Rabs.
  by case: Rcase_abs => _ H; nra.
have Sl x : List.In x l -> S x = 0 by move=> xl; rewrite /S lzero // fsq //; ring.
have Sy : S y = 0 by rewrite /S /K; field; lra.
have Speriod x : S (x + 2 * PI) = S x by rewrite /S !tp_period.
have S'period x : S' (x + 2 * PI) = S' x by rewrite /S' !tp_period.
(* sorting the 2n+1 zeros *)
have ndZ : List.NoDup (y :: l) by apply: List.NoDup_cons.
have Zrange x : List.In x (y :: l) -> 0 <= x < 2 * PI by move=> [<-|/lrange].
have SZ x : List.In x (y :: l) -> S x = 0 by move=> [<-|/Sl].
have su := sortR_sorted ndZ; have lenu := sortR_length (y :: l); have memu := sortR_in (y :: l).
move: su lenu memu; set u := sortR (y :: l); case: u => [|u0 u'] su lenu memu.
  by move: lenu; rewrite /= lenl.
have Su x : List.In x (u0 :: u') -> S x = 0 by move=> /memu; exact: SZ.
have urange x : List.In x (u0 :: u') -> 0 <= x < 2 * PI by move=> /memu; exact: Zrange.
have lenu' : length u' = (2 * n)%N by move: lenu; rewrite /= lenl; lia.
have [w [sw [lenw wP]]] := rolle_list dS su Su.
(* the last gap, from the last point round to the first point + 2 pi *)
have last_in_u : List.In (List.last u' u0) (u0 :: u').
  by case: u' su lenu memu Su urange lenu' sw lenw wP => [|u1 u'] *; [left | right; exact: last_in].
have u0_in : List.In u0 (u0 :: u') by left.
have ulast_range := urange _ last_in_u.
have u0_range := urange _ u0_in.
have u_le_last := sorted_le_last su.
have u0_le x : List.In x (u0 :: u') -> u0 <= x.
  move=> [<-|xu']; first exact: Rle_refl.
  by have [_ fu0] := StronglySorted_inv su; move: fu0; rewrite List.Forall_forall => fu0; apply: Rlt_le; apply: fu0.
have gap : List.last u' u0 < u0 + 2 * PI by lra.
have prr x : List.last u' u0 < x < u0 + 2 * PI -> derivable_pt S x.
  by move=> _; exists (S' x); apply/is_derive_Reals; exact: dS.
have contr x : List.last u' u0 <= x <= u0 + 2 * PI -> continuity_pt S x.
  by move=> _; apply: derivable_continuous_pt; exists (S' x); apply/is_derive_Reals; exact: dS.
have Sgap : S (List.last u' u0) = S (u0 + 2 * PI) by rewrite Speriod !Su.
have [zeta [[zl zr] dz]] := Rolle S _ _ prr contr gap Sgap.
have S'zeta : S' zeta = 0.
  rewrite -dz; apply/esym.
  exact: (derive_pt_eq_0 S zeta (S' zeta) (prr zeta (conj zl zr)) (proj1 (is_derive_Reals _ _ _) (dS zeta))).
(* the point zeta, brought back to [0, 2 pi), is a zero of S' outside u and w *)
have [zeta' [S'zeta' [zr' [znu znw]]]] : exists zeta', S' zeta' = 0 /\ 0 <= zeta' < 2 * PI /\
    ~ List.In zeta' (u0 :: u') /\ ~ List.In zeta' w.
  case: (Rlt_dec zeta (2 * PI)) => [z2|/Rnot_lt_le z2].
    exists zeta; split => //; split; first by lra.
    split=> [/u_le_last|/wP [_ [_ [_ zlast]]]]; lra.
  exists (zeta - 2 * PI); split.
    by rewrite -(S'period (zeta - 2 * PI)) (_ : zeta - 2 * PI + 2 * PI = zeta) //; ring.
  split; first by lra.
  split=> [/u0_le|/wP [_ [_ [u0z _]]]]; lra.
(* f'' + K f vanishes at the 2n+1 points zeta' :: w, where f' does not vanish *)
have lu x : List.In x l -> List.In x (u0 :: u') by move=> xl; apply/memu; right.
have f'nz z : 0 <= z < 2 * PI -> ~ List.In z (u0 :: u') -> tp a' b' n z <> 0.
  move=> zrg znu2 f'z; apply: (f'zeros (z :: l)).
  - by rewrite /= ul andbT; apply/negP => /In_mem zl2; apply: znu2; exact: lu.
  - by move=> x; rewrite in_cons => /orP[/eqP ->|/In_mem/lrange].
  - by move=> x; rewrite in_cons => /orP[/eqP ->|/In_mem/lzero].
  - by rewrite size_length /= lenl.
pose Zeta := zeta' :: w.
have ndZeta : List.NoDup Zeta by apply: List.NoDup_cons => //; exact: sorted_NoDup.
have Zrange' z : List.In z Zeta -> 0 <= z < 2 * PI.
  by move=> [<-|/wP [_ [_ [u0z zlast]]]] //; lra.
have Zsize : size Zeta = (2 * n).+1 by rewrite size_length /= lenw lenu'.
have Gzero z : List.In z Zeta -> tp a'' b'' n z + K * tp a b n z = 0.
  move=> zZ; have zrg := Zrange' z zZ.
  have [S'z znu'] : S' z = 0 /\ ~ List.In z (u0 :: u').
    by case: zZ => [<-|/wP [S'z [znu' _]]] //.
  have := f'nz z zrg znu'; move: S'z; rewrite S'E => /Rmult_integral [/Rmult_integral [|]|] //.
  by move=> H1 H2; exfalso; apply: H2; lra.
pose aG := fun k : nat => a'' k + K * a k.
pose bG := fun k : nat => b'' k + K * b k.
have [bG0 abG] := tp_zeros (al := aG) (be := bG) (m := n) (l := Zeta) (NoDup_uniq ndZeta)
  (fun x xZ => Zrange' x (proj1 (In_mem _ _) xZ))
  (fun x xZ => (etrans (tp_lin _ _ _ _ _ _ _) (Gzero x (proj1 (In_mem _ _) xZ))))
  (eq_leq (esym Zsize)).
(* the coefficient equations: (K - k^2) a_k = 0, (K - k^2) b_k = 0, K b_0 = 0 *)
have coefk k : (1 <= k <= n)%N -> (K - INR k * INR k) * a k = 0 /\ (K - INR k * INR k) * b k = 0.
  move=> k1n; have [ak bk] := abG k k1n; move: ak bk.
  by rewrite /aG /bG /a'' /b'' /a' /b' /da /db => ak bk; split; lra.
have Kb0 : K * b 0%N = 0 by move: bG0; rewrite /bG /b'' /db /= Rmult_0_l Rplus_0_l.
(* the harmonic j0 that is present forces K = j0^2 and kills the other harmonics *)
have [ab0|[j0 [j0n abj0]]] := exists_harmonic a b n; first by exfalso; exact: nconst.
have Kj0 : K = INR j0 * INR j0.
  have [aj bj] := coefk j0 j0n; case: abj0 => [aj0|bj0].
  - by move: aj => /Rmult_integral [|] //; lra.
  - by move: bj => /Rmult_integral [|] //; lra.
have others k : (1 <= k <= n)%N -> k <> j0 -> a k = 0 /\ b k = 0.
  move=> k1n kj0; have [ak bk] := coefk k k1n; rewrite Kj0 in ak bk.
  have jk : INR j0 * INR j0 - INR k * INR k <> 0.
    move=> H; apply: kj0; apply/esym/INR_eq.
    by have := pos_INR j0; have := pos_INR k; nra.
  by split; [move: ak | move: bk] => /Rmult_integral [|] //.
have j0pos : 0 < INR j0 by apply: lt_0_INR; lia.
have b0 : b 0%N = 0 by move: Kb0; rewrite Kj0 => /Rmult_integral [|] //; nra.
have fS x : tp a b n x = a j0 * sin (j0 * x) + b j0 * cos (j0 * x) by apply: tp_single.
have f'S x : tp a' b' n x = a' j0 * sin (j0 * x) + b' j0 * cos (j0 * x).
  apply: tp_single => //; first by rewrite /b' /db /= Rmult_0_l.
  by move=> k k1n kj0; rewrite /a' /b' /da /db; have [-> ->] := others k k1n kj0; split; ring.
(* j0 = n: otherwise f', of degree j0 < n, would vanish at 2n >= 2 j0 + 1 points *)
have j0n' : j0 = n.
  have [j01 j0n''] := andP j0n; apply/eqP; rewrite eqn_leq j0n'' /= leqNgt; apply/negP => j0ltn.
  have f'j0 x : tp a' b' j0 x = tp a' b' n x.
    rewrite f'S; apply: tp_single => //; [lia | by rewrite /b' /db /= Rmult_0_l |].
    by move=> k k1n kj0; rewrite /a' /b' /da /db; have [-> ->] := others k (ltac:(lia) : (1 <= k <= n)%N) kj0; split; ring.
  have [_ ab'j0] := tp_zeros (al := a') (be := b') (m := j0) (l := l) ul
    (fun x xl => lrange x (proj1 (In_mem _ _) xl))
    (fun x xl => etrans (f'j0 x) (lzero x (proj1 (In_mem _ _) xl)))
    (ltac:(rewrite size_length lenl; lia) : ((2 * j0).+1 <= size l)%N).
  have [a'j b'j] := ab'j0 j0 (ltac:(lia) : (1 <= j0 <= j0)%N); move: a'j b'j.
  rewrite /a' /b' /da /db => a'j b'j; case: abj0 => [aj0|bj0]; [apply: aj0 | apply: bj0]; nra.
subst j0.
(* a_n^2 + b_n^2 = 1, from f = +-1 and f' = 0 at one of the 2n points *)
have [x1 x1l] : exists x1, List.In x1 l by apply: list_nonempty; rewrite lenl; lia.
have norm1 : a n * a n + b n * b n = 1.
  have := fsq x1 x1l; have := lzero x1 x1l; rewrite fS f'S /a' /b' /da /db.
  have := sin2_cos2 (n * x1); rewrite /Rsqr.
  set sn := sin (n * x1); set cn := cos (n * x1) => sc f'x1 fx1.
  have npos : 0 < INR n by apply: lt_0_INR; lia.
  have h : a n * cn - b n * sn = 0.
    have : INR n * (a n * cn - b n * sn) = 0 by rewrite -f'x1; ring.
    by move=> /Rmult_integral [|] //; lra.
  have key : (a n * sn + b n * cn) * (a n * sn + b n * cn) + (a n * cn - b n * sn) * (a n * cn - b n * sn)
           = (a n * a n + b n * b n) * (sn * sn + cn * cn) by ring.
  by rewrite fx1 h sc in key; lra.
(* the angle a with cos a = b_n and sin a = - a_n *)
have norm1' : b n * b n + - a n * - a n = 1 by lra.
have [phi [cphi sphi]] := angle_exists norm1'.
exists phi; apply: funext => x.
by rewrite fE fS cos_plus cphi sphi; ring.
Qed.
