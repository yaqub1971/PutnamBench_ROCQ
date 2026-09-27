(* ============================================================================
   PutnamBench 1962 A2 -- Rocq proof of the CORRECTED statement.
   Problem: find every nonnegative real function f on [0, +oo), or on an interval
   [0, e), such that for every x > 0 in the domain the mean value of f over [0, x]
   equals the geometric mean of f 0 and f x:  (1/x) int_0^x f = sqrt (f 0 * f x).
   Statement: coq/src/putnam_1962_a2.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20), with the
   one change of putnam_1962_a2_corrected.v: the solution set is the four-family set of
   PutnamBench's Lean statement, transcribed, instead of the single family
   a / (1 - c x)^2 (with which the theorem is false: putnam_1962_a2_statement_is_false.v).
   The Definition of the solution set and the Theorem block below are byte-identical to
   putnam_1962_a2_corrected.v; only the extra imports, the auxiliary lemmas and the
   proof script were added.
   Reading the statement: "\int[mu]_(t in D) f t" in ring_scope is MathComp-Analysis'
   real-valued integral (Rintegral), the finite part of the Lebesgue integral, which is
   0 when that integral is +oo; f is not assumed measurable, so the Lebesgue integral of
   f is its lower integral; mu is Lebesgue measure.
   Proof idea. Write F x for the integral of f over [0, x] and a for f 0; the domain D
   is (0, +oo) or (0, e). The hypothesis says F x = x * sqrt (a * f x) on D.
   - a = 0: then F = 0 on D, and f itself belongs to the fourth family.
   - a > 0: then f x = (F x)^2 / (a x^2) on D. Let U be the set of x in D where the
     Lebesgue integral of f over [0, x] is finite; U is an initial segment of D. For u
     in U, F is nondecreasing on [0, u], hence f = F^2/(a x^2) is measurable and
     integrable on [0, u], F is continuous on [0, u] and f on (0, u); by the fundamental
     theorem of calculus F' = f there, so K = 1/F - 1/(a x) has derivative 0 wherever
     F > 0, and the mean value theorem gives 1/F x - 1/F z = (1/a)(1/x - 1/z) on every
     [x, z] inside U on which F > 0. With the intermediate value theorem this forces F
     to be either 0 on all of U or positive on all of U.
     * F = 0 on U: outside U the integral is +oo, so F = 0 on all of D, hence f = 0 on
       D, and f agrees on the domain with a member of the third family (g x = 0 for
       x > 0, g 0 = f 0).
     * F > 0 on U: fixing z in U and putting c := -a (1/F z - 1/(a z)), the identity
       gives F x = a x / (1 - c x), so f x = a / (1 - c x)^2 on U. Bounding f by a
       constant on [0, x] shows that U is exactly the part of D where 1 - c x > 0;
       outside U the integral is +oo, so F x = 0 and f x = 0. Thus f agrees on the
       domain with a member of the first family (c <= 0) or of the second (c > 0).
   - Conversely, a / (1 - c t)^2 has the primitive a t / (1 - c t), so by the
     Newton-Leibniz formula its mean value over [0, x] is a / (1 - c x), which is
     sqrt (a * a / (1 - c x)^2), whenever 1 - c x > 0: the first family satisfies the
     condition on (0, +oo) if c <= 0 and on (0, 1/c) if c > 0, and the second family
     on (0, 1/c). The third family has zero integral (the integrand vanishes off the
     null set {0}) and the fourth has zero integral by definition; in both cases the
     two sides of the condition are 0.
   Produced with Claude Fable 5.1 (Anthropic), September 2026; all checks run by the repository author.
   Verified on Rocq 9.1.0 / MathComp 2.5 / MathComp-Analysis 1.16.0 (Rocq Platform 2026.07, macOS):
   compiles; Print Assumptions putnam_1962_a2 lists only the Variable R declared by the
   statement and the three classical axioms that mathcomp.reals is built on
   (propositional_extensionality, functional_extensionality_dep,
   constructive_indefinite_description); rocqchk: "Modules were successfully checked".
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1 / MathComp 2.5 (Rocq Platform 2026.07) the import lines
   trigger ~40 warnings emitted by MathComp itself (all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations). They are library
   warnings, not warnings about this file: none of this file's own lines produce any.
   The upstream import lines are kept exactly as upstream wrote them so that the
   statement stays identical to the benchmark's.
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

(* Extra imports for the proof (they add nothing to the statement). *)
From mathcomp Require Import boolp functions set_interval numfun constructive_ereal ereal.
From mathcomp Require Import measurable_realfun realfun ftc interval ring lra.
Import GRing.Theory Num.Theory Order.Theory.
Import numFieldNormedType.Exports.

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

(* ------------------------------------------------------------------ *)
(* Part 1: facts about the lower Lebesgue integral of an arbitrary     *)
(* nonnegative function (the statement's f is not assumed measurable). *)
(* ------------------------------------------------------------------ *)
Section LowerIntegral.

(* monotone in the integrand, no measurability needed *)
Lemma ge0_le_integral_nm (A : set R) (g h : R -> \bar R) :
  (forall t, 0 <= g t)%E -> (forall t, 0 <= h t)%E -> (forall t, A t -> g t <= h t)%E ->
  (\int[mu]_(t in A) g t <= \int[mu]_(t in A) h t)%E.
Proof.
move=> g0 h0 gh; rewrite !ge0_integralE//; apply: ge_ereal_sup => _ /= [k kg <-].
apply: ereal_sup_ubound; exists k => //= t; apply: le_trans (kg t) _.
exact: lee_restrict.
Qed.

(* monotone in the domain, no measurability needed *)
Lemma ge0_subset_integral_nm (A B : set R) (g : R -> \bar R) :
  (forall t, 0 <= g t)%E -> A `<=` B ->
  (\int[mu]_(t in A) g t <= \int[mu]_(t in B) g t)%E.
Proof.
move=> g0 AB; rewrite !ge0_integralE//; apply: ge_ereal_sup => _ /= [k kg <-].
apply: ereal_sup_ubound; exists k => //= t; apply: le_trans (kg t) _.
exact: restrict_lee.
Qed.

End LowerIntegral.

(* ------------------------------------------------------------------ *)
(* Part 2: measurability helpers.                                      *)
(* ------------------------------------------------------------------ *)
Section Measurability.

Lemma measurable_fun_set1' (g : R -> R) (p : R) : measurable_fun [set p] g.
Proof.
move=> _ Y mY; have [gpY|gpY] := pselect (Y (g p)).
- rewrite (_ : [set p] `&` g @^-1` Y = [set p]); first exact: measurable_set1.
  by apply/seteqP; split => t /=; [case | move=> ->].
- rewrite (_ : [set p] `&` g @^-1` Y = set0); first exact: measurable0.
  by apply/seteqP; split => t //= [->].
Qed.

(* the statement's integration set is the closed interval [0, x] *)
Lemma set_cc (x : R) : [set t | 0 <= t <= x] = `[0, x] :> set R.
Proof. by apply/seteqP; split => t /=; rewrite in_itv. Qed.

End Measurability.

(* ------------------------------------------------------------------ *)
(* Part 3: the calculus facts used (the two forms of the fundamental    *)
(* theorem of calculus and the continuity of x |-> int_0^x g), in the   *)
(* shape needed below.                                                  *)
(* ------------------------------------------------------------------ *)
Section Calculus.

(* FTC, first form: the integral function of an integrable g is derivable at
   every point where g is continuous, with derivative g *)
Lemma FTC1_here (g : R -> R) (x : R) : mu.-integrable setT (EFin \o g) ->
  0 < x -> {for x, continuous g} ->
  derivable (fun y : R => \int[mu]_(t in `[0, y]) g t) x 1 /\
  derive1 (fun y : R => \int[mu]_(t in `[0, y]) g t) x = g x.
Proof.
move=> ig x0 cg.
have ig' : mu.-integrable [set` Interval (BLeft 0) (BRight (x + 1))] (EFin \o g).
  by apply: integrableS ig => //; exact: measurable_itv.
have x1 : x < x + 1 by rewrite ltrDl ltr01.
have := @continuous_FTC1 R g (BLeft 0) x (x + 1) x1 ig' _ cg.
by apply; rewrite /= lte_fin.
Qed.

(* the integral function of an integrable g is continuous on [0, z] *)
Lemma PIC_here (g : R -> R) (z : R) : 0 < z -> mu.-integrable `[0, z] (EFin \o g) ->
  {within `[0, z], continuous (fun y : R => \int[mu]_(t in `[0, y]) g t)}.
Proof. by move=> z0 ig; exact: (parameterized_integral_continuous (ltW z0) ig). Qed.

(* FTC, second form (Newton-Leibniz) *)
Lemma FTC2_here (h H : R -> R) (x : R) : 0 < x ->
  {in `[0, x]%R, continuous h} ->
  {in `]0, x[%R, forall t, derivable H t 1} ->
  H @ 0^'+ --> H 0 -> H @ x^'- --> H x ->
  {in `]0, x[%R, derive1 H =1 h} ->
  (\int[mu]_(t in `[0%R, x]%classic) (h t)%:E = (H x)%:E - (H 0%R)%:E)%E.
Proof.
move=> x0 ch dH H0 Hx H'.
have ch' : {in (`[0, x] : set R), continuous h} by move=> t /set_mem tx; exact: (ch t tx).
by exact: (continuous_FTC2 x0 (continuous_in_subspaceT ch') (And3 dH H0 Hx) H').
Qed.

End Calculus.

(* ------------------------------------------------------------------ *)
(* Part 4: continuity helpers.                                          *)
(* ------------------------------------------------------------------ *)
Section Continuity.

Lemma continuous_near_eq (h k : R -> R) (t : R) :
  (\forall s \near t, h s = k s) -> {for t, continuous h} -> {for t, continuous k}.
Proof.
move=> hk ch; rewrite /prop_for/= /continuous_at -(nbhs_singleton hk).
exact: cvg_trans (near_eq_cvg hk) ch.
Qed.

Lemma continuous_id' (t : R) : {for t, continuous (@id R)}.
Proof. exact: cvg_id. Qed.

Lemma continuous_cst' (c t : R) : {for t, continuous (fun _ : R => c)}.
Proof. exact: cvg_cst. Qed.

Lemma continuous_mul' (h k : R -> R) (t : R) :
  {for t, continuous h} -> {for t, continuous k} -> {for t, continuous (fun s => h s * k s)}.
Proof. by move=> ch ck; exact: cvgM. Qed.

Lemma continuous_sub' (h k : R -> R) (t : R) :
  {for t, continuous h} -> {for t, continuous k} -> {for t, continuous (fun s => h s - k s)}.
Proof. by move=> ch ck; exact: cvgB. Qed.

Lemma continuous_inv' (h : R -> R) (t : R) : h t != 0 ->
  {for t, continuous h} -> {for t, continuous (fun s => (h s)^-1)}.
Proof. by move=> ht0 ch; exact: continuousV. Qed.

End Continuity.

(* ------------------------------------------------------------------ *)
(* Part 5: the core of the argument.                                    *)
(* ------------------------------------------------------------------ *)
Lemma axx_neq0 (a x : R) : 0 < a -> 0 < x -> a * (x * x) != 0.
Proof. by move=> a0 x0; apply: mulf_neq0; [rewrite gt_eqF | apply: mulf_neq0; rewrite gt_eqF]. Qed.

(* the algebraic identity behind K' = 0 below *)
Lemma dK_alg (a t p : R) : a != 0 -> t != 0 -> p != 0 ->
  - p ^- 2 * (p * p / (a * (t * t))) - - (a * t) ^- 2 * (a * 1) = 0.
Proof.
move=> a0 t0 p0.
rewrite mulr1 !mulNr; apply/eqP; rewrite subr_eq0 eqr_opp; apply/eqP.
rewrite -[p * p]expr2 [p ^- 2 * (_ * _)]mulrA mulVf ?expf_neq0// mul1r.
rewrite expr2 !invfM -!mulrA; congr (_ * (_ * _)).
by rewrite [t^-1 * a]mulrC mulrA mulVf// mul1r.
Qed.

Section Core.

Variable f : R -> R.
Hypothesis f_ge0 : forall x, 0 <= f x.

(* the extended-real integral over [0, x] and its real part F *)
Let I (x : R) : \bar R := \int[mu]_(t in `[0, x]) (f t)%:E.
Let F (x : R) : R := \int[mu]_(t in `[0, x]) f t.

Lemma FI x : F x = fine (I x). Proof. by []. Qed.

Lemma I_ge0 x : (0 <= I x)%E.
Proof. by apply: integral_ge0 => t _; rewrite lee_fin. Qed.

Lemma F_ge0 x : 0 <= F x.
Proof. by rewrite FI fine_ge0// I_ge0. Qed.

Lemma I_mono x y : x <= y -> (I x <= I y)%E.
Proof.
move=> xy; apply: ge0_subset_integral_nm => [t|t]; first by rewrite lee_fin.
by rewrite /= !in_itv/= => /andP[-> /le_trans]; exact.
Qed.

Lemma I_fin x : (I x < +oo)%E -> I x \is a fin_num.
Proof. by rewrite ge0_fin_numE// I_ge0. Qed.

Lemma F_mono x y z : x <= y -> y <= z -> (I z < +oo)%E -> F x <= F y.
Proof.
move=> xy yz Iz; rewrite !FI; apply: fine_le; last exact: I_mono.
- by apply: I_fin; exact: le_lt_trans (I_mono (le_trans xy yz)) Iz.
- by apply: I_fin; exact: le_lt_trans (I_mono yz) Iz.
Qed.

Lemma F_pinfty x : I x = +oo%E -> F x = 0.
Proof. by move=> Ix; rewrite FI Ix. Qed.

(* the domain of the hypothesis: 0 < x < e, with e possibly +oo *)
Variable e : \bar R.
Hypothesis hP : forall x, 0 < x -> (x%:E < e)%E -> 1 / x * F x = Num.sqrt (f 0 * f x).

Let a := f 0.

Lemma FE x : 0 < x -> (x%:E < e)%E -> F x = x * Num.sqrt (a * f x).
Proof. by move=> x0 xe; rewrite -(hP x0 xe) div1r mulrA mulfV ?mul1r// gt_eqF. Qed.

Lemma fE x : 0 < a -> 0 < x -> (x%:E < e)%E -> f x = F x * F x / (a * (x * x)).
Proof.
move=> a0 x0 xe; rewrite FE//; set s := Num.sqrt (a * f x).
have s2 : s * s = a * f x by rewrite -expr2 sqr_sqrtr// mulr_ge0// ltW.
have axx : a * (x * x) != 0 by exact: axx_neq0.
rewrite mulrACA s2 -[LHS](mulfK axx); congr (_ / _); lra.
Qed.

(* the points of the domain where the integral is finite *)
Let U : set R := [set x | 0 < x /\ (x%:E < e)%E /\ (I x < +oo)%E].

Lemma U_down x y : U y -> 0 < x -> x <= y -> U x.
Proof.
move=> [y0 [ye Iy]] x0 xy; split=> //; split.
- by apply: le_lt_trans ye; rewrite lee_fin.
- exact: le_lt_trans (I_mono xy) Iy.
Qed.

(* f is measurable on [0, u] for u in U: on ]0, u] it is a rational expression
   in F, and F is nondecreasing there *)
Lemma f_measurable_U u : 0 < a -> U u -> measurable_fun `[0, u] f.
Proof.
move=> a0 Uu; have [u0 [ue Iu]] := Uu.
pose Fu := fun x => F (Order.min x u).
have Fu_nd x y : x <= y -> Fu x <= Fu y.
  move=> xy; apply: (@F_mono _ _ u) => //.
  - by rewrite le_min ge_min xy/= ge_min lexx orbT.
  - by rewrite ge_min lexx orbT.
have mFu : measurable_fun `]0, u] Fu.
  by apply: nondecreasing_measurable; [exact: measurable_itv | exact: Fu_nd].
have mf_oc : measurable_fun `]0, u] f.
  apply: (@eq_measurable_fun _ _ _ _ _ (fun x => Fu x * Fu x * (a * (x * x))^-1)).
    move=> x; rewrite inE/= in_itv/= => /andP[x0 xu].
    by rewrite /Fu (min_l xu) -fE// (le_lt_trans _ ue)// lee_fin.
  apply: measurable_funM; first exact: measurable_funM.
  apply: subspace_continuous_measurable_fun; first exact: measurable_itv.
  rewrite continuous_subspace_in => x; rewrite inE/= => xu.
  apply: continuous_subspaceT_for => //.
  have [x0 _] := andP (xu : (0 < x <= u)).
  apply: continuous_inv'; first exact: axx_neq0.
  by apply: continuous_mul'; [exact: continuous_cst' | apply: continuous_mul'; exact: continuous_id'].
have -> : `[0, u] = [set 0] `|` `]0, u] :> set R.
  apply/seteqP; split => t /=; rewrite !in_itv/= ?andbT.
  - by move=> /andP[]; rewrite le_eqVlt => /orP[/eqP <- _|-> ->]; [left | right].
  - by move=> [-> |/andP[/ltW -> ->]]; rewrite ?lexx ?ltW.
apply/measurable_funU; [exact: measurable_set1 | exact: measurable_itv | split => //].
exact: measurable_fun_set1'.
Qed.

Lemma f_integrable_U u : 0 < a -> U u -> mu.-integrable `[0, u] (EFin \o f).
Proof.
move=> a0 Uu; have [u0 [ue Iu]] := Uu; apply/integrableP; split.
  by apply/measurable_EFinP; exact: f_measurable_U.
by under eq_integral do rewrite /= ger0_norm//.
Qed.

(* F is continuous on [0, u] for u in U *)
Lemma F_cont_U u : 0 < a -> U u -> {within `[0, u], continuous F}.
Proof. by move=> a0 Uu; have [u0 _] := Uu; exact: (PIC_here u0 (f_integrable_U a0 Uu)). Qed.

Lemma F_cont_oo u : 0 < a -> U u -> {in `]0, u[%R, continuous F}.
Proof.
move=> a0 Uu; have [u0 _] := Uu.
by have := F_cont_U a0 Uu; rewrite (continuous_within_itvP _ u0) => -[].
Qed.

(* f is continuous on ]0, u[ for u in U *)
Lemma f_cont_oo u : 0 < a -> U u -> {in `]0, u[%R, continuous f}.
Proof.
move=> a0 Uu t tu; have [u0 [ue _]] := Uu.
apply: (@continuous_near_eq (fun s => F s * F s * (a * (s * s))^-1)).
  near=> s; have : s \in `]0, u[%R by near: s; exact: (near_in_itvoo tu).
  rewrite in_itv/= => /andP[s0 su].
  by rewrite -fE// (lt_trans _ ue)// lte_fin.
have Ft := F_cont_oo a0 Uu tu; move: tu; rewrite in_itv/= => /andP[t0 tu].
apply: continuous_mul'; first exact: continuous_mul'.
apply: continuous_inv'; first exact: axx_neq0.
by apply: continuous_mul'; [exact: continuous_cst' | apply: continuous_mul'; exact: continuous_id'].
Unshelve. all: by end_near. Qed.

(* the ODE identity: on any interval [x, z] inside U where F > 0,
   1/F x - 1/F z = (1/a) (1/x - 1/z) *)
Lemma ode_identity x z : 0 < a -> U z -> 0 < x -> x < z ->
  (forall t, x <= t <= z -> 0 < F t) ->
  (F x)^-1 - (F z)^-1 = a^-1 * (x^-1 - z^-1).
Proof.
move=> a0 Uz x0 xz Fpos; have [z0 [ze Iz]] := Uz.
(* the restriction of f to [0, z], integrable on the whole line *)
pose g := f \_ `[0, z].
pose G y := \int[mu]_(t in `[0, y]) g t.
have gf t : t \in `[0, z] -> g t = f t by move=> tz; rewrite /g patchT.
have GF y : y <= z -> G y = F y.
  move=> yz; rewrite /G /F /Rintegral; congr fine; apply: eq_integral => t.
  rewrite inE/= in_itv/= => /andP[t0 ty].
  by rewrite gf// inE/= in_itv/= t0 (le_trans ty yz).
have ig : mu.-integrable setT (EFin \o g).
  rewrite /g -restrict_EFin; apply/integrable_restrict; [exact: measurable_itv | by [] | ].
  by rewrite setTI; exact: f_integrable_U.
have cg : {in `]0, z[%R, continuous g}.
  move=> t tz; have cf := f_cont_oo a0 Uz.
  apply: (continuous_near_eq (h := f)); last exact: (cf t tz).
  near=> s; have : s \in `]0, z[%R by near: s; exact: (near_in_itvoo tz).
  by rewrite in_itv/= => /andP[s0 sz]; rewrite gf// inE/= in_itv/= (ltW s0) ltW.
(* derivative of G on ]0, z[ *)
have dG t : t \in `]0, z[%R -> derivable G t 1 /\ derive1 G t = f t.
  move=> tz; have [t0 _] := andP (tz : (0 < t < z)); rewrite -gf; last first.
    by move: tz; rewrite inE/= !in_itv/= => /andP[/ltW -> /ltW ->].
  exact: (FTC1_here ig t0 (cg _ tz)).
(* K := 1/G - 1/(a id) has derivative 0 on ]x, z[ *)
pose K y := (G y)^-1 - (a * y)^-1.
have dK t : t \in `]x, z[%R -> is_derive t 1 K 0.
  move=> txz; have [xt tz] := andP (txz : (x < t < z)).
  have tz' : t \in `]0, z[%R by rewrite in_itv/= tz (lt_trans x0).
  have [dGt G't] := dG _ tz'.
  have Gt : G t = F t by rewrite GF// ltW.
  have Ft0 : 0 < F t by apply: Fpos; rewrite (ltW xt) ltW.
  have isG : is_derive t 1 G (f t) by apply: DeriveDef => //; rewrite -derive1E.
  have t0 : 0 < t by exact: (lt_trans x0 xt).
  apply: (is_derive_eq (is_deriveB (is_deriveV _ isG) (is_deriveV _ (is_deriveZ a (is_derive_id t 1))))).
  - by rewrite Gt gt_eqF.
  - by apply: mulf_neq0; rewrite gt_eqF.
  rewrite /GRing.scale/= Gt (fE a0 t0); last by apply: lt_trans ze; rewrite lte_fin.
  by rewrite -[a *: t]/(a * t); apply: dK_alg; rewrite gt_eqF.
have cK : {within `[x, z], continuous K}.
  have cG : {within `[x, z], continuous G}.
    have igz : mu.-integrable `[0, z] (EFin \o g).
      by apply: (integrableS measurableT) => //; exact: measurable_itv.
    apply: (continuous_subspaceW _ (PIC_here z0 igz)).
    by move=> t; rewrite /= !in_itv/= => /andP[/(le_trans (ltW x0)) -> ->].
  move: cG; rewrite continuous_subspace_in => cG; rewrite continuous_subspace_in => y yxz.
  have cGy := cG y yxz; move: yxz; rewrite inE/= => yxz.
  have [xy yz] := andP (yxz : (x <= y <= z)).
  have y0 : 0 < y := lt_le_trans x0 xy.
  apply: cvgB.
  - apply: cvgV; last exact: cGy.
    by rewrite GF// gt_eqF// Fpos// xy yz.
  - have : {for y, continuous ((fun s => (a * s)^-1) : subspace `[x, z] -> R)}.
      apply: continuous_subspaceT_for => //.
      apply: continuous_inv'; first by rewrite mulf_neq0// gt_eqF.
      by apply: continuous_mul'; [exact: continuous_cst' | exact: continuous_id'].
    by [].
have [c cxz Kxz] := @MVT _ K (fun _ => 0) x z xz dK cK.
move: Kxz; rewrite mul0r /K !GF// ?lexx// ?ltW// => /subr0_eq/esym.
move/eqP; rewrite subr_eq => /eqP ->.
by rewrite mulrBr !invfM; lra.
Unshelve. all: by end_near. Qed.


(* ------------------------------------------------------------------ *)
(* Part 6: with a > 0, either F = 0 on U or F > 0 on U; in the second   *)
(* case F, hence f, has the textbook closed form on U, and U is exactly *)
(* the part of the domain where 1 - c x > 0.                            *)
(* ------------------------------------------------------------------ *)
Section Pos.
Hypothesis a0 : 0 < a.

(* F cannot vanish at one point of U and be positive at another *)
Lemma F_dichotomy x z : U x -> U z -> F x = 0 -> 0 < F z -> False.
Proof.
move=> Ux Uz Fx0 Fz0.
have [x0 [xe Ix]] := Ux; have [z0 [ze Iz]] := Uz.
have xz : x < z.
  rewrite ltNge; apply/negP => zx.
  by have := F_mono zx (lexx x) Ix; rewrite Fx0 => Fz_le0; move: Fz0; rewrite ltNge Fz_le0.
(* the ODE identity on [u, z] bounds 1/F u for every u in ]x, z] with F u > 0 *)
have hxz : 0 <= a^-1 * (x^-1 - z^-1).
  by rewrite mulr_ge0 ?invr_ge0 ?(ltW a0)// subr_ge0 lef_pV2 ?posrE// ltW.
have bound u : x < u -> u <= z -> 0 < F u -> (F u)^-1 <= (F z)^-1 + a^-1 * (x^-1 - z^-1).
  move=> xu uz Fu0.
  have Fpos t : u <= t <= z -> 0 < F t.
    by move=> /andP[ut tz]; exact: lt_le_trans Fu0 (F_mono ut tz Iz).
  have u0 : 0 < u := lt_trans x0 xu.
  move: uz; rewrite le_eqVlt => /orP[/eqP ->|uz]; first by rewrite lerDl.
  have := ode_identity a0 Uz u0 uz Fpos.
  move/eqP; rewrite subr_eq => /eqP ->; rewrite addrC lerD2l ler_pM2l ?invr_gt0//.
  by rewrite lerD2r lef_pV2 ?posrE// ltW.
pose B := (F z)^-1 + a^-1 * (x^-1 - z^-1).
have Fzi : 0 < (F z)^-1 by rewrite invr_gt0.
have B0 : 0 < B by rewrite /B; lra.
have Bi0 : 0 < B^-1 by rewrite invr_gt0.
(* a value v strictly between 0 and both F z and 1/B *)
pose v := Order.min (B^-1 / 2) (F z / 2).
have v0 : 0 < v by rewrite lt_min; apply/andP; split; lra.
have vB : v < B^-1 by rewrite gt_min; apply/orP; left; lra.
have vFz : v < F z by rewrite gt_min; apply/orP; right; lra.
(* the intermediate value theorem gives F u = v for some u in [x, z] *)
have cF : {within `[x, z], continuous F}.
  apply: (continuous_subspaceW _ (F_cont_U a0 Uz)).
  by move=> t; rewrite /= !in_itv/= => /andP[/(le_trans (ltW x0)) -> ->].
have vminmax : Order.min (F x) (F z) <= v <= Order.max (F x) (F z).
  by rewrite Fx0 (min_l (ltW Fz0)) (max_r (ltW Fz0)) (ltW v0) (ltW vFz).
have [u uxz Fuv] := IVT (ltW xz) cF vminmax.
move: uxz; rewrite in_itv/= => /andP[xu uz].
have Fu0 : 0 < F u by rewrite Fuv.
have xu' : x < u.
  rewrite lt_neqAle xu andbT; apply/eqP => xu'.
  by move: Fu0; rewrite -xu' Fx0 ltxx.
(* but then 1/v <= B, i.e. v >= 1/B: contradiction *)
have := bound u xu' uz Fu0; rewrite Fuv -/B leNgt => /negP; apply.
by rewrite -[B]invrK ltf_pV2 ?posrE ?invr_gt0// vB.
Qed.

Lemma F_zero_or_pos : (forall x, U x -> F x = 0) \/
  (exists z, U z /\ forall x, U x -> 0 < F x).
Proof.
have [[z [Uz Fz0]]|nex] := pselect (exists z, U z /\ 0 < F z).
  right; exists z; split=> // x Ux; rewrite lt_neqAle F_ge0 andbT; apply/eqP => Fx0.
  exact: (F_dichotomy Ux Uz (esym Fx0) Fz0).
left=> x Ux; apply/eqP; rewrite eq_le F_ge0 andbT leNgt; apply/negP => Fx0.
by apply: nex; exists x.
Qed.

(* if F vanishes on U then f vanishes on the whole domain *)
Lemma f_zero_dom : (forall x, U x -> F x = 0) ->
  forall x, 0 < x -> (x%:E < e)%E -> f x = 0.
Proof.
move=> FU x x0 xe; rewrite (fE a0 x0 xe).
have [Ix|Ix] := pselect (I x < +oo)%E; first by rewrite FU ?mul0r ?mul0r.
have Ix' : I x = +oo%E by apply/eqP; rewrite -leye_eq leNgt; apply/negP.
by rewrite F_pinfty// mul0r mul0r.
Qed.

Section ClosedForm.
Hypothesis Fpos : forall x, U x -> 0 < F x.
Variable z : R.
Hypothesis Uz : U z.
Let C := (F z)^-1 - (a * z)^-1.
Let c := - (a * C).

Lemma invF x : U x -> (F x)^-1 = (a * x)^-1 + C.
Proof.
move=> Ux; have [x0 [xe Ix]] := Ux; have [z0 [ze Iz]] := Uz.
have [xz|zx|xz] := ltgtP x z; last by rewrite xz /C; lra.
- have Fp t : x <= t <= z -> 0 < F t.
    by move=> /andP[xt tz]; apply: Fpos; exact: U_down Uz (lt_le_trans x0 xt) tz.
  have := ode_identity a0 Uz x0 xz Fp; rewrite !invfM /C; lra.
- have Fp t : z <= t <= x -> 0 < F t.
    by move=> /andP[zt tx]; apply: Fpos; exact: U_down Ux (lt_le_trans z0 zt) tx.
  have := ode_identity a0 Ux z0 zx Fp; rewrite !invfM /C; lra.
Qed.

Lemma onemcx x : U x -> 1 - c * x = a * x * (F x)^-1.
Proof.
move=> Ux; have [x0 _] := Ux; rewrite invF// mulrDr mulfV ?mulf_neq0 ?gt_eqF//.
by rewrite /c; lra.
Qed.

Lemma onemcx_pos x : U x -> 0 < 1 - c * x.
Proof. by move=> Ux; have [x0 _] := Ux; rewrite onemcx// mulr_gt0 ?mulr_gt0// invr_gt0 Fpos. Qed.

Lemma F_closed x : U x -> F x = a * x / (1 - c * x).
Proof.
move=> Ux; have [x0 _] := Ux; have Fx0 : F x != 0 by rewrite gt_eqF// Fpos.
by rewrite onemcx// invfM invrK mulrA mulfV ?mul1r// mulf_neq0// gt_eqF.
Qed.

Lemma f_closed x : U x -> f x = a / ((1 - c * x) * (1 - c * x)).
Proof.
move=> Ux; have [x0 [xe _]] := Ux; have q0 : 1 - c * x != 0 by rewrite gt_eqF// onemcx_pos.
have ax0 : a * (x * x) != 0 by exact: axx_neq0.
rewrite (fE a0 x0 xe) F_closed// mulf_div mulrAC.
rewrite (_ : a * x * (a * x) = a * (a * (x * x))); last by rewrite -mulrA [x * (a * x)]mulrCA.
by rewrite mulfK.
Qed.

(* the set U is exactly the part of the domain where 1 - c x > 0 *)
Lemma U_of_pos x : 0 < x -> (x%:E < e)%E -> 0 < 1 - c * x -> U x.
Proof.
move=> x0 xe cx; split=> //; split=> //.
rewrite ltNge; apply/negP => Ix.
have Ix' : I x = +oo%E by apply/eqP; rewrite -leye_eq.
pose qx := 1 - c * x.
pose M := a + a / (qx * qx).
have M0 : 0 <= M by rewrite addr_ge0 ?(ltW a0)// divr_ge0 ?(ltW a0)// mulr_ge0// ltW.
(* f is bounded by M on [0, x] *)
have fM u : 0 <= u <= x -> f u <= M.
  move=> /andP[u0 ux]; move: u0; rewrite le_eqVlt => /orP[/eqP <-|u0].
    by rewrite -/a lerDl divr_ge0 ?(ltW a0)// mulr_ge0// ltW.
  have ue : (u%:E < e)%E by apply: le_lt_trans xe; rewrite lee_fin.
  have [Uu|nUu] := pselect (U u).
    rewrite f_closed//; have q0 := onemcx_pos Uu.
    have [c0|c0] := boolP (0 <= c).
      (* c >= 0: 1 - c u >= 1 - c x = qx *)
      have qq : qx <= 1 - c * u by rewrite /qx lerD2l lerN2 ler_wpM2l.
      by apply: ler_wpDl (ltW a0) _; rewrite ler_wpM2l ?(ltW a0)// lef_pV2 ?posrE ?mulr_gt0// ler_pM// ltW.
    (* c < 0: 1 - c u >= 1 *)
    rewrite -ltNge in c0.
    have q1 : 1 <= 1 - c * u by nra.
    apply: ler_wpDr; first by rewrite divr_ge0 ?(ltW a0)// mulr_ge0// ltW.
    by rewrite ler_pdivrMr ?mulr_gt0// ler_peMr ?(ltW a0)// mulr_ege1.
  (* u not in U: I u = +oo, so F u = 0 and f u = 0 *)
  have Iu : I u = +oo%E.
    by apply/eqP; rewrite -leye_eq leNgt; apply/negP => Iu; apply: nUu; split.
  by rewrite (fE a0 u0 ue) F_pinfty// mul0r mul0r.
have : (I x <= \int[mu]_(t in `[0%R, x]%classic) (cst M%:E) t)%E.
  apply: ge0_le_integral_nm => t; rewrite ?lee_fin//.
  by rewrite /= in_itv/= => /andP[t0 tx]; rewrite fM// t0 tx.
rewrite integral_cst; last exact: measurable_itv.
rewrite Ix' leye_eq /mu/= lebesgue_measure_itv/= lte_fin x0 -EFinD -EFinM.
by move/eqP.
Qed.

End ClosedForm.

End Pos.

(* ------------------------------------------------------------------ *)
(* Part 7: on [0, e), f coincides with a member of the solution set.    *)
(* ------------------------------------------------------------------ *)

(* a positive real below e, used as the "e" of the fourth family *)
Variable r : R.
Hypothesis r0 : 0 < r.
Hypothesis re : (r%:E <= e)%E.

Lemma sq_form (q : R) : a / (q * q) = a / q ^ 2.
Proof. by rewrite -expr2. Qed.

Lemma complete : exists g, g \in putnam_1962_a2_solution /\
  forall x, 0 <= x -> (x%:E < e)%E -> f x = g x.
Proof.
have [a0|a0] := eqVneq a 0.
- (* a = 0: f itself belongs to the fourth family *)
  exists f; split=> //; rewrite inE/=; right; right; right.
  exists r; split=> //; split=> //; split=> // x /andP[x0 xr]; rewrite set_cc.
  have xe : (x%:E < e)%E by apply: lt_le_trans re; rewrite lte_fin.
  have := hP x0 xe; rewrite -/a a0 mul0r sqrtr0 => /eqP.
  by rewrite mulf_eq0 div1r invr_eq0 gt_eqF//= => /eqP.
- have a0' : 0 < a by rewrite lt_neqAle eq_sym a0 f_ge0.
  have [FU|[z [Uz Fpos]]] := F_zero_or_pos a0'.
  + (* F = 0 on U: f vanishes on (0, e), third family *)
    exists (fun x => if 0 < x then 0 else f x); split.
      rewrite inE/=; right; right; left; split=> [x|x x0]; last by rewrite x0.
      by case: ifP => // _; exact: f_ge0.
    move=> x x0 xe; case: ifPn => // x0'.
    exact: (f_zero_dom a0' FU).
  + (* F > 0 on U: the closed form, first or second family *)
    pose c := - (a * ((F z)^-1 - (a * z)^-1)).
    have [c0|c0] := leP c 0.
    * exists (fun x => a / (1 - c * x) ^ 2); split.
        by rewrite inE/=; left; exists a, c; split=> //; exact: ltW.
      move=> x; rewrite le_eqVlt => /orP[/eqP <-|x0] xe.
        by rewrite mulr0 subr0 exp1rz divr1.
      have cx : 0 < 1 - c * x.
        by rewrite subr_gt0 (le_lt_trans _ ltr01)// mulr_le0_ge0// ltW.
      by rewrite (f_closed a0' Fpos Uz (U_of_pos a0' Fpos Uz x0 xe cx)) sq_form.
    * exists (fun x => if x < 1 / c then a / (1 - c * x) ^ 2 else 0); split.
        by rewrite inE/=; right; left; exists a, c; split=> //; exact: ltW.
      move=> x; rewrite le_eqVlt => /orP[/eqP <-|x0] xe.
        by rewrite div1r invr_gt0 c0 mulr0 subr0 exp1rz divr1.
      case: ifPn => [xc|xc].
        have cx : 0 < 1 - c * x.
          by rewrite subr_gt0 mulrC; move: xc; rewrite ltr_pdivlMr.
        by rewrite (f_closed a0' Fpos Uz (U_of_pos a0' Fpos Uz x0 xe cx)) sq_form.
      (* x >= 1 / c: the integral is infinite, so F x = 0 and f x = 0 *)
      rewrite -leNgt in xc.
      have nUx : ~ U x.
        move=> Ux; have := onemcx_pos a0' Fpos Uz Ux.
        by rewrite subr_gt0 mulrC -(ltr_pdivlMr x 1 c0) ltNge xc.
      have Ix : I x = +oo%E.
        by apply/eqP; rewrite -leye_eq leNgt; apply/negP => Ix; apply: nUx; split.
      by rewrite (fE a0' x0 xe) (F_pinfty Ix) mul0r mul0r.
Qed.

End Core.

(* ------------------------------------------------------------------ *)
(* Part 8: the members of the solution set satisfy the condition.       *)
(* ------------------------------------------------------------------ *)
Section Families.

(* the function a / (1 - c t)^2 and its primitive a t / (1 - c t) *)
Variables (a c : R).
Hypothesis a_ge0 : 0 <= a.
Let h (t : R) : R := a / (1 - c * t) ^ 2.
Let H (t : R) : R := a * t / (1 - c * t).

Lemma h_ge0 t : 0 <= h t.
Proof. by rewrite /h divr_ge0//; exact: sqr_ge0. Qed.

Lemma dH t : 1 - c * t != 0 -> is_derive t 1 H (h t).
Proof.
move=> ct0.
apply: (is_derive_eq (is_deriveM (is_deriveZ a (is_derive_id t 1))
  (is_deriveV _ (is_deriveB (is_derive_cst (1 : R) t 1) (is_deriveZ c (is_derive_id t 1)))))).
  exact: ct0.
rewrite /GRing.scale/= /h -[a *: t]/(a * t) (_ : (cst 1 - c \*: id) t = 1 - c * t)//.
by field; rewrite ?ct0.
Qed.

Lemma cont_H t : 1 - c * t != 0 -> {for t, continuous H}.
Proof.
move=> ct0; apply/differentiable_continuous/derivable1_diffP.
by case: (dH ct0).
Qed.

Lemma cont_lin t : {for t, continuous (fun s : R => 1 - c * s)}.
Proof.
apply: continuous_sub'; first exact: continuous_cst'.
by apply: continuous_mul'; [exact: continuous_cst' | exact: continuous_id'].
Qed.

Lemma cont_sq t : {for t, continuous (fun s : R => (1 - c * s) ^ 2)}.
Proof. exact: (continuous_mul' (@cont_lin t) (@cont_lin t)). Qed.

Lemma cont_h t : 1 - c * t != 0 -> {for t, continuous h}.
Proof.
move=> ct0; rewrite /h; apply: continuous_mul'; first exact: continuous_cst'.
apply: continuous_inv'; last exact: cont_sq.
by apply: expf_neq0.
Qed.

(* 1 - c t stays positive on [0, x] when it is positive at x *)
Lemma pos_on_segment x t : 0 < 1 - c * x -> 0 <= t <= x -> 0 < 1 - c * t.
Proof.
move=> cx /andP[t0 tx]; have [c0|c0] := boolP (0 <= c).
  by apply: lt_le_trans cx _; rewrite lerD2l lerN2 ler_wpM2l.
rewrite -ltNge in c0; rewrite subr_gt0 (le_lt_trans _ ltr01)// mulr_le0_ge0//.
exact: ltW.
Qed.

(* the integral of h over [0, x] *)
Lemma int_h x : 0 < x -> 0 < 1 - c * x -> \int[mu]_(t in `[0, x]) h t = a * x / (1 - c * x).
Proof.
move=> x0 cx.
have pos t : t \in `[0, x]%R -> 1 - c * t != 0.
  by move=> tx; rewrite gt_eqF// (pos_on_segment cx)//; move: tx; rewrite in_itv.
have posoo t : t \in `]0, x[%R -> 1 - c * t != 0.
  by move=> tx; apply: pos; move: tx; rewrite !in_itv/= => /andP[/ltW -> /ltW ->].
have -> : \int[mu]_(t in `[0, x]) h t = fine ((H x)%:E - (H 0)%:E).
  rewrite /Rintegral; congr fine; apply: FTC2_here => //.
  - by move=> t tx; apply: cont_h; exact: pos.
  - by move=> t tx; case: (dH (posoo t tx)).
  - by apply: cvg_at_right_filter; apply: cont_H; apply: pos; rewrite in_itv/= lexx ltW.
  - by apply: cvg_at_left_filter; apply: cont_H; apply: pos; rewrite in_itv/= lexx ltW.
  - by move=> t tx; rewrite derive1E; case: (dH (posoo t tx)) => _ ->.
by rewrite /H mulr0 mul0r -EFinB/= subr0.
Qed.

(* the condition holds for h at every x > 0 with 1 - c x > 0 *)
Lemma cond_h x : 0 < x -> 0 < 1 - c * x ->
  1 / x * \int[mu]_(t in `[0, x]) h t = Num.sqrt (h 0 * h x).
Proof.
move=> x0 cx; rewrite int_h// /h mulr0 subr0 exp1rz divr1.
have q0 : 1 - c * x != 0 by rewrite gt_eqF.
rewrite (_ : a * (a / (1 - c * x) ^ 2) = (a / (1 - c * x)) ^+ 2); last by field; rewrite ?q0.
rewrite sqrtr_sqr ger0_norm ?divr_ge0 ?(ltW cx)//.
by field; rewrite ?(gt_eqF cx) ?(gt_eqF x0).
Qed.

End Families.

(* ------------------------------------------------------------------ *)
(* Part 9: one more integral computation.                              *)
(* ------------------------------------------------------------------ *)

(* a nonnegative function vanishing on (0, +oo) has zero integral over [0, x] *)
Lemma int_zero_oc (g : R -> R) : (forall t, 0 <= g t) -> (forall t, 0 < t -> g t = 0) ->
  forall x, 0 < x -> \int[mu]_(t in `[0, x]) g t = 0.
Proof.
move=> g_ge0 g0 x x0; rewrite /Rintegral.
have -> : `[0, x] = [set 0] `|` `]0, x] :> set R.
  apply/seteqP; split => t /=; rewrite !in_itv/= ?andbT.
  - by move=> /andP[]; rewrite le_eqVlt => /orP[/eqP <- _|-> ->]; [left | right].
  - by move=> [-> |/andP[/ltW -> ->]]; rewrite ?lexx ?ltW.
rewrite ge0_integral_setU//; first last.
- rewrite disj_set2E; apply/eqP/seteqP; split => t //= [->].
  by rewrite in_itv/= ltxx.
- by move=> t _; rewrite lee_fin.
- apply/measurable_funU; [exact: measurable_set1 | exact: measurable_itv | split].
    by apply/measurable_EFinP; exact: measurable_fun_set1'.
  apply/measurable_EFinP; apply: (@eq_measurable_fun _ _ _ _ _ (cst 0 : R -> R)) => //.
  by move=> t; rewrite inE/= in_itv/= => /andP[t0 _]; rewrite g0.
rewrite integral_set1 add0e integral0_eq//.
by move=> t; rewrite /= in_itv/= => /andP[t0 _]; rewrite g0.
Qed.

Theorem putnam_1962_a2
    (P : (set R) -> (R -> R) -> Prop)
    (P_def : forall s f, P s f <-> ((forall x, f x >= 0) /\ forall x, x \in s -> 
                1/x * \int[mu]_(t in [set t | 0 <= t <= x]) f t = Num.sqrt (f 0 * f x)))
    : (forall f,
        (P [set t | 0 < t] f -> exists g, g \in putnam_1962_a2_solution /\ (forall x : R, x > 0 -> f x = g x)) /\
        (forall e, 0 < e -> P [set t | 0 < t < e] f -> exists g, g \in putnam_1962_a2_solution /\ (forall x : R, 0 <= x < e -> f x = g x))) /\
        forall f, f \in putnam_1962_a2_solution -> P [set t | 0 < t] f \/ exists e, 0 < e /\ P [set t | 0 < t < e] f.
Proof.
split.
  move=> f; split.
    (* the condition on (0, +oo) *)
    move=> /P_def[f_ge0 hP].
    have hP' x : 0 < x -> (x%:E < +oo)%E ->
        1 / x * \int[mu]_(t in `[0, x]) f t = Num.sqrt (f 0 * f x).
      by move=> x0 _; rewrite -set_cc; apply: hP; rewrite in_setE.
    have [g [gsol fg]] := complete f_ge0 hP' ltr01 (leey 1%:E).
    by exists g; split=> // x x0; apply: fg (ltW x0) _; exact: ltry.
  (* the condition on (0, e) *)
  move=> e e0 /P_def[f_ge0 hP].
  have hP' x : 0 < x -> (x%:E < e%:E)%E ->
      1 / x * \int[mu]_(t in `[0, x]) f t = Num.sqrt (f 0 * f x).
    by move=> x0 xe; rewrite -set_cc; apply: hP; rewrite in_setE/= x0 -lte_fin.
  have [g [gsol fg]] := complete f_ge0 hP' e0 (lexx e%:E).
  by exists g; split=> // x /andP[x0 xe]; apply: fg => //; rewrite lte_fin.
(* every member of the solution set satisfies the condition on (0, +oo) or on some (0, e) *)
move=> g; rewrite inE/= => -[[a [c [a0 ->]]]|[[a [c [a0 [c0 ->]]]]|[[g0 gz]|[e [e0 [g00 [g0 gI]]]]]]].
- (* first family: on (0, +oo) if c <= 0, on (0, 1/c) if c > 0 *)
  have [c0|c0] := leP c 0.
    left; apply/P_def; split=> [x|x]; first exact: h_ge0.
    rewrite in_setE/= => x0; rewrite set_cc; apply: cond_h => //.
    by rewrite subr_gt0 (le_lt_trans _ ltr01)// mulr_le0_ge0// ltW.
  right; exists (1 / c); split; first by rewrite div1r invr_gt0.
  apply/P_def; split=> [x|x]; first exact: h_ge0.
  rewrite in_setE/= => /andP[x0 xc]; rewrite set_cc; apply: cond_h => //.
  by rewrite subr_gt0 mulrC; move: xc; rewrite ltr_pdivlMr.
- (* second family: on (0, 1/c), where it coincides with the first *)
  right; exists (1 / c); split; first by rewrite div1r invr_gt0.
  have c0' : 0 < 1 / c by rewrite div1r invr_gt0.
  apply/P_def; split=> [x|x]; first by case: ifP => // _; exact: h_ge0.
  rewrite in_setE/= => /andP[x0 xc]; rewrite set_cc.
  rewrite (eq_Rintegral mu (g := fun t => a / (1 - c * t) ^ 2)); last first.
    move=> t; rewrite inE/= in_itv/= => /andP[t0 tx].
    by rewrite (le_lt_trans tx xc).
  rewrite c0' xc; apply: cond_h => //.
  by rewrite subr_gt0 mulrC; move: xc; rewrite ltr_pdivlMr.
- (* third family: the integral vanishes, and so does g x *)
  left; apply/P_def; split=> // x; rewrite in_setE/= => x0.
  by rewrite set_cc int_zero_oc// (gz x x0) !mulr0 sqrtr0.
- (* fourth family: g 0 = 0 and the integral vanishes on (0, e) *)
  right; exists e; split=> //; apply/P_def; split=> // x.
  by rewrite in_setE/= => xe; rewrite gI// g00 mul0r sqrtr0 mulr0.
Qed.

Print Assumptions putnam_1962_a2.
