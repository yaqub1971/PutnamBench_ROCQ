(* ============================================================================
   PutnamBench 1962 A4 -- Rocq/MathComp proof.
   Problem: if |f(x)| <= 1 and |f''(x)| <= 1 on an interval of length at least 2,
   then |f'(x)| <= 2 on that interval.
   Statement: coq/src/putnam_1962_a4.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   The Theorem below is byte-identical to upstream; only one line of extra imports
   (boolp, functions, interval, ring, lra: library modules and tactic libraries used
   by the proof), the auxiliary lemmas and the proof script were added.
   Compat lines: the two lines marked "(* compat: ... *)" were added because the
   upstream file does not compile at all on the current toolchain: (1) since
   MathComp-Analysis 1.9.0 the notations f^`() and f^`(2) used by the statement exist
   only in classical_set_scope, which the statement never opens, so it does not parse;
   (2) a Variable outside a Section is an error since Rocq 9.0 (Coq 8.x only warns),
   and the upstream statement declares R this way. Neither changes the meaning of the
   statement.
   Proof idea: the mean value theorem (MathComp-Analysis's MVT) turns a sign
   condition on a derivative into monotonicity; applied twice, this gives the
   second-order bound 2 |f(y) - f(x) - f'(x)(y - x)| <= (y - x)^2 for x, y in [a, b]
   (the auxiliary function G below has G(x) = G'(x) = 0 and G'' <= 0). Writing it
   at the two endpoints c and c + 2 of a subinterval of [a, b] that contains x, and
   using |f| <= 1 there, gives 2 |f'(x)| <= 2 + ((x - c)^2 + (c + 2 - x)^2)/2 <= 4.
   Produced with Claude Fable 5.1 (Anthropic), September 2026; all checks run by the repository author.
   Verified on Rocq 9.1.0 / MathComp 2.5 (Rocq Platform 2026.07, macOS) and Coq 8.18.0 / MathComp 2.1.0 (Ubuntu 24.04):
   compiles; Print Assumptions putnam_1962_a4 lists only R (the Variable declared by
   the statement itself) and the three classical axioms that mathcomp.reals is built on
   (propositional_extensionality, functional_extensionality_dep,
   constructive_indefinite_description) -- nothing from the proof;
   rocqchk / coqchk: "Modules were successfully checked".
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1 / MathComp 2.5 (Rocq Platform 2026.07) the import lines
   below trigger warnings emitted by MathComp itself (all_ssreflect is deprecated
   since 2.5, ambiguous coercion paths, overridden notations). They are library
   warnings, not warnings about this file: none of this file's own lines produce any.
   The import lines are kept exactly as upstream wrote them so that the statement
   stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_ssreflect ssrnum ssralg.
From mathcomp Require Import reals derive normedtype topology sequences.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope. (* compat: since MathComp-Analysis 1.9.0 (Feb. 2025) the derivative notations f^`() and f^`(n) live in classical_set_scope only (they were global when the statement was written), so the statement does not even parse unless that scope is open. Opened before ring_scope so that the ring notations keep precedence; it does not change the meaning of the statement. *)
Local Open Scope ring_scope.

(* Extra imports for the proof (they add nothing to the statement). *)
From mathcomp Require Import boolp functions interval ring lra.
Import GRing.Theory Num.Theory Order.Theory.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.

(* ------------------------------------------------------------------ *)
(* Auxiliary lemmas: the mean value theorem gives monotonicity from    *)
(* the sign of the derivative; applied twice, that gives the           *)
(* second-order (Taylor) bound  2 |f(y) - f(x) - f'(x)(y - x)| <= (y-x)^2 *)
(* when |f''| <= 1.                                                     *)
(* ------------------------------------------------------------------ *)
Section Aux.

Lemma derivable_continuous (F : R -> R) : (forall t, derivable F t 1) -> continuous F.
Proof. by move=> dF t; apply/differentiable_continuous/derivable1_diffP. Qed.

Lemma derive1_is_derive (F : R -> R) (t : R) :
  derivable F t 1 -> is_derive t 1 F (F^`() t).
Proof. by move=> dF; apply: DeriveDef => //; rewrite derive1E. Qed.

(* F' <= 0 on [a, b]  =>  F is nonincreasing on [a, b]  (mean value theorem) *)
Lemma nincr_of_derive_le0 (F : R -> R) (a b : R) :
  (forall t, derivable F t 1) -> (forall t, a <= t <= b -> F^`() t <= 0) ->
  forall x y, a <= x -> x <= y -> y <= b -> F y <= F x.
Proof.
move=> dF F1le0 x y ax xy yb; move: xy; rewrite le_eqVlt => /orP[/eqP <- //|xy].
have [c cxy Fyx] := @MVT _ F F^`() x y xy (fun t _ => derive1_is_derive (dF t))
  (continuous_subspaceT (derivable_continuous dF)).
rewrite -subr_le0 Fyx mulr_le0_ge0 //; last by rewrite subr_ge0 ltW.
apply: F1le0; move: cxy; rewrite in_itv/= => /andP[xc cy].
by rewrite (le_trans ax (ltW xc)) (le_trans (ltW cy) yb).
Qed.

(* F x = 0, F' x = 0 and F'' <= 0 on [a, b]  =>  F <= 0 on [a, b] *)
Lemma concave_le0 (F : R -> R) (a b x : R) :
  (forall t, derivable F t 1) -> (forall t, derivable F^`() t 1) ->
  (forall t, a <= t <= b -> F^`()^`() t <= 0) ->
  a <= x <= b -> F x = 0 -> F^`() x = 0 ->
  forall y, a <= y <= b -> F y <= 0.
Proof.
move=> dF dF1 F2le0 /andP[ax xb] Fx0 F1x0 y /andP[ay yb].
have F1le t : x <= t -> t <= b -> F^`() t <= 0.
  move=> xt tb; rewrite -F1x0.
  apply: (nincr_of_derive_le0 (a := x) (b := b) dF1 _ (lexx x) xt tb) => u /andP[xu ub].
  by apply: F2le0; rewrite (le_trans ax xu) ub.
have F1ge t : a <= t -> t <= x -> 0 <= F^`() t.
  move=> at_ tx; rewrite -F1x0.
  apply: (nincr_of_derive_le0 (a := a) (b := x) dF1 _ at_ tx (lexx x)) => u /andP[au ux].
  by apply: F2le0; rewrite au (le_trans ux xb).
have [xy|yx] := leP x y.
  rewrite -Fx0.
  apply: (nincr_of_derive_le0 (a := x) (b := b) dF _ (lexx x) xy yb) => u /andP[xu ub].
  exact: F1le.
rewrite -Fx0 -lerN2 -[- F y]/((- F) y) -[- F x]/((- F) x).
apply: (nincr_of_derive_le0 (F := - F) (a := a) (b := x) _ _ ay (ltW yx) (lexx x)).
  by move=> t; exact/derivableN/dF.
move=> u /andP[au ux]; rewrite derive1E deriveN; last exact: dF.
by rewrite -derive1E oppr_le0; apply: F1ge.
Qed.

(* The second-order bound. With s = 1 and s = -1 it gives both sides of
   2 |f y - f x - f'(x) (y - x)| <= (y - x)^2 when |f''| <= 1 on [a, b]. *)
Lemma taylor_bound (f : R -> R) (a b s : R) :
  (forall t, derivable f t 1) -> (forall t, derivable f^`() t 1) ->
  (forall t, a <= t <= b -> s * f^`()^`() t <= 1) ->
  forall x y, a <= x <= b -> a <= y <= b ->
  2 * (s * (f y - f x - f^`() x * (y - x))) <= (y - x) ^+ 2.
Proof.
move=> df df1 sf2 x y xab yab.
pose G : R -> R := 2 \*: (s \*: (f - cst (f x) - (f^`() x) \*: (id - cst x)))
                   - (id - cst x) * (id - cst x).
pose G1 : R -> R := 2 \*: (s \*: (f^`() - cst (f^`() x))) - 2 \*: (id - cst x).
have dG (t : R) : is_derive t 1 G (G1 t).
  apply: (is_derive_eq (is_deriveB (is_deriveZ 2 (is_deriveZ s (is_deriveB
    (is_deriveB (derive1_is_derive (df t)) (is_derive_cst (f x) t 1))
    (is_deriveZ (f^`() x) (is_deriveB (is_derive_id t 1) (is_derive_cst x t 1))))))
    (is_deriveM (is_deriveB (is_derive_id t 1) (is_derive_cst x t 1))
                (is_deriveB (is_derive_id t 1) (is_derive_cst x t 1))))).
  by rewrite /G1 /= !fctE /= /GRing.scale /=; ring.
have dG1 (t : R) : is_derive t 1 G1 (2 * (s * f^`()^`() t) - 2).
  apply: (is_derive_eq (is_deriveB (is_deriveZ 2 (is_deriveZ s (is_deriveB
    (derive1_is_derive (df1 t)) (is_derive_cst (f^`() x) t 1))))
    (is_deriveZ 2 (is_deriveB (is_derive_id t 1) (is_derive_cst x t 1))))).
  by rewrite /GRing.scale /=; ring.
have G1E : G^`() = G1.
  by apply/funext => t; rewrite derive1E (@derive_val _ _ _ _ _ _ _ (dG t)).
have dGall (t : R) : derivable G t 1 by exact: (@ex_derive _ _ _ _ _ _ _ (dG t)).
have dG1all (t : R) : derivable G^`() t 1.
  by rewrite G1E; exact: (@ex_derive _ _ _ _ _ _ _ (dG1 t)).
have G2le t : a <= t <= b -> G^`()^`() t <= 0.
  move=> tab; rewrite G1E derive1E (@derive_val _ _ _ _ _ _ _ (dG1 t)).
  by have := sf2 t tab; lra.
have Gx : G x = 0 by rewrite /G !fctE /= /GRing.scale /=; ring.
have G1x : G^`() x = 0 by rewrite G1E /G1 !fctE /= /GRing.scale /=; ring.
have Gy : G y <= 0 := concave_le0 dGall dG1all G2le xab Gx G1x yab.
move: Gy; rewrite /G !fctE /= /GRing.scale /= => Gy.
by rewrite expr2; lra.
Qed.

End Aux.

Theorem putnam_1962_a4
    (f : R -> R)
    (a b : R)
    (hfdiff : forall x : R, differentiable f x /\ differentiable f^`() x)
    (hfabs : forall x : R, (a <= x <= b) -> `| f x | <= 1)
    (hfppabs : forall x : R, (a <= x <= b) -> `| f^`(2) x | <= 1)
    (hlen2 : b - a >= 2)
    : forall x : R, (a <= x <= b) -> `| f^`() x | <= 2.
Proof.
move=> x xab.
have df t : derivable f t 1 by apply/derivable1_diffP; exact: (hfdiff t).1.
have df1 t : derivable f^`() t 1 by apply/derivable1_diffP; exact: (hfdiff t).2.
have f2 t : a <= t <= b -> `| f^`()^`() t | <= 1.
  by move=> tab; have := hfppabs t tab; rewrite derive1nS derive1n1.
(* the second-order bounds at x, for both signs *)
have T1 y : a <= y <= b -> 2 * (f y - f x - f^`() x * (y - x)) <= (y - x) ^+ 2.
  move=> yab; have := taylor_bound (s := 1) df df1 _ xab yab; rewrite mul1r.
  by apply=> t tab; rewrite mul1r; have := f2 t tab; rewrite ler_norml => /andP[].
have T2 y : a <= y <= b -> - (y - x) ^+ 2 <= 2 * (f y - f x - f^`() x * (y - x)).
  move=> yab; have := taylor_bound (s := -1) df df1 _ xab yab.
  rewrite mulN1r mulrN lerNl => h; apply: h.
  by move=> t tab; rewrite mulN1r lerNl; have := f2 t tab; rewrite ler_norml => /andP[].
(* the bound on a subinterval [c, c + 2] of [a, b] containing x *)
have key c : a <= c -> c <= x -> x <= c + 2 -> c + 2 <= b -> `| f^`() x | <= 2.
  move=> ac cx xc2 c2b.
  have cab : a <= c <= b by rewrite ac (le_trans _ c2b) // lerDl.
  have c2ab : a <= c + 2 <= b by rewrite c2b andbT (le_trans ac) // lerDl.
  have := T1 _ cab; have := T2 _ cab; have := T1 _ c2ab; have := T2 _ c2ab.
  have := hfabs _ cab; have := hfabs _ c2ab; rewrite !ler_norml => /andP[? ?] /andP[? ?].
  have sq : (c - x) ^+ 2 + (c + 2 - x) ^+ 2 <= 4.
    have -> : (c - x) ^+ 2 + (c + 2 - x) ^+ 2 = 4 + 2 * ((x - c) * (x - c - 2)) by ring.
    have : (x - c) * (x - c - 2) <= 0.
      by apply: mulr_ge0_le0; rewrite ?subr_ge0 // subr_le0 lerBlDl.
    by lra.
  by move=> h1 h2 h3 h4; apply/andP; split; lra.
have [xb2|b2x] := leP x (b - 2).
  apply: (key x); [exact: (andP xab).1 | exact: lexx | by rewrite lerDl | by rewrite -lerBrDr].
apply: (key (b - 2)); [by rewrite lerBrDr; lra | exact: ltW | by rewrite subrK (andP xab).2 | by rewrite subrK lexx].
Qed.
