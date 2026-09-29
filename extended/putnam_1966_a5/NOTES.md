# putnam_1966_a5 -- notes

Audit verdict: **unfaithful** (the statement is trivialized). Files in this folder:
`putnam_1966_a5.v` (upstream copy, evidence), `putnam_1966_a5_corrected.v` (proposed
fix, ends in `Admitted`), this file. No `_statement_is_false` / `_statement_is_vacuous`
file: the upstream statement is neither false nor vacuous, it is *provable for the wrong
reason* (see section 2 for the machine-checked evidence of that, run as a scratch check).

## 1. The problem

Let C be the set of continuous functions f : R -> R and let T : C -> C be
(1) linear, T(a f + b g) = a T(f) + b T(g) for all reals a, b and all f, g in C, and
(2) local: if f, g in C are identical on some interval I, then T(f) and T(g) are
identical on I. Prove that there is a function h in C such that T(g)(x) = h(x) g(x)
for all g in C (and all x). The intended solution: h := T(1); for g in C and a point
x0, split k := g - g(x0) (which vanishes at x0) into k1 := k on [x0, +oo), 0 on
(-oo, x0] and k2 := k on (-oo, x0], 0 on [x0, +oo); both are continuous because
k(x0) = 0, k1 vanishes on the interval (-oo, x0] and k2 on [x0, +oo), so by locality and
T(0) = 0 both T(k1)(x0) and T(k2)(x0) are 0; linearity then gives
T(g)(x0) = g(x0) T(1)(x0). The content of the problem is this pasting argument, which
needs continuity; "interval" means a nondegenerate interval.

## 2. Defect of the upstream statement

Upstream line 19 (verbatim):

```
    (localT : forall r s : R, r <= s -> forall f g : R -> R, f \in C -> g \in C -> (forall x : R, r <= x <= s -> f x = g x) -> (forall x : R, r <= x <= s -> T f x = T g x))
```

Locality is assumed for every closed interval `[r, s]` with `r <= s`, which includes the
degenerate intervals `[x, x]`. Taken with `r = s = x`, `localT` says that `T f x` depends
only on the single value `f x`. Together with `linearT` this gives the conclusion at
once, with no continuity argument at all: for every `x`, `g` agrees at `x` with the
constant function `fun _ => g x * 1 + 0 * 1`, so
`T g x = T (fun _ => g x * 1 + 0 * 1) x = g x * T 1 x + 0 * T 1 x = g x * T 1 x`,
where `1` is the constant function 1 and `T 1 \in C` by `imageTC`. The upstream theorem
is therefore provable in a few lines. This was machine-checked (scratch file
`upstream_is_trivial.v`, same preamble as upstream plus `From mathcomp Require Import
boolp.` and `Import GRing.Theory Num.Theory Order.Theory.`, `R` a `Section` variable; the
theorem is the upstream statement verbatim):

```coq
Proof.
have one_C : (fun _ : R => 1) \in C by rewrite in_setE /C /=; exact: cst_continuous.
exists (T (fun _ => 1)); split; first exact: imageTC.
move=> g gC; apply/funext => x.
have gx_C : (fun _ : R => g x * 1 + 0 * 1) \in C.
  by rewrite in_setE /C /=; exact: cst_continuous.
have -> : T g x = T (fun _ => g x * 1 + 0 * 1) x.
  apply: (localT x x (lexx x) _ _ gC gx_C); last by rewrite lexx.
  by move=> y /le_anti <-; rewrite mulr1 mul0r addr0.
by rewrite (linearT (g x) 0 _ _ one_C one_C) mul0r addr0 mulrC.
Qed.
```

`coqc` exit status 0; `Print Assumptions` lists exactly `boolp.propositional_extensionality`,
`boolp.functional_extensionality_dep`, `boolp.constructive_indefinite_description` (the
classical axioms of `mathcomp.classical`; nothing else). The only use of `localT` is with
`r = s = x`. So the upstream statement encodes a different, contentless problem: it is
UNFAITHFUL, not false and not vacuous.

PutnamBench's Lean statement has exactly the same hypothesis (`∀ r s : ℝ, r ≤ s → ... Set.Icc r s ...`)
and therefore the same defect.

Other traps checked (section 7.5 of the brief): none found. `\in` on the classical set
`C` is the `in_set` predicate (`in_setE : x \in A = A x`); `continuous f` for
`f : R -> R` is continuity for the standard topology of `R : realType`; the ring
operations are on `R`; `linearT` is an equality of functions (functional
extensionality is available in `mathcomp.classical`); the conclusion is exactly the
problem's ("there exists f in C such that T g = f * g for all g in C"); `T` is a total
function on `R -> R` whose values outside `C` are unconstrained and irrelevant, which is
the usual and harmless encoding of `T : C -> C`. No numerals, exponents, sums, integrals,
`nat` arithmetic or indexing occur.

## 3. The fix and why it is faithful

Exactly one line of the statement changes (the diff of the two files with header
comments and marked compat lines removed is this one line):

```
-    (localT : forall r s : R, r <= s -> forall f g : R -> R, f \in C -> g \in C -> (forall x : R, r <= x <= s -> f x = g x) -> (forall x : R, r <= x <= s -> T f x = T g x))
+    (localT : forall r s : R, r < s -> forall f g : R -> R, f \in C -> g \in C -> (forall x : R, r <= x <= s -> f x = g x) -> (forall x : R, r <= x <= s -> T f x = T g x))
```

Locality is now assumed only for nondegenerate closed intervals `[r, s]`, `r < s`.

* This is the problem's hypothesis. The problem says "identical on some interval I";
  intervals of a problem of this kind are nondegenerate (with degenerate intervals the
  problem is trivial, section 2). Quantifying over nondegenerate *closed* intervals is
  equivalent to quantifying over all nondegenerate intervals: if f = g on an arbitrary
  nondegenerate interval I (open, half-open, closed, bounded or not), then for every
  closed `[r, s] ⊆ I` with `r < s` we get `T f = T g` on `[r, s]`, and every point of I
  lies in such a sub-interval, so `T f = T g` on I; conversely a nondegenerate closed
  interval is an interval. So nothing is weakened relative to the informal hypothesis,
  and the degenerate case that trivialized the upstream statement is removed.
* Nothing else changes: same set `C`, same `imageTC`, same `linearT`, same conclusion,
  same library, names, order and style. No hypothesis is added.
* The hypotheses remain satisfiable (section 4, check 3) and the corrected theorem is
  provable by the intended argument (section 4, check 4), which uses locality only on
  the intervals `[x0 - 1, x0]` and `[x0, x0 + 1]`.
* Lean comparison: the Lean statement is otherwise the model of the Rocq one (same
  `C`, `T`, `imageTC`, `linearT`, `localT`, conclusion) but has the same `r ≤ s`; on this
  one point the Lean statement was not followed, since it has the same defect.

Compat lines (both files): kind (1) after the upstream import lines and kind (2)
before `Variable R : realType.`, copied from the root files. Kind (2) is needed: on
this toolchain the upstream `Variable` line itself emits a `local-declaration` warning
(the upstream build log shows it at line 13), which the CI counts as a warning from the
file's own lines, and Rocq >= 9.0 rejects the line. Kind (1) is a precaution: the
statement uses no `1`, `-1` or `%:R` numeral but does use `ring_scope` arithmetic on `R`
(`a * f x + b * g x`, `f x * g x`); the line is a no-op on MathComp <= 2.4 and changes
nothing mathematically. Kind (3) does not apply (no derivative notation).

## 4. Sanity checks run (Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0, Ubuntu 24.04)

1. Compile, `cd /home/user/PutnamBench_ROCQ/extended/putnam_1966_a5 && coqc -R . "" putnam_1966_a5.v`:
   exit 0. The log has 23 warnings, all attached to the first import line
   (`all_algebra all_ssreflect`; ambiguous coercion paths and overridden notations
   emitted by MathComp), none from any other line; in particular the `Variable` line no
   longer warns (compat line of kind (2)) and the compat re-import of `ssralg` is silent.
2. Compile, `coqc -R . "" putnam_1966_a5_corrected.v`: exit 0, same 23 library warnings
   at the first import line, none from the file's own lines.
3. Statement integrity, with the CI's `strip` (drop the header comment and the marked
   compat lines): the upstream copy is byte-identical to
   `scratchpad/upstream/coq/putnam_1966_a5.v` (`diff` empty); the corrected file differs
   from upstream in exactly one line (diff shows 2 changed lines = the `localT` line).
4. Upstream statement is trivially provable: scratch file `upstream_is_trivial.v`
   (section 2), exit 0, `Print Assumptions`: only the three `boolp` axioms.
5. Corrected hypotheses are satisfiable (non-vacuity): scratch file `witness.v`, exit 0.
   With `Tw f := fun x => x * f x` the three hypotheses of the corrected statement are
   proved: `Tw_imageTC` (`cvgM` with `cvg_id`), `Tw_linearT` (`mulrDr`, `mulrCA`),
   `Tw_localT` (immediate, for every `r < s`), and the conclusion holds with `h = id`.
   The identity `T f := f` is another witness. The pointwise instance used in check 4 is
   no longer available: `localT x x` would need `x < x`, which is false (`ltxx`).
6. Corrected statement is provable: scratch file `proof_sketch.v`, containing the
   corrected theorem verbatim (inside a `Section` with `Variable R : realType`) and the
   proof of section 5, exit 0, `Print Assumptions`: exactly
   `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`,
   `boolp.constructive_indefinite_description`. This is the intended proof; it is kept
   in the scratch directory only, since the proof file is not part of this phase.
7. `grep -rniE "claude|anthropic|gpt|fable|opus|sonnet|openai|gemini"` on the folder:
   no match.

Not run: Rocq 9.1 / MathComp 2.5 (not available on this machine). The compat lines are
the repository's standard ones.

## 5. Difficulty and proof sketch for `putnam_1966_a5_corrected_proof.v`

Difficulty: **2** (routine given the check 6 script; MathComp-Analysis bookkeeping only,
no real mathematics beyond the pasting argument). About 60 lines of ssreflect.

Extra imports for the proof: `From mathcomp Require Import boolp.` (for `funext`),
`Import GRing.Theory Num.Theory Order.Theory.`, and `Import numFieldNormedType.Exports.`
(needed for `cvgD`, which is stated for a `normedModType`; `cvgM`/`cvgMr` need only a
`numFieldType`).

Strategy (all steps compiled in `proof_sketch.v`):

1. `cst_C c : (fun _ => c) \in C` -- `rewrite in_setE /C /=; exact: cst_continuous`.
2. `lin_C a b f g : f \in C -> g \in C -> (fun x => a * f x + b * g x) \in C` --
   pointwise: `cvgMr` for each summand, then `exact: (cvgD h1 h2)` (conversion unfolds the
   function-ring `+`).
3. `T0x h r s x0 : h \in C -> r < s -> r <= x0 <= s -> (forall x, r <= x <= s -> h x = 0) -> T h x0 = 0`:
   `h` agrees on `[r, s]` with `fun x => 0 * h x + 0 * h x` (in `C` by `lin_C`), so by
   `localT r s` (this is the only use of locality) `T h x0 = T (fun x => 0 * h x + 0 * h x) x0`,
   and `linearT 0 0` makes that `0 * T h x0 + 0 * T h x0 = 0` (`mul0r`, `addr0`). This
   also avoids proving `T 0 = 0` separately.
4. Witness `h := T (fun _ => 1)`, in `C` by `imageTC`. Fix `g \in C`, `apply/funext => x0`.
5. `k := fun x => 1 * g x + (- g x0) * 1` (in `C` by `lin_C`), `k x0 = 0` (`mul1r mulr1 subrr`).
   `k1 := fun x => k (Num.max x x0)`, `k2 := fun x => k (Num.min x x0)`.
   Continuity: `continuous_comp` with `continuous_max` / `continuous_min` (`normedtype`,
   `Section max_cts`, stated for `f g : T -> R^o`; `apply: continuous_max; [exact: cvg_id | exact: cvg_cst]`
   works by unification) composed with the continuity of `k`.
   `k1 = 0` on `[x0 - 1, x0]` (`max_r`, then `k x0 = 0`), `k2 = 0` on `[x0, x0 + 1]` (`min_r`).
   `k = fun x => 1 * k1 x + 1 * k2 x` by `funext` and `case: (leP x x0)` (its spec
   rewrites `Num.max x x0` / `Num.min x x0` in both cases), then `k x0 = 0`, `add0r`/`addr0`.
6. `T k x0 = 0`: rewrite `k` as `1 * k1 + 1 * k2`, `linearT 1 1`, then `T0x` on
   `[x0 - 1, x0]` for `k1` and on `[x0, x0 + 1]` for `k2` (side conditions
   `x0 - 1 < x0`, `x0 - 1 <= x0 <= x0`, `x0 < x0 + 1`, `x0 <= x0 <= x0 + 1` by
   `ltrBlDr ltrDl ltr01`, `lexx andbT lerBlDr lerDl ler01`, `ltrDl ltr01`, `lexx /= lerDl ler01`).
7. `linearT 1 (- g x0) g (fun _ => 1)` evaluated at `x0` (`congr1 (fun F => F x0)`, `exact:`
   by conversion) gives `T k x0 = 1 * T g x0 + (- g x0) * T 1 x0`; with step 6,
   `mul1r mulNr`, `/eqP`, `eq_sym subr_eq0` this is `T g x0 = g x0 * T 1 x0`; finish
   with `mulrC`.

Library facts used: `in_setE`, `cst_continuous`, `cvg_id`, `cvg_cst`, `cvgMr`, `cvgD`,
`continuous_comp`, `continuous_max`, `continuous_min` (MathComp-Analysis); `funext`
(`boolp`); `max_r`, `min_r`, `leP`, `lexx`, `le_anti` (`order`); `mul0r`, `mul1r`,
`mulr1`, `mulNr`, `mulrC`, `add0r`, `addr0`, `subrr`, `subr_eq0`, `ltrBlDr`, `ltrDl`,
`ltr01`, `lerBlDr`, `lerDl`, `ler01`, `andbT` (`ssralg`/`ssrnum`/`ssrbool`). Expected
`Print Assumptions` of the proof file: the statement's `Variable R` and the three
`boolp` axioms.

Portability notes for Rocq 9.1 / MathComp 2.5 / MathComp-Analysis 1.16: all lemma names
above are the post-2.0 MathComp names (`ltrBlDr`, `lerDl`, ...), `Num.max`/`Num.min` are
used rather than the `Def`-module notations `maxr`/`minr`; `continuous_max`/`continuous_min`
and `cvg_cst`/`cvg_id` have existed unchanged in MathComp-Analysis since 0.6.

## 6. Status of the files

| file | status |
|---|---|
| `putnam_1966_a5.v` | upstream statement, byte-identical apart from the header comment and the marked compat lines (checked with the CI strip); ends in `Proof. Admitted.`; compiles, no own-line warnings |
| `putnam_1966_a5_corrected.v` | corrected statement (one line changed: `r <= s` -> `r < s` in `localT`); ends in `Proof. Admitted.`; compiles, no own-line warnings |
| `putnam_1966_a5_statement_is_false.v` / `_vacuous.v` | not applicable (verdict unfaithful: the upstream statement is provable, see section 2 and check 4) |
| `putnam_1966_a5_corrected_proof.v` | not written in this phase; the check 6 script is a complete proof to transplant |
| `NOTES.md` | this file |
