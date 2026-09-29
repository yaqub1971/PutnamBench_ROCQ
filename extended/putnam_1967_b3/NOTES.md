# putnam_1967_b3 -- notes

Audit verdict: **compile** (the `-->` is applied to a bare sequence; the missing `@ \oo`
is the whole fix; the statement is otherwise faithful). Upstream commit
4dbe26ef21563af851eedaeb82d936fe1f94fc52 of PutnamBench, file `coq/src/putnam_1967_b3.v`.

## 1. The problem

Putnam 1967 B3. If f and g are continuous and periodic functions with period 1 on the
real line, then lim_{n -> oo} int_0^1 f(x) g(nx) dx = (int_0^1 f(x) dx)(int_0^1 g(x) dx).
(The informal file gives no solution. The standard argument: split [0, 1] into the n
intervals [k/n, (k+1)/n], on each of which g(nx) runs through one full period while f
is almost constant, so the integral is a Riemann sum of f times int_0^1 g, up to an error
controlled by the modulus of continuity of f.)

## 2. Defect(s) in the upstream statement

The upstream file (kept verbatim, after a header comment, in `putnam_1967_b3.v`) is

```coq
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals normedtype trigo measure lebesgue_measure lebesgue_integral topology.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Variable R : realType.
Definition mu := [the measure _ _ of @lebesgue_measure R].
Theorem putnam_1967_b3
    (f g : R -> R)
    (fgcont : continuous f /\ continuous g)
    (fgperiod : periodic f 1 /\ periodic g 1)
    : (fun n : nat => \int[mu]_(x in [set y | 0 < y < 1]) (f x * g (n%:~R * x))) --> 
        (\int[mu]_(x in [set y | 0 < y < 1]) f x) * (\int[mu]_(x in [set y | 0 < y < 1]) g x).
Proof. Admitted.
```

**Defect (the audited one): it does not compile.** `F --> l` is `cvg_to (nbhs F) (nbhs l)`:
its left side must be a filter (or a point of a filtered type). Upstream puts the
sequence itself, a function `nat -> R`, there; MathComp-Analysis' notation for "the
limit of the sequence u as n -> oo" is `u @ \oo --> l` (the image of the filter
`\oo = eventually` on `nat` under `u`), and the `@ \oo` is missing. Error, identical on
both toolchains (Coq 8.18.0: upstream line 19, characters 7-79; Rocq 9.1.1: same place,
reached once the `Variable` line is accepted, see below):

```
The term
 "fun n : nat => \int[mu]_(x in [set y | 0 < y < 1]) (f x * g (n%:~R * x))"
has type "nat -> R" while it is expected to have type
"Filtered.sort ?s".
```

The audit table's other `-->` compile rows (1966 A3, 1966 A6, 1969 B3, 1978 B2, 2015 B4)
concern the *target* of `-->` (a bare numeral or `ratr` without a type); this row is the
only one where the *source* side is at fault (the missing `@ \oo`).

**Rocq 9.1 / MathComp 2.5 compatibility (not a mathematical defect):** on Rocq 9.1.1 the
upstream file stops even earlier, at `Variable R : realType.` outside a `Section`
("Use of "Variable" or "Hypothesis" outside sections behaves as "#[local] Parameter" or
"#[local] Axiom"", `declaration-outside-section`, an error since Rocq 9.0; Coq 8.18 only
emits the `local-declaration` warning there). The corrected file carries the
repository's marked compat line for it.

**Re-reading the whole statement against the trap list of the brief (section 7.5):** no
further defect.

* Limit: with the fix, `u @ \oo --> l` unfolds (by `reflexivity`, check 4.3) to
  `cvg_to (fmap u eventually) (nbhs l)` with `l : R`: ordinary convergence of the real
  sequence to a real limit, not a `+oo`-admitting notion (no `ex_lim_seq` issue).
* Index range: `n : nat` runs through 0, 1, 2, ...; the limit does not depend on
  finitely many terms, so including n = 0 is harmless. PutnamBench's Lean statement uses
  `n : ℤ` with `atTop`, which is the same limit.
* Integrals: in `ring_scope`, `\int[mu]_(x in D) h x` is `Rintegral mu D h = fine
  (\int[mu]_(x in D) (h x)%:E)` (checked under `Set Printing All`: the elaborated term is
  `lebesgue_Rintegral.Rintegral ... mu (mkset (fun y => 0 < y < 1)) ...` on Rocq 9.1, and
  `Rintegral` is defined as that `fine (...)` in both MathComp-Analysis 1.0.0 and 1.16.0).
  `mu` is Lebesgue measure. The domain `[set y | 0 < y < 1]` is the open interval (0, 1);
  it differs from [0, 1] by a null set, so it is int_0^1. The integrands `f`, `g` and
  `x |-> f x * g (n x)` are continuous, hence bounded and integrable on (0, 1), so
  `Rintegral` is the true integral (the "`fine` of an infinite integral is 0" trap
  cannot occur). The integration variable is the bound variable `x`, not `n`.
* `n%:~R * x` is the real number n x (`%:~R` is the `int -> R` cast; the elaborated term
  is `intmul 1 (Posz n) * x`); no `nat` division, no `pow`/`^`, no `Rpower`/`ln`, no
  `exprz`, no `Series`/`sum_n`, no `sup`, no `Q`, no divisibility.
* `periodic f 1` is `trigo.periodic`, defined in both MathComp-Analysis versions as
  `forall u, f (u + T) = f u` with `T = 1`: period 1 as in the problem (1 need not be the
  least period, and the problem does not ask that). `continuous f` for `f : R -> R` is
  `forall x, continuous_at x f` (visible in the `Set Printing All` output): continuity
  on the whole real line.
* `1`, `0`, `<` are the ring/order notations of `R` (`GRing.one`, `Algebra.zero`,
  `Order.lt` in the elaborated term), not `nat` ones.
* Hypotheses: exactly the problem's (continuity and period 1 of f and g); none missing,
  none extra, none of the `(h : Prop := ...)` kind; no existential scoping over an iff.
* Theorem name matches the problem (no `naming` issue); there is no `_solution`.

## 3. The fix

`putnam_1967_b3_corrected.v` differs from the upstream text in exactly one statement line
(`@ \oo` inserted), plus the marked compat lines:

```diff
 From mathcomp Require Import reals normedtype trigo measure lebesgue_measure lebesgue_integral topology.
+Set Warnings "-notation-overridden". (* compat: ... *)
+From mathcomp Require Import ssralg. (* compat: ... *)
+Set Warnings "notation-overridden". (* compat: restore the default. *)
 From mathcomp Require Import classical_sets.
 ...
+Set Warnings "-declaration-outside-section,-local-declaration". (* compat: ... *)
 Variable R : realType.
 ...
-    : (fun n : nat => \int[mu]_(x in [set y | 0 < y < 1]) (f x * g (n%:~R * x))) --> 
+    : (fun n : nat => \int[mu]_(x in [set y | 0 < y < 1]) (f x * g (n%:~R * x))) @ \oo --> 
```

(The trailing space that upstream has after `-->` is kept. The compat lines are copied
byte-for-byte from the root file `putnam_1962_a2_corrected.v`, checked by matching each
line against that file.)

Compat lines: kind (2) (before `Variable R : realType.`) is required on Rocq >= 9.0.
Kind (1) (the bracketed `ssralg` re-import, placed after the second import line and
before `From mathcomp Require Import classical_sets.`, as in the root A2 files) is added
because the statement uses the ring notations `1`, `0`, `%:~R` (the brief's criterion).
This file's upstream import order is `all_ssreflect all_algebra` (the reverse of the root
files), so the re-import is in fact a no-op even on MathComp 2.5: the theorem's type and
`mu` print identically under `Set Printing All` with and without it (check 4.2). It is
kept for uniformity with the repository. Kind (3) (derivative notations) does not apply.

Why the corrected statement is faithful: `@ \oo` only supplies the filter "n -> oo"
along which the limit is taken; the conclusion becomes "int_0^1 f(x) g(nx) dx tends to
(int_0^1 f)(int_0^1 g) as n -> oo", which is the problem's claim. Everything else is
upstream's text, already faithful (section 2). Nothing is weakened, no hypothesis is
added or dropped.

Comparison with the Lean statement (`putnam_1967_b3.lean`):

```lean
theorem putnam_1967_b3
(f g : ℝ → ℝ)
(fgcont : Continuous f ∧ Continuous g)
(fgperiod : Function.Periodic f 1 ∧ Function.Periodic g 1)
: Tendsto (fun n : ℤ => ∫ x in Set.Ioo 0 1, f x * g (n * x)) atTop (𝓝 ((∫ x in Set.Ioo 0 1, f x) * (∫ x in Set.Ioo 0 1, g x)))
```

The corrected Rocq statement matches it hypothesis by hypothesis (`Continuous` =
`continuous`, `Function.Periodic f 1` = `periodic f 1` = `forall u, f (u + 1) = f u`,
`Set.Ioo 0 1` = `[set y | 0 < y < 1]`, Lebesgue integral in both). The only deviation is
the index type: Lean's `n : ℤ` with `atTop` versus upstream's `n : nat` with `\oo`,
which I kept (minimal diff); both are the limit as n -> +oo and are equivalent. Both
agree with the informal problem.

## 4. Sanity checks actually run

Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (Nix, `source
/opt/rocq91/bin/rocq-env.sh`) and Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0
(Ubuntu 24.04, plain `coqc`), build products deleted between toolchains. The scratch files
named below (not deliverables) are in the session scratch directory
`.../scratchpad/work/putnam_1967_b3/`.

1. **Compilation of the deliverables.**
   * `rocq compile -R . "" putnam_1967_b3_corrected.v` (Rocq 9.1.1): exit 0, `.vo`
     written; all 27 warnings of the log point at line 45, the upstream
     `From mathcomp Require Import all_ssreflect all_algebra.` line (MathComp's own:
     `all_ssreflect` deprecated, overridden notations, ambiguous coercion paths); none at
     any other line.
   * `coqc -R . "" putnam_1967_b3_corrected.v` (Coq 8.18.0, after deleting the `.vo`
     files): exit 0, `.vo` written; all 23 warnings point at line 45 as well; none
     elsewhere.
   * `putnam_1967_b3.v` (upstream copy): Rocq 9.1.1 exits 1 at line 53 (= upstream
     line 13, `Variable R : realType.`, `declaration-outside-section` error); Coq 8.18.0
     exits 1 at line 59 (= upstream line 19) with the "has type nat -> R while it is
     expected to have type Filtered.sort ?s" error quoted in section 2 (plus the
     `local-declaration` warning at line 53). A scratch copy of the upstream text with
     only the Variable compat line added fails on Rocq 9.1.1 with the same `-->` error,
     so compat lines cannot rescue the upstream copy; it is kept strictly verbatim.
2. **Byte identity and minimal diff.** `tail -n +41 putnam_1967_b3.v | cmp - <upstream>`:
   no difference (the upstream file is 804 bytes, no trailing newline; the files were
   assembled from the upstream bytes by a script, not retyped). `diff` of the upstream
   text against the corrected file's body with the `(* compat: ... *)` lines removed
   shows exactly one changed line, the conclusion line, as in section 3.
   **Elaboration unchanged by the compat lines** (`Set Printing All. Check
   putnam_1967_b3_corrected.putnam_1967_b3. Print putnam_1967_b3_corrected.mu.` in a
   scratch file, output diffed): on Rocq 9.1.1 the final corrected file and a variant
   without the `ssralg` compat block print identically; on Coq 8.18.0 the final
   corrected file and the bare upstream text with only `@ \oo` inserted (no compat line
   at all) print identically (64 KB of output each).
3. **Non-vacuity and a concrete instance** (`s91/sanity.v` and `s818/sanity.v`: the
   corrected file followed by four lemmas; exit 0 on BOTH toolchains, no warnings from
   the added lines):
   * `concl_unfold : (u @ \oo --> l) = cvg_to (fmap u eventually) (nbhs l)` by
     `reflexivity` (the shape of the corrected conclusion).
   * `witness_cst`: constant functions satisfy `fgcont` and `fgperiod` (`cvg_cst`).
   * `witness_cos`: `x |-> cos (2 * pi * x)` is continuous (`continuous_comp`, `cvgM`,
     `continuous_cos`) and `periodic _ 1` (`mulrDr`, `mulr_natl`, `cosD2pi`): the
     hypotheses admit non-constant models, so the theorem is not vacuous.
   * `instance_cst`: the corrected conclusion, instantiated with `f = g = fun _ => c`, is
     PROVED (both sides are c^2: `integral_cst`, `lebesgue_measure_itv` gives
     `mu [set y | 0 < y < 1] = 1%:E`, then `cvg_cst`). This exercises every notation of
     the conclusion (`Rintegral` over `[set y | 0 < y < 1]`, `@ \oo`, `-->`) and shows
     that it means what it should on the simplest instance.
   * `Print Assumptions` of `witness_cos` and `instance_cst` (both toolchains): only
     `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`,
     `boolp.constructive_indefinite_description` and the statement's `R : realType`
     (they do not use the admitted theorem).
4. **Numerical check** (`numeric_check.py`, composite Simpson rule with 200000
   subintervals) with the non-trivial 1-periodic continuous functions
   f(x) = |frac(x) - 1/2| (int f = 1/4) and g(x) = exp(cos 2 pi x) + sin 4 pi x
   (int g = I_0(1) = 1.2660658778): target (int f)(int g) = 0.3165164694;
   I_n - target = 3.6e-1 (n = 0), 1.2e-1 (n = 1), 1.3e-2 (n = 3), 4.6e-3 (n = 5),
   9.5e-4 (n = 11), 4.4e-5 (n = 51), 1.1e-5 (n = 101), 1.1e-7 (n = 1001), and
   < 1e-13 for every even n tested (2, 4, 10, 50, 100, 500: f has only odd harmonics,
   so the even-n integrals equal the target exactly by orthogonality). The sequence is
   not constant and converges to the product of the integrals, as the corrected
   statement asserts.
5. **No model names** in the `.v` files or in this file (grep for the usual names: no hit).
6. No `_statement_is_false` / `_statement_is_vacuous` file: the verdict is `compile`;
   the (corrected) statement is neither false nor vacuous (check 3 exhibits models of
   the hypotheses, check 4 is consistent with the conclusion, and the conclusion is a
   known theorem). `Print Assumptions` of the theorem itself is not applicable in this
   phase (the file ends in `Admitted`).
7. **Verifier**, verdict lines as printed:
   * `(source /opt/rocq91/bin/rocq-env.sh && cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1967_b3)`:
     ```
     toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
     NOTE putnam_1967_b3.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)
     OK   putnam_1967_b3_corrected.v compiles
     OK   putnam_1967_b3_corrected.v ends in Admitted (statement only)
     OK   putnam_1967_b3.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
     checked 1 problem folder(s), 0 with a proof file
     ALL CHECKS PASSED
     ```
   * `(cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1967_b3)`:
     ```
     toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
     NOTE putnam_1967_b3.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)
     OK   putnam_1967_b3_corrected.v compiles
     OK   putnam_1967_b3_corrected.v ends in Admitted (statement only)
     OK   putnam_1967_b3.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
     checked 1 problem folder(s), 0 with a proof file
     ALL CHECKS PASSED
     ```

## 5. Difficulty estimate and proof sketch

**Difficulty: 4 / 5.** The mathematics is short, but a MathComp-Analysis proof needs
splitting a Lebesgue integral over n subintervals, a linear change of variables (or the
fundamental theorem of calculus), uniform continuity of f on a compact interval (not in
the library under the name Heine), and Riemann sums, all with `Rintegral` / `\bar R`
bookkeeping and integrability side conditions.

Mathematical proof. Let w be the modulus of continuity of f on [0, 1] (w(d) -> 0 as
d -> 0 by uniform continuity) and M = sup_{[0,1]} |g| (finite; by periodicity M bounds
|g| everywhere). For n >= 1:

1. int_0^1 f(x) g(nx) dx = sum_{k<n} int_{k/n}^{(k+1)/n} f(x) g(nx) dx.
2. For each k, int_{k/n}^{(k+1)/n} g(nx) dx = (1/n) int_k^{k+1} g = (1/n) int_0^1 g
   (substitution t = nx, then periodicity: int_k^{k+1} g = int_0^1 g).
3. Hence I_n - (1/n) sum_{k<n} f(k/n) int_0^1 g
   = sum_{k<n} int_{k/n}^{(k+1)/n} (f(x) - f(k/n)) g(nx) dx, of absolute value at most
   n * (1/n) * w(1/n) * M = w(1/n) M -> 0.
4. (1/n) sum_{k<n} f(k/n) -> int_0^1 f (left Riemann sums of a continuous function; the
   same estimate: |int_0^1 f - (1/n) sum f(k/n)| <= w(1/n)).
5. So I_n -> (int_0^1 f)(int_0^1 g).

Rocq plan (names checked in the MathComp-Analysis 1.16.0 sources at
`.../scratchpad/src91/analysis`; a proof using `ftc` would compile only on Rocq 9.1, since
MathComp-Analysis 1.0.0 has no `ftc.v`):

* Integrability: `continuous_compact_integrable` (with `segment_compact`) on `` `[0, 1] ``,
  and `integrableS` to pass to `[set y | 0 < y < 1]` (= `` `]0, 1[ `` by `set_itvoo`) and
  to the pieces; measurability of continuous functions by `continuous_measurable_fun`.
* Step 1: `Rintegral_setU` / `integral_bigsetU_EFin` over the disjoint pieces
  `` `[k/n, (k+1)/n[ `` (and `Rintegral_itv_bndo_bndc` / `integral_itv_bndo_bndc` to move
  between open/closed endpoints).
* Step 2: either `integration_by_substitution_increasing` (`ftc.v`) with F x = n x, or
  `continuous_FTC1` / `continuous_FTC2` with the antiderivative G y = int_0^y g
  (then int_a^b g(nx) dx = (G(nb) - G(na))/n), plus `periodicn` (`trigo.v`:
  `f (a + T *+ n) = f a`) to show int_k^{k+1} g = int_0^1 g.
* Step 3: `le_normr_Rintegral`, `le_Rintegral`, `RintegralD`, `RintegralZr` for the
  estimate; M from `EVT_max` (`derive.v`) applied to `|g|` on `` `[0, 1] ``.
* Uniform continuity: derive it from compactness (`segment_compact`, via a finite
  subcover / `near` argument), or use `unif_continuousP` (`pseudometric_structure.v`)
  after establishing `unif_continuous` for the restriction; no ready-made Heine lemma
  was found by grep.
* Step 4-5: turn the eps-estimates into `@ \oo -->` statements (`cvgrPdist_le` /
  `cvgrPdist_lt`-style characterizations, `near` for "n large", `cvg_harmonic`
  (`sequences.v`) for 1/n -> 0), then `cvgM`/`cvgD` to combine.
* Expected `Print Assumptions`: only the statement's `R` and the three `boolp` axioms.

## 6. Status of each file

| file | status |
|---|---|
| `putnam_1967_b3.v` | upstream text verbatim after a header comment (no compat lines: it would not compile with them either). **Does not compile** on Rocq 9.1.1 (first stop: `Variable` outside a Section) nor on Coq 8.18.0 (the missing `@ \oo`), as expected for the `compile` verdict; errors in section 2 / check 4.1. |
| `putnam_1967_b3_corrected.v` | corrected statement (`@ \oo` inserted) + marked compat lines; ends in `Proof. Admitted.`; **compiles** on Rocq 9.1.1 and on Coq 8.18.0 with no warning from its own lines (check 4.1). |
| `putnam_1967_b3_statement_is_false.v` / `_vacuous.v` | not applicable (verdict `compile`; the corrected statement is satisfiable and true). |
| `putnam_1967_b3_corrected_proof.v` | not written in this phase (proofs are out of scope). Sketch in section 5. |
| `NOTES.md` | this file. |
