# putnam_1994_b3 -- notes

Audit verdict: **naming, compile** (the file defines `putnam_1993_b3` and
`putnam_1993_b3_solution`; it does not compile until `f` is annotated `f : R -> R` in
the set-builder; content faithful). Upstream commit
4dbe26ef21563af851eedaeb82d936fe1f94fc52 of PutnamBench, file `coq/src/putnam_1994_b3.v`.

## 1. The problem

Putnam 1994 B3. Find the set of all real numbers k with the following property: for
any positive, differentiable function f satisfying f'(x) > f(x) for all x, there is some
number N such that f(x) > e^(kx) for all x > N. Answer: the interval (-oo, 1).

## 2. Defect(s) in the upstream statement

The upstream file (kept verbatim, after a header comment, in `putnam_1994_b3.v`) is

```coq
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import reals normedtype derive topology sequences.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Variable R : realType.
Definition putnam_1993_b3_solution : set R := [set k | k < 1].
Theorem putnam_1993_b3
    : [set k | forall f (hf : forall x, differentiable f x /\ 0 < f x < f^`() x),
        exists N : R, forall x, N < x -> expR (k * x) < f x] = putnam_1993_b3_solution.
Proof. Admitted.
```

**Defect 1 (naming).** The theorem and the solution set are named `putnam_1993_b3`
and `putnam_1993_b3_solution`, although the file and the problem are 1994 B3 (Putnam
1993 B3 is an unrelated probability problem).

**Defect 2 (compile).** The binder `forall f (hf : ...)` leaves the type of `f` to
inference. `differentiable f x` makes Rocq type `f` as a map into a normed module, then
`0 < f x` requires `f x` in an ordered domain, and unification cannot connect the two
structures. Error on Coq 8.18.0 (upstream line 16, characters 66-69, i.e. the `f x` of
`0 < f x`):

```
In environment
k : ?T
f : ?t1 -> ?W
x : ?t1
The term "f x" has type "NormedModule.sort ?W"
while it is expected to have type
 "Order.POrder.sort
    (join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder ?t)".
```

On Rocq 9.1.1 the file stops earlier, at `Variable R : realType.` outside a Section
(`declaration-outside-section`, an error since Rocq 9.0). With that line silenced (or
with all the repository's compat lines added, scratch file `s91/up3.v`), Rocq 9.1.1 stops at
the same `f x` error (with `Order.Preorder.sort (...)` in place of
`Order.POrder.sort (...)`, the MathComp 2.5 name). So compat lines cannot rescue the
upstream copy, and it is kept strictly verbatim.

**Re-reading the whole statement against the trap list of the brief (section 7.5):** no
further defect.

* Exponential: `expR (k * x)` is e^(kx) for every real k, x (`expR` is
  `mathcomp.analysis.sequences.expR`, `limn (series (exp_coeff x))`, checked by `Print`
  on both toolchains). No `Rpower`/`ln`, no `pow`/`^` with a `nat` exponent, no `exprz`,
  no `nat`/`int` division.
* Derivative: `f^`() x` is `derive1 f x` (the ordinary derivative; `derive1E` rewrites it
  to `'D_1 f x`, check 4.3). `differentiable f x` for `f : R -> R` is equivalent to
  derivability at x (`derivable1_diffP`), required at every x, as in the problem.
* `0 < f x < f^`() x` is `(0 < f x) && (f x < f^`() x)`: positivity and f(x) < f'(x),
  both strict, as in the problem. `hf` is a binder of the `forall`, i.e. a genuine
  hypothesis (not a `(h : Prop := ...)` local definition).
* Quantifiers: `exists N : R` is inside `forall f`, so N may depend on f, as in the
  problem; `forall x, N < x -> expR (k * x) < f x` is "f(x) > e^(kx) for all x > N"
  (strict both times). No existential scoping over an iff.
* Answer: `[set k | k < 1]` is (-oo, 1), the official answer and the Lean statement's
  `Set.Iio 1` (open at 1, which is correct: k = 1 fails, see check 4.5). The equality of
  sets encodes "find the set of all k", both inclusions.
* `k` has type `R` (forced by the equality with `putnam_1994_b3_solution : set R`;
  visible in the `Set Printing All` output), `0`, `1`, `<`, `*` are the ring/order
  operations of `R` (`GRing.zero`, `GRing.one`, `Order.lt`, `GRing.mul` in the elaborated
  terms), not `nat` ones. No `Series`, `sum_n`, integrals, `sup`, `Q`, divisibility,
  indexing.
* Hypotheses: exactly the problem's (positivity, differentiability, f' > f); none
  missing, none extra.

## 3. The fix

`putnam_1994_b3_corrected.v` differs from the upstream text in four statement lines,
plus the marked compat lines (output of `diff` of the corrected body with the compat
lines removed against the upstream file):

```diff
+Set Warnings "-notation-overridden". (* compat: ... *)         [after line 2]
+From mathcomp Require Import ssralg. (* compat: ... *)
+Set Warnings "notation-overridden". (* compat: restore the default. *)
 ...
+Set Warnings "-declaration-outside-section,-local-declaration". (* compat: ... *)
 Variable R : realType.
-Definition putnam_1993_b3_solution : set R := [set k | k < 1].
-Theorem putnam_1993_b3
-    : [set k | forall f (hf : forall x, differentiable f x /\ 0 < f x < f^`() x),
-        exists N : R, forall x, N < x -> expR (k * x) < f x] = putnam_1993_b3_solution.
+Definition putnam_1994_b3_solution : set R := [set k | k < 1].
+Theorem putnam_1994_b3
+    : [set k | forall (f : R -> R) (hf : forall x, differentiable f x /\ 0 < f x < f^`() x),
+        exists N : R, forall x, N < x -> expR (k * x) < f x] = putnam_1994_b3_solution.
```

(The compat lines are copied byte-for-byte from the repository's root/extended files.)

* Renaming (`1993` -> `1994` in both names) is the `naming` fix.
* `f` -> `(f : R -> R)` is the `compile` fix the audit names. It only states the type the
  problem intends; the elaborated theorem has `f : Real.sort R -> Real.sort R`, and
  every other token elaborates as upstream intended (section 2).

Compat lines: kind (2) (before `Variable R : realType.`) is required on Rocq >= 9.0.
Kind (1) (the bracketed `ssralg` re-import, after the second import line and before
`From mathcomp Require Import classical_sets.`, as in the other files of the repository)
is added because the statement uses the ring numerals `0`, `1`. This file already
imports `ssralg` after `all_ssreflect` and never imports `all_algebra`, so the re-import
is a no-op on MathComp 2.5 as well: the theorem's type and `putnam_1994_b3_solution`
print identically under `Set Printing All` with and without it (check 4.2). It is kept for
uniformity. Kind (3) (derivative notations) is not needed: upstream already opens
`classical_set_scope`, where MathComp-Analysis >= 1.9 defines ``f^`()``.

Why the corrected statement is faithful: it is the problem's "find all k" as an equality
of sets, with the official answer (-oo, 1), and the property of k transcribed literally
(section 2). Nothing is weakened; no hypothesis added or dropped.

Comparison with the Lean statement (`putnam_1994_b3.lean`):

```lean
theorem putnam_1994_b3 :
    {k | ∀ f (hf : (∀ x, 0 < f x ∧ f x < deriv f x) ∧ Differentiable ℝ f),
      ∃ N, ∀ x > N, Real.exp (k * x) < f x} = putnam_1994_b3_solution
-- putnam_1994_b3_solution := Set.Iio 1
```

Same content: Lean's `Differentiable ℝ f` = differentiability at every x (Rocq puts it
inside `forall x`), `deriv f x` = `f^`() x`, `∀ x > N` = `forall x, N < x -> ...`,
`Set.Iio 1` = `[set k | k < 1]`. Lean infers `f : ℝ → ℝ`; the Rocq fix writes it. The
Rocq statement keeps upstream's hypothesis layout (differentiability and the inequalities
in one `forall x`), which is logically the same as Lean's.

## 4. Sanity checks actually run

Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (Nix, `source
/opt/rocq91/bin/rocq-env.sh`) and Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0
(Ubuntu 24.04, plain `coqc`), build products deleted between toolchains. Scratch files
(not deliverables) are in `.../scratchpad/work/putnam_1994_b3/`.

1. **Compilation of the deliverables** (in the problem folder).
   * `rocq compile -R . "" putnam_1994_b3_corrected.v` (Rocq 9.1.1): exit 0, `.vo`
     written; all 26 warnings of the log are at line 46, the upstream
     `From mathcomp Require Import all_ssreflect ssralg ssrnum.` (MathComp's own:
     `all_ssreflect` deprecated, overridden notations, ambiguous coercion paths); none at
     any other line.
   * `coqc -R . "" putnam_1994_b3_corrected.v` (Coq 8.18.0, after deleting the `.vo`
     files): exit 0; all 22 warnings at line 46; none elsewhere.
   * `putnam_1994_b3.v` (upstream copy): Rocq 9.1.1 exits 1 at line 55 (= upstream
     line 13, the `Variable`, `declaration-outside-section`); Coq 8.18.0 exits 1 at
     line 58, characters 66-69 (= upstream line 16) with the `f x` error of section 2
     (plus the `local-declaration` warning at line 55). Scratch copies with the compat
     lines added (`s91/up2.v`: Variable line only; `s91/up3.v`: all compat lines) fail on
     Rocq 9.1.1 with the same `f x` error, and `s818/up3.v` fails the same way on Coq 8.18.0.
2. **Byte identity and minimal diff.** `tail -n +43 putnam_1994_b3.v | cmp - <upstream>`:
   identical (658 bytes, no trailing newline; assembled by `cat` of the header and the
   upstream file). `diff` of the corrected body without the compat lines against the
   upstream file: exactly lines 14-17 differ, as shown in section 3.
   **Compat lines do not change the elaboration**: `Set Printing All. Check
   putnam_1994_b3. Print putnam_1994_b3_solution.` appended to the corrected body with
   and without the three `ssralg` compat lines (`pa_with.v` / `pa_without.v`): outputs
   byte-identical on Rocq 9.1.1 (6029 bytes) and on Coq 8.18.0 (5709 bytes).
3. **Non-vacuity and meaning of the notations** (`sanity.v` = the corrected file followed
   by the lemmas below; exit 0 on BOTH toolchains; the only warning outside the upstream
   import line comes from the scratch import `From mathcomp Require Import functions exp.`):
   * `derive1_shape : f^`() x = 'D_1 f x` (by `derive1E`).
   * `witness_hf`: `f = expR * expR` (i.e. x |-> e^(2x)) satisfies `hf` at every x:
     differentiable (`is_deriveM`, `is_derive_expR`, `derivable1_diffP`) and
     `0 < e^x e^x < e^x e^x + e^x e^x` (`derive_val`, `mulr_gt0`, `ltrDr`). So the
     class of functions quantified over is nonempty and the set-builder is not vacuously
     all of R.
   * `solution_nontrivial : 0 \in putnam_1994_b3_solution /\ 1 \notin putnam_1994_b3_solution`.
   * `Print Assumptions` of `witness_hf` and `solution_nontrivial` (both toolchains):
     `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`,
     `boolp.constructive_indefinite_description` and `R : realType` only.
   * `Set Printing All. Check putnam_1994_b3.`: `k` ranges over the carrier of `R`,
     `f : forall _ : Real.sort R, Real.sort R`, the conclusion uses `@expR`, `derive1`,
     `Order.lt`, `GRing.mul`, `GRing.zero` (and `GRing.one` in the solution set).
     `Locate expR` / `Print expR`: `mathcomp.analysis.sequences.expR`, the exponential
     series, on both toolchains.
4. **Final files**: the Rocq 9.1.1 compile in 4.1 was run before a comment-only edit of the
   corrected file's header (same line count); the Coq 8.18.0 compile in 4.1 and both verifier
   runs (4.8) compiled the final files.
5. **Numerical check of the answer boundary** (`numeric_check.py`): for
   f(x) = exp(x - e^(-x)) the script asserts on the grid x = -5, -4.75, ..., 15 that
   f > 0, f' > f (central difference; exactly f' = (1 + e^(-x)) f) and f < e^x, all
   passing; f/e^x = 0.3679, 0.99328, 0.9999546, 0.9999997, 1.0000000 at x = 0, 5, 10, 15,
   30 (always < 1), while f/e^(0.9x) = 0.37, 1.64, 2.72, 4.48, 20.1 grows. This is the
   behaviour the answer (-oo, 1) predicts: k = 1 (and so every k >= 1) fails, k = 0.9 holds
   for this f.
6. **No model names** in the `.v` files or in this file (grep: no hit).
7. No `_statement_is_false` / `_statement_is_vacuous` file: the verdict is
   naming/compile; the corrected statement is satisfiable (check 3) and true (section 5).
8. **Verifier**, verdict lines as printed:
   * `(source /opt/rocq91/bin/rocq-env.sh && cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1994_b3)`:
     ```
     NOTE putnam_1994_b3.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)
     OK   putnam_1994_b3_corrected.v compiles
     OK   putnam_1994_b3_corrected.v ends in Admitted (statement only)
     OK   putnam_1994_b3.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
     checked 1 problem folder(s), 0 with a proof file
     ALL CHECKS PASSED
     ```
   * `(cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1994_b3)` (Coq 8.18.0):
     ```
     NOTE putnam_1994_b3.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)
     OK   putnam_1994_b3_corrected.v compiles
     OK   putnam_1994_b3_corrected.v ends in Admitted (statement only)
     OK   putnam_1994_b3.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
     checked 1 problem folder(s), 0 with a proof file
     ALL CHECKS PASSED
     ```

## 5. Difficulty estimate and proof sketch

**Difficulty: 2 / 5.** Elementary real analysis. It needs one monotonicity-from-derivative
lemma, a derivative of an explicit function, and some `expR`/`ln` algebra. All of these
are in MathComp-Analysis (on both versions).

Mathematical proof.

* (k < 1 => property.) Let g(x) = f(x) e^(-x). Then g'(x) = (f'(x) - f(x)) e^(-x) > 0,
  so g is increasing and f(x) >= f(0) e^x for x >= 0. With c = f(0) > 0 and
  N = max(0, -ln c / (1 - k)), for x > N: f(x) >= c e^x = c e^((1-k)x) e^(kx)
  > e^(kx), because (1-k)x > -ln c.
* (property => k < 1.) Suppose k >= 1. Take f(x) = e^(x - e^(-x)): positive, differentiable,
  f'(x) = (1 + e^(-x)) f(x) > f(x). For x >= 0, f(x) < e^x <= e^(kx). Given any N,
  x = max(N, 0) + 1 violates f(x) > e^(kx). So k is not in the set.

Rocq plan (names checked in the MathComp-Analysis 1.16.0 sources; the same lemmas exist
in 1.0.0):

* Set equality: `eqEsubset` / `funext` + `propext` (or `seteqP`), then two directions.
* Direction 1: monotonicity of g = f * (expR \o -) by `ger0_derive1_ndecr` (derive.v;
  hypotheses: derivability on `]a, b[`, `0 <= g^`()` there, continuity on `[a, b]`,
  from `differentiable_continuous`). Derivative of g: `is_deriveM`, chain rule
  (`derive1_comp`) or `expRN` to write e^(-x) = (e^x)^-1 and `deriveV`,
  `is_derive_expR`, `derive1E`, `derive_val`, `derivable1_diffP` to go from
  `differentiable` to `derivable`. Then `expRD`, `ltr_expR`, `lnK` / `expRK` for the
  choice of N; `ln` of `f 0 > 0`.
* Direction 2: the witness x |-> expR (x - expR (- x)): derivative via
  `is_derive_expR`, `is_deriveB`, `is_deriveN` and the chain rule; `f' - f =
  expR (- x) * f x > 0` by `expR_gt0`, `mulr_gt0`; the bound `f x < expR x <= expR (k * x)`
  by `ltr_expR`, `ler_expR` (monotone), `expR_gt0`, `ler_wpM2r` for `x <= k * x` when
  `x >= 0`, `k >= 1`; then `N < max N 0 + 1` for the contradiction. Here k >= 1 comes from
  `~ (k < 1)` via `leNgt`.
* Expected `Print Assumptions`: only the statement's `R` and the three `boolp` axioms.

## 6. Status of each file

| file | status |
|---|---|
| `putnam_1994_b3.v` | upstream text verbatim after a header comment (no compat lines: it would not compile with them either). **Does not compile** on Rocq 9.1.1 (first stop: `Variable` outside a Section; then the `f x` type error) nor on Coq 8.18.0 (the `f x` type error), as expected for the `compile` verdict. |
| `putnam_1994_b3_corrected.v` | corrected statement (names 1993 -> 1994, `f : R -> R`) + marked compat lines; ends in `Proof. Admitted.`; **compiles** on Rocq 9.1.1 and on Coq 8.18.0 with no warning from its own lines. |
| `putnam_1994_b3_statement_is_false.v` / `_vacuous.v` | not applicable (verdict naming/compile; the corrected statement is satisfiable and true). |
| `putnam_1994_b3_corrected_proof.v` | not written in this phase (proofs are out of scope). Sketch in section 5. |
| `NOTES.md` | this file. |
