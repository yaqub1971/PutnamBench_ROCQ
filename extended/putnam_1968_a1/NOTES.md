# putnam_1968_a1 -- notes

Audit verdict: **naming** (the theorem has the wrong name; the mathematics is faithful).
Upstream commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 of PutnamBench, file
`coq/src/putnam_1968_a1.v`.

## 1. The problem

Putnam 1968 A1. Prove that

    22/7 - pi = int_0^1 x^4 (1 - x)^4 / (1 + x^2) dx.

(A classical proof that 22/7 > pi: the integrand is positive on (0, 1). Long division gives
x^4 (1 - x)^4 / (1 + x^2) = x^6 - 4x^5 + 5x^4 - 4x^2 + 4 - 4/(1 + x^2), and integrating
term by term gives 1/7 - 2/3 + 1 - 4/3 + 4 - 4 atan 1 = 22/7 - pi.) PutnamBench's informal
file gives no solution text ("None."); nothing is to be determined, it is a pure "prove that".

## 2. Defect(s) in the upstream statement

The upstream file (kept verbatim, after a header comment and the marked compat lines, in
`putnam_1968_a1.v`) is

```coq
Variable R : realType.
Definition mu := [the measure _ _ of @lebesgue_measure R].
Theorem putnam_1968_b1
    : 22/7 - pi = \int[mu]_(x in [set x : R | 0 <= x <= 1]) (x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2)).
Proof. Admitted.
```

**Defect (the audited one): naming.** The theorem is declared `putnam_1968_b1`, although
the file is `coq/src/putnam_1968_a1.v` and the problem is 1968 **A1** (PutnamBench's
informal statement and Lean statement are both named `putnam_1968_a1`; 1968 B1 is a
different problem of the same competition). A harness or a proof file that looks for the
theorem `putnam_1968_a1` does not find it (checked: `Check putnam_1968_a1.putnam_1968_a1`
fails, see section 4).

**Re-reading the whole statement against the trap list of the brief (section 7.5): no
further defect.** Checked item by item (the elaboration claims are backed by the
`Set Printing All` output and the conversion check of section 4):

* `22/7` is real division: it elaborates to `GRing.mul (22%:R) (GRing.inv (7%:R))` in `R`
  (natmul of the ring's `1`), not `nat` or `int` division.
* `x ^ 4`, `(1 - x) ^ 4`, `x ^ 2` are `ssrint.exprz` with the int exponents `4`, `4`, `2`
  (the "exprz exponents parsed in int" trap): harmless, each is convertible to `x ^+ 4`
  etc. The problem's exponents are integers, so no real exponent was meant.
* `1 - x`, `1 + x ^ 2` and the division are ring operations of `R`; the denominator
  `1 + x^2` is never 0, so the field inverse is the true inverse on all of `R`.
* `pi` is MathComp-Analysis' `trigo.pi` on `R` (the library proves `atan 1 = pi / 4`).
* The right-hand side is `Rintegral mu D g` (ring_scope `\int`), i.e.
  `fine (\int[mu]_(x in D) (g x)%:E)`: the finite part of the Lebesgue integral, which
  would be 0 if the integral were infinite (the "Rintegral / divergent" trap). Here the
  integrand is continuous on the compact set [0, 1], hence integrable, so the value is the
  genuine integral.
* `mu` is Lebesgue measure on `R`; `D = [set x : R | 0 <= x <= 1]` is the closed interval
  [0, 1] with the ring order of `R` (both bounds are the ring's `0` and `1`; checked).
  Closed vs. open interval makes no difference (the endpoints are a null set). The bounds
  are real numbers, not of a wrong type.
* No `sum_n`, `Series`, `ex_lim_seq`, `sup`, `Rpower`/`ln`/`expR`, `Q`, `int` division,
  indexing, divisibility, `\prod`, absolute values, existentials or local `:=`
  definitions occur. No hypotheses at all: the statement is a closed equation, so it
  cannot be vacuous.

**Rocq 9.1 / MathComp 2.5 compatibility (not a mathematical defect):** the raw upstream
file does not compile on Rocq 9.1.1 (checked): `Variable R : realType.` outside a `Section`
is an error there (`Use of "Variable" or "Hypothesis" outside sections behaves as
"#[local] Parameter" ...`, upstream line 11); on Coq 8.18.0 the raw file compiles, with a
`local-declaration` warning at that line. With only the Variable compat line, Rocq 9.1 /
MathComp 2.5 still fails at the `1` of `0 <= x <= 1` (upstream line 14, characters 56-57:
`The term "1" has type "BaseUMagma.sort ?s" while it is expected to have type
"Order.Preorder.sort R"`), because MathComp 2.5's `all_ssreflect` imported after
`all_algebra` overrides the ring notations `1` / `%:R`. Both files therefore carry the
repository's two marked compat lines (kinds (1) and (2) of the brief; kind (3) does not
apply: no derivative notation).

## 3. The fix

`putnam_1968_a1_corrected.v` differs from the upstream copy `putnam_1968_a1.v` in exactly
one line (besides the header comment); both carry the same marked compat lines:

```diff
 From mathcomp Require Import all_algebra all_ssreflect.
 From mathcomp Require Import reals sequences trigo measure lebesgue_measure lebesgue_integral normedtype topology.
+Set Warnings "-notation-overridden". (* compat: ... *)            (in both files)
+From mathcomp Require Import ssralg. (* compat: ... *)            (in both files)
+Set Warnings "notation-overridden". (* compat: restore the default. *)   (in both files)
 From mathcomp Require Import classical_sets.
 ...
+Set Warnings "-declaration-outside-section,-local-declaration". (* compat: ... *)   (in both files)
 Variable R : realType.
 Definition mu := [the measure _ _ of @lebesgue_measure R].
-Theorem putnam_1968_b1
+Theorem putnam_1968_a1
     : 22/7 - pi = \int[mu]_(x in [set x : R | 0 <= x <= 1]) (x ^ 4 * (1 - x) ^ 4 / (1 + x ^ 2)).
 Proof. Admitted.
```

(The ssralg compat block is placed after the second import line and before
`From mathcomp Require Import classical_sets.`, as in the root file `putnam_1962_a2.v`,
whose import block has the same shape.)

Why the corrected statement is faithful: renaming changes nothing mathematical (the two
elaborated theorem types print identically under `Set Printing All`, up to the module
name; section 4, check 3). The statement is exactly the problem's equation: left side the
real number 22/7 - pi, right side the integral over [0, 1] of x^4 (1 - x)^4 / (1 + x^2)
with respect to Lebesgue measure. Nothing is weakened; there are no hypotheses to add or
drop; there is no `_solution` definition to rename.

Comparison with the Lean statement (`putnam_1968_a1.lean`):

```lean
theorem putnam_1968_a1
: 22/7 - Real.pi = ∫ x in (0)..1, x^4 * (1 - x)^4 / (1 + x^2) :=
```

The Rocq statement follows it: the same equation, same name after the fix. The only
difference is the integral: Lean's interval integral over (0)..1 vs. the Lebesgue integral
over the closed interval [0, 1] here; for this continuous integrand both equal the Riemann
integral. The informal statement is followed exactly.

## 4. Sanity checks actually run

All on this machine, under both toolchains unless stated:
Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (Nix, `source /opt/rocq91/bin/rocq-env.sh`,
`rocq compile`) and Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (Ubuntu 24.04, `coqc`).
Scratch files are in the scratch directory `work/putnam_1968_a1/` (`b91/`, `b818/`).

1. **Both deliverable files compile, with no warning from their own lines.**
   `rocq compile -R . "" putnam_1968_a1.v` and `... putnam_1968_a1_corrected.v`: exit 0;
   the 30 warnings of each log all point at the first upstream import line
   (`From mathcomp Require Import all_algebra all_ssreflect.`, line 43 resp. 47: MathComp's
   own ambiguous-coercion, overridden-notation and all_ssreflect-deprecation warnings).
   After deleting the `.vo` files, `coqc -R . "" ...` on both: exit 0; 23 warnings each, all
   at that same import line. No `Error`, no warning at a compat line, the `Variable` or the
   `Theorem`.
2. **Raw upstream file** (no compat lines): Rocq 9.1.1 exit 1 with the Variable error at
   line 11; Coq 8.18.0 exit 0 with 23 import-line warnings plus the `local-declaration`
   warning at line 11. With the Variable compat line but without the ssralg re-import
   (tested on both the upstream and the corrected body): Rocq 9.1.1 exit 1 at the `1` of
   `0 <= x <= 1`, text quoted in section 2. On Coq 8.18.0 the raw upstream module and the
   upstream copy with the compat lines give byte-identical `Set Printing All` output for
   `Check putnam_1968_b1` and `Print mu` (the compat lines are no-ops there).
3. **Byte identity and minimal diff.** The two files were assembled by a script from the
   upstream bytes (not retyped). Stripping the header box and the `(* compat: ... *)` lines
   of `putnam_1968_a1.v` (the verifier's `strip` function) and `cmp`-ing with the upstream
   file: identical. `diff` of the two deliverables below their headers: exactly one changed
   line, `Theorem putnam_1968_b1` -> `Theorem putnam_1968_a1`. On both toolchains, `Check`
   of `putnam_1968_a1.putnam_1968_b1` and of `putnam_1968_a1_corrected.putnam_1968_a1`
   (and `Print ... mu`) under `Set Printing All` give identical output after replacing the
   module and theorem names.
4. **Reading of the statement** (`reading.v`, which `Require`s the corrected module; exit 0
   on both toolchains):
   * `Check (putnam_1968_a1 : 22%:R / 7%:R - pi = Rintegral mu D f)` succeeds, where
     `D := [set x : R | (0 <= x) && (x <= 1)]` and `f x := x ^+ 4 * (1 - x) ^+ 4 / (1 + x ^+ 2)`
     (so `x ^ 4` is convertible to `x ^+ 4`, `22/7` is real division, the domain is [0, 1]).
   * `Rintegral mu D f = fine (integral mu D (fun x => EFin (f x)))` by `reflexivity`.
   * `About putnam_1968_a1` shows the expected statement; `Fail Check putnam_1968_b1`
     succeeds (the old name is gone).
5. **Facts behind the classical proof, machine-checked in `reading.v` (both toolchains):**
   * `0 < 1 + x ^+ 2` for all `x : R` and `0 <= f x` on `D` (the integrand is defined
     everywhere and nonnegative on [0, 1]);
   * the long division `f x = x^6 - 4x^5 + 5x^4 - 4x^2 + 4 - 4/(1 + x^2)` (by `field`);
   * with `F x := x^7/7 - 2x^6/3 + x^5 - 4x^3/3 + 4x - 4 atan x`, `F 1 - F 0 = 22/7 - pi`
     (by `atan1`, `atan0`, `field`). `Print Assumptions` of that lemma: only
     `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`,
     `boolp.constructive_indefinite_description` and the module's `R`.
6. **Numerical check** (`numeric_check.py`, Python): 22/7 - pi = 0.0012644892673496777;
   Simpson's rule for the integral gives 0.0012640527 (n = 10), 0.00126448926691 (n = 100),
   0.0012644892673496172 (n = 1000; difference -6e-17). The polynomial part integrates
   exactly (rational arithmetic) to 22/7; the long-division identity holds exactly at
   x = 0, 1/3, 1/2, 2, -5/7; the integrand's minimum on a 10001-point grid of [0, 1] is
   0.0 (at the endpoints). The statement is true and non-trivial (both sides are
   approx. 0.00126, not 0).
7. **No model names** in the files (grep over the folder for the usual names: no hit).
8. `Print Assumptions` of the theorem: not applicable in this phase (both files end in
   `Admitted`).
9. **Verifier**, under both toolchains (verdict lines quoted verbatim):

   `(source /opt/rocq91/bin/rocq-env.sh && cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1968_a1)`
   ```
   toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
   OK   putnam_1968_a1.v (upstream copy) compiles
   OK   putnam_1968_a1_corrected.v compiles
   OK   putnam_1968_a1_corrected.v ends in Admitted (statement only)
   OK   putnam_1968_a1.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
   checked 1 problem folder(s), 0 with a proof file
   ALL CHECKS PASSED
   ```
   `(cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1968_a1)`
   ```
   toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
   OK   putnam_1968_a1.v (upstream copy) compiles
   OK   putnam_1968_a1_corrected.v compiles
   OK   putnam_1968_a1_corrected.v ends in Admitted (statement only)
   OK   putnam_1968_a1.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
   checked 1 problem folder(s), 0 with a proof file
   ALL CHECKS PASSED
   ```

## 5. Difficulty estimate and proof sketch

**Difficulty: 2 / 5** (routine calculus; every ingredient is in MathComp-Analysis 1.16.0,
the work is FTC bookkeeping). A proof will compile **only on Rocq 9.1 /
MathComp-Analysis 1.16.0**: MathComp-Analysis 1.0.0 (Coq 8.18 here) has no `ftc` module
and no `integral0_oneDsqr`.

Mathematical proof: long division (section 1), then the fundamental theorem of calculus
with the antiderivative F x = x^7/7 - 2x^6/3 + x^5 - 4x^3/3 + 4x - 4 atan x, and
atan 1 = pi/4, atan 0 = 0.

Rocq plan (names checked in the 1.16.0 / 2.5.0 sources; extra imports `ftc`, `derive`,
`realfun`, `ring`):

1. Replace the domain: `[set x : R | 0 <= x <= 1] = `[0, 1]%classic` (`set_itvcc`,
   `classical/set_interval.v`).
2. Route A (one FTC): `rewrite /Rintegral (@continuous_FTC2 _ _ F)` (`ftc.v`:
   `(a < b) -> {within `[a, b], continuous f} -> derivable_oo_LRcontinuous F a b ->
   {in `]a, b[, F^`() =1 f} -> \int[mu]_(x in `[a, b]) (f x)%:E = (F b)%:E - (F a)%:E`),
   exactly as the library proves `integral0_oneDsqr` in `trigo.v`. Side goals: continuity
   of the integrand (polynomials, `continuous_oneDsqrV`-style inverse of a nonvanishing
   function), derivability of F on ]0, 1[ and one-sided continuity at 0 and 1
   (`derivable_atan`, `continuous_atan`, polynomial derivability), and `F^`() x = f x`
   (build `is_derive x 1 F _` from the instances `is_deriveD`, `is_deriveM`, `is_deriveX`,
   `is_derive1_atan`, take `derive_val`, and close the rational-function identity with
   `field` using `1 + x^2 != 0`). Finally `F 1 - F 0 = 22/7 - pi` is the lemma already
   checked in `reading.v` (`atan1`, `atan0`, `field`).
3. Route B (avoids the atan derivative): split the integrand with the long division
   (checked lemma), use `RintegralB` / `RintegralD` / `RintegralZl`
   (`lebesgue_Rintegral.v`; integrability from `continuous_compact_integrable` and
   `segment_compact`), `integral0_oneDsqr 1` (`trigo.v`: `\int[mu]_(x in `[0, b])
   (oneDsqr x)^-1 = atan b`) for the 4/(1 + x^2) part, and `continuous_FTC2` for the
   polynomial part.
4. Friction points: the statement's `mu` is `[the measure _ _ of @lebesgue_measure R]`
   while `trigo.v` uses `@lebesgue_measure R` (should be convertible; check early), and the
   statement's `x ^ 4` is `exprz x 4` with the int `4` elaborated as `4%:R` and `exprz`
   declared `simpl never` in MathComp 2.5: turn it into `x ^+ 4` by `change` (it is
   convertible, check 4) rather than `simpl` (`exprnP : x ^+ n = x ^ n` only matches a
   `Posz n` exponent syntactically).
5. Expected `Print Assumptions`: only the statement's `R` and the three `boolp` axioms.

## 6. Status of each file

| file | status |
|---|---|
| `putnam_1968_a1.v` | upstream text verbatim after a header comment, plus the marked compat lines; compiles on Rocq 9.1.1 and on Coq 8.18.0 (checks 1, 9); verified byte-identical to upstream apart from header and compat lines (checks 3, 9). |
| `putnam_1968_a1_corrected.v` | corrected statement (theorem renamed `putnam_1968_a1`, nothing else changed), ends in `Proof. Admitted.`; compiles on Rocq 9.1.1 and on Coq 8.18.0 with no warning from its own lines (checks 1, 9). |
| `putnam_1968_a1_statement_is_false.v` / `_vacuous.v` | not written: the verdict is `naming`; the statement has no hypotheses (so it cannot be vacuous) and is true (checks 5, 6), so there is nothing to refute. |
| `putnam_1968_a1_corrected_proof.v` | not written in this phase (proofs are out of scope). Sketch in section 5. |
| `NOTES.md` | this file. |
