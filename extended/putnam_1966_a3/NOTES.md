# putnam_1966_a3 -- notes

Audit verdict: **compile** (one-token fix; statement otherwise faithful). Upstream commit
4dbe26ef21563af851eedaeb82d936fe1f94fc52 of PutnamBench, file `coq/src/putnam_1966_a3.v`.

## 1. The problem

Putnam 1966 A3. If 0 < x_1 < 1 and x_{n+1} = x_n (1 - x_n) for all n >= 1, prove that
lim_{n -> oo} n x_n = 1. (The sequence decreases to 0 like 1/n; the classical proof
looks at 1/x_{n+1} - 1/x_n = 1/(1 - x_n) -> 1 and applies Cesaro's lemma.)

## 2. Defect(s) in the upstream statement

The upstream file (kept verbatim, after a header comment, in `putnam_1966_a3.v`) is

```coq
Variable R : realType.
Theorem putnam_1966_a3
    (x : nat -> R)
    (hx1 : 0 < x 1%nat /\ x 1%nat < 1)
    (hxi : forall n : nat, ge n 1 -> x (n.+1) = x n * (1 - x n))
    : (fun n : nat => n%:R * x n) @ \oo --> 1.
Proof. Admitted.
```

**Defect (the audited one): it does not compile.** The target of `-->` is the bare
numeral `1`. `F --> y` is `cvg_to (nbhs F) (nbhs y)`, so `y` must live in a filtered
(topological) type; a bare `1` is only known to be the unit of *some* semiring, and the
two unification problems have no common solution. On Coq 8.18.0 / MathComp 2.1.0 /
MathComp-Analysis 1.0.0 the error is (upstream line 18, characters 44-45):

```
The term "1" has type "GRing.SemiRing.sort ?s0"
while it is expected to have type "Filtered.sort ?s".
```

The audit table lists the identical defect for 1966 A6, 1969 B3, 1978 B2, 2015 B4 and
2021 B2 (`--> <numeral or ratr ...>` without a type ascription).

**Re-reading the whole statement against the trap list of the brief (section 7.5):**
no further defect.

* Indexing: the problem's sequence is x_1, x_2, ...; the statement constrains `x 1%nat`
  and imposes the recurrence for `ge n 1` (Peano's `n >= 1`, printed `(n >= 1)%coq_nat`
  in the error log), i.e. for n = 1, 2, .... This is 1-indexed exactly like the problem.
  `x 0` is unconstrained; the conclusion is a limit, which does not depend on `x 0`
  (and at n = 0 the term is `0%:R * x 0 = 0` anyway). Harmless and faithful.
* `n%:R * x n` is the real number n times x_n (`n%:R` is the cast `nat -> R`; the
  `Set Printing All` output in the scratch file shows `GRing.natmul ... (GRing.one ...) n`).
* `*` and `-` are ring operations on `R` (the error log prints the elaborated hypotheses
  `0 < x 1%N /\ x 1%N < 1` and `x n.+1 = x n * (1 - x n)` in `R`): no `nat` subtraction,
  no division, no `pow`/`^`, no `Rpower`/`ln`, no `Series`/`sum_n`, no integrals, no
  `sup`, no `exprz`, no `Q`. None of the numeric traps can occur.
* `@ \oo --> (1 : R)` is the image filter of `\oo` (checked: `\oo = eventually` on `nat`
  by `reflexivity`) under n |-> n x_n converging to the neighbourhoods of the real 1: the
  ordinary limit lim_{n -> oo} n x_n = 1, not a one-sided or `+oo`-admitting notion.
* Hypotheses: exactly the problem's two (0 < x_1 < 1 and the recurrence for n >= 1);
  none missing, none extra, none of the `(h : Prop := ...)` kind.
* The theorem name matches the problem (no `naming` issue); there is no `_solution`.

**Rocq 9.1 / MathComp 2.5 compatibility (not a mathematical defect):** the upstream text
has the two constructs the repository README documents as fatal on the CI toolchain:
`Variable R : realType.` outside a `Section` (an error since Rocq 9.0; Coq 8.18 only
warns, and that warning does appear in this machine's Coq 8.18 log at the `Variable`
line; under Rocq 9.1.1 compiling the upstream copy stops exactly there, with
`Error: Use of "Variable" or "Hypothesis" outside sections behaves as "#[local] Parameter"
or "#[local] Axiom". [declaration-outside-section,vernacular,default]`, so on the CI
toolchain the `--> 1` error is not even reached) and
the import order `all_algebra all_ssreflect` (MathComp 2.5's `all_ssreflect` overrides
the ring notations `1` and `%:R`). The corrected file carries the repository's marked
compat lines for both.

## 3. The fix

`putnam_1966_a3_corrected.v` differs from the upstream text in exactly one statement
token, plus the marked compat lines:

```diff
 From mathcomp Require Import reals topology normedtype.
+Set Warnings "-notation-overridden". (* compat: ... *)
+From mathcomp Require Import ssralg. (* compat: ... *)
+Set Warnings "notation-overridden". (* compat: restore the default. *)
 From mathcomp Require Import classical_sets.
 ...
+Set Warnings "-declaration-outside-section,-local-declaration". (* compat: ... *)
 Variable R : realType.
 ...
-    : (fun n : nat => n%:R * x n) @ \oo --> 1.
+    : (fun n : nat => n%:R * x n) @ \oo --> (1 : R).
```

(The ssralg compat block is placed after the second import line and before
`From mathcomp Require Import classical_sets.`, mirroring the root file
`putnam_1962_a2.v`, whose import block has the same shape.)

Why the corrected statement is faithful: the ascription `(1 : R)` only tells Coq the type
of the limit; the conclusion becomes "n%:R * x n converges to the real number 1 as
n -> oo", which is what the problem asks. Everything else is upstream's text, already
faithful (section 2). Nothing is weakened, no hypothesis is added or dropped.

Comparison with the Lean statement (`putnam_1966_a3.lean`):

```lean
theorem putnam_1966_a3
(x : ℕ → ℝ)
(hx1 : 0 < x 1 ∧ x 1 < 1)
(hxi : ∀ n ≥ 1, x (n + 1) = (x n) * (1 - (x n)))
: Tendsto (fun n : ℕ => n * (x n)) atTop (𝓝 1)
```

The Rocq statement is a line-by-line transcription of it (1-indexed `x`, same `hx1`,
`hxi` for `n >= 1`, limit of `n * x n` at `atTop` to `𝓝 1`); the corrected file follows
the Lean statement exactly and deviates from it nowhere. Both agree with the informal
problem.

## 4. Sanity checks actually run

Two toolchains: **Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot
3.4.4** (Nix, `/opt/rocq91`, the CI toolchain; check 0 and the verifier run below) and
**Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1** (Ubuntu
24.04; checks 1-4 unless stated otherwise).

0. **Rocq 9.1.1 compile.**
   `source /opt/rocq91/bin/rocq-env.sh && cd /home/user/PutnamBench_ROCQ/extended/putnam_1966_a3 && rocq compile -R . "" putnam_1966_a3_corrected.v`
   exits 0 and writes the `.vo`. All 30 warnings in the log point at line 41 of the file
   (the upstream `From mathcomp Require Import all_algebra all_ssreflect.` line: the
   `all_ssreflect` deprecation, ambiguous coercion paths, overridden notations); no
   warning and no error at any other line (compat lines, `Variable`, `Theorem`). The
   upstream copy `putnam_1966_a3.v` exits 1 under Rocq 9.1.1, first error at its line 50
   (`Variable R : realType.`), `declaration-outside-section`, text quoted in section 2.

1. **Corrected statement compiles.**
   `cd /home/user/PutnamBench_ROCQ/extended/putnam_1966_a3 && coqc -R . "" putnam_1966_a3_corrected.v`
   exits 0 and writes `putnam_1966_a3_corrected.vo`. All 23 warnings in the log point at
   line 41 of the file, the upstream `From mathcomp Require Import all_algebra
   all_ssreflect.` line (library warnings: ambiguous coercion paths, overridden
   notations); no warning or error points at any other line, in particular none at the
   compat lines, the `Variable` or the `Theorem`. No `Error` line.
2. **Upstream copy fails as described.** `coqc -R . "" putnam_1966_a3.v` exits 1 with no
   `.vo`; the only error is at the conclusion line (line 55 of the file with its header,
   upstream line 18), text exactly as quoted in section 2. Its log also shows Coq 8.18's
   `local-declaration` warning at the upstream `Variable R : realType.` line.
3. **Byte identity.** `tail -c 574 putnam_1966_a3.v | cmp - <upstream file>` reports no
   difference (the upstream file is 574 bytes, without a trailing newline, and so is the
   body of the copy). `diff` of the upstream text against the corrected file's body with
   the `(* compat: ... *)` lines removed shows exactly one changed line, the conclusion
   (the `diff` output of the assembly script is reproduced in section 3). The two files
   were assembled from the upstream bytes by a script rather than retyped.
4. **Non-vacuity and shape** (scratch file `scratch_checks.v`, in the scratch directory,
   compiled with exit 0 on Coq 8.18.0; a copy with the three ssralg compat lines added
   after the second import line, `work/putnam_1966_a3/r91/scratch_checks.v`, also compiles
   with exit 0 on Rocq 9.1.1 and every lemma below closes there too. Without the ssralg
   re-import the Rocq 9.1 copy fails at the first `%:R`/`1` with `The term "1" has type
   "BaseUMagma.sort ?s1" while it is expected to have type "Algebra.BaseAddUMagma.sort ?V"`,
   which is exactly why the corrected file carries that compat block. Under Rocq 9.1.1
   `Print concl` shows the same term with MathComp 2.5 structure names:
   `cvg_to (nbhs (fmap (fun n => GRing.mul (Algebra.natmul (GRing.one _) n) (x n)) (nbhs eventually))) (nbhs (GRing.one _ : Real.sort R))`):
   * `Definition concl x := (fun n : nat => n%:R * x n) @ \oo --> (1 : R)` elaborates;
     `Set Printing All. Print concl.` shows
     `cvg_to (nbhs (fmap (fun n => GRing.mul (GRing.natmul GRing.one n) (x n)) (nbhs eventually))) (nbhs (GRing.one : Real.sort R))`,
     i.e. the ordinary limit in `R`. `concl x = cvg_to (fmap (fun n => n%:R * x n) eventually) (nbhs (1 : R))`
     and `(\oo : set (set nat)) = eventually` both close by `reflexivity`.
   * Witness for the hypotheses: `Fixpoint xs` with `xs 0 = 0`, `xs 1 = 1/2`,
     `xs (m+2) = xs (m+1) * (1 - xs (m+1))`. `0 < xs 1 /\ xs 1 < 1` closes by `lra`;
     `forall n, ge n 1 -> xs n.+1 = xs n * (1 - xs n)` closes by case analysis
     (`n = 0` is excluded by `inversion`, `n = m.+1` is the definition). So the
     hypotheses are satisfiable and the corrected theorem is not vacuous.
   * Small values, each closed by `lra` after unfolding: `xs 2 = 1/4`, `xs 3 = 3/16`,
     `3%:R * xs 3 = 9/16`, `4%:R * xs 4 = 39/64` (i.e. 0.5625 and 0.609375: n x_n is
     climbing towards 1 from below, as the problem predicts).
   * The full corrected theorem statement, restated inside a `Section` as a `Lemma`
     and `Check`ed, has the expected type
     `forall x : nat -> R, 0 < x 1 /\ x 1 < 1 -> (forall n, (n >= 1)%coq_nat -> x n.+1 = x n * (1 - x n)) -> n%:R * x n @[n --> \oo] --> 1`.
5. **Numerical check** (`numeric_check.py`, exact rationals for n <= 6 and floating point
   up to n = 10^6): with x_1 = 1/2, n x_n = 0.5, 0.5, 0.5625, 0.609375, 0.645676,
   0.674755 for n = 1..6, then 0.750893 (n = 10), 0.948576 (10^2), 0.992376 (10^3),
   0.999003 (10^4), 0.999877 (10^5), 0.999985 (10^6); with x_1 = 0.9, 0.01 and 0.999
   the values at n = 10^6 are 0.999979, 0.999892 and 0.998995. All approach 1 (the
   second-order term is - ln n / n, and the match with 1 - ln n / n is visible in the
   output), consistent with the statement and its `(1 : R)` target.
6. **No model names** in the two `.v` files (grep for the usual names: no hit).
7. `Print Assumptions`: not applicable in this phase (both files end in `Admitted`; there
   is no proof yet). No `_statement_is_false` / `_statement_is_vacuous` file: the verdict
   is `compile`, the statement is neither false nor vacuous (section 4.4 exhibits a
   model of the hypotheses, and the conclusion is the true theorem).

**Verifier, both toolchains** (`extended/verify.sh`, run after the final edits):

* Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix,
  /opt/rocq91), `(source /opt/rocq91/bin/rocq-env.sh && cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1966_a3)`:
  prints `NOTE putnam_1966_a3.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)`
  (its first error is Rocq >= 9.0 rejecting the top-level `Variable R : realType.`:
  `Use of "Variable" or "Hypothesis" outside sections behaves as "#[local] Parameter" or "#[local] Axiom". [declaration-outside-section,vernacular,default]`),
  `OK   putnam_1966_a3_corrected.v compiles` (no warning from its own lines, check 0),
  `OK   putnam_1966_a3_corrected.v ends in Admitted (statement only)`,
  `OK   putnam_1966_a3.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines`,
  `ALL CHECKS PASSED`.
* Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04),
  `(cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1966_a3)`:
  prints the same NOTE (here the error is the `--> 1` one:
  `The term "1" has type "GRing.SemiRing.sort ?s0" while it is expected to have type "Filtered.sort ?s".`),
  `OK   putnam_1966_a3_corrected.v compiles`,
  `OK   putnam_1966_a3_corrected.v ends in Admitted (statement only)`,
  `OK   putnam_1966_a3.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines`,
  `ALL CHECKS PASSED`.

(One earlier Rocq 9.1 run printed `NOTE putnam_1966_a3.v: could not download upstream for
comparison` after a `curl: (23) Failure writing output`: the verifier's shared
`extended/ci_upstream/` directory was removed by another problem's concurrent verifier run.
Re-running gave the output quoted above; this is a harness race, not a property of the files.)

## 5. Difficulty estimate and proof sketch

**Difficulty: 3 / 5** (routine real analysis, but with MathComp-Analysis filter
bookkeeping, index shifts and a Cesaro argument).

Mathematical proof:

1. For n >= 1, 0 < x_n < 1 (induction from `hx1` using `hxi`: if 0 < t < 1 then
   0 < t (1 - t) < 1), hence x_{n+1} = x_n (1 - x_n) < x_n: the sequence (x_n)_{n>=1} is
   strictly decreasing and bounded below by 0, so it converges to some L >= 0; passing to
   the limit in the recurrence gives L = L (1 - L), so L = 0.
2. For n >= 1 put y_n = 1/x_n. Then y_{n+1} - y_n = 1/(x_n (1 - x_n)) - 1/x_n
   = 1/(1 - x_n) -> 1/(1 - 0) = 1.
3. Cesaro: the arithmetic means of the differences converge to the same limit, and they
   telescope: (1/n) sum_{k=1}^{n} (y_{k+1} - y_k) = (y_{n+1} - y_1)/n -> 1. Hence
   y_{n+1}/n -> 1, i.e. n x_{n+1} -> 1, and n x_n = (n/(n-1)) (n-1) x_n -> 1 * 1 = 1.

Rocq plan (all names checked to exist both in the installed MathComp 2.1.0 /
MathComp-Analysis 1.0.0 sources and in the MathComp 2.5.0 / MathComp-Analysis 1.16.0
sources of the CI toolchain: in 1.16.0 `cesaro`, `cvg_harmonic`, `nonincreasing_is_cvgn`,
`near_nonincreasing_is_cvgn`, `cvg_shiftS`, `cvg_shiftn`, `seriesEnat` and the notation
`nonincreasing_seq` are in `theories/sequences.v`, `cvgM`/`cvgV` in
`theories/normedtype_theory/normed_module.v`, `cvgB`/`cvgD` in
`theories/normedtype_theory/pseudometric_normed_Zmodule.v`; in 2.5.0 `telescope_sumr` is
in `algebra/ssralg.v` (and `boot/nmodule.v`), `mulr_ilt1`/`mulr_gt0`/`subr_gt0` in
`algebra/num_theory/numdomain.v`; extra imports for the proof: `sequences`, `lra`):

* Step 1: prove `forall n, (1 <= n)%N -> 0 < x n < 1` by induction (`lra` or
  `mulr_gt0`, `mulr_ilt1`, `subr_gt0`), then `nonincreasing_seq` / `has_lbound` for the
  shifted sequence `fun n => x n.+1` and `nonincreasing_is_cvgn` (or
  `near_nonincreasing_is_cvgn`) to get `cvgn`; identify the limit with `cvg_lim`,
  `cvg_unique`, continuity of the ring operations (`cvgM`, `cvgB`, `cvg_cst`) and the
  fact that `L = L * (1 - L)` forces `L = 0` (`lra`/`mulf_eq0`); transport across the
  index shift with `cvg_shiftS` / `cvg_shiftn` (`sequences.v`).
* Step 2: `cvgB`, `cvgV` (`1 - 0 != 0`), `cvg_cst` give `(fun n => (1 - x n.+1)^-1) @ \oo --> 1`.
* Step 3: `cesaro` (`sequences.v`, `Theorem cesaro (u_ : R ^nat) (l : R) : u_ @ \oo --> l -> arithmetic_mean u_ @ \oo --> l`
  with `arithmetic_mean u_ n = n.+1%:R^-1 * series u_ n.+1`) applied to
  `u_ k := (x k.+1)^-1 ... ` written as the difference `(x k.+2)^-1 - (x k.+1)^-1`
  (`hxi` gives `x k.+2 = x k.+1 * (1 - x k.+1)`, so this difference is `(1 - x k.+1)^-1`);
  `seriesEnat` and `telescope_sumr` (`ssralg.v`) turn `series u_ n.+1` into
  `(x n.+2)^-1 - (x 1)^-1`. Then `cvgD`/`cvgM` with `cvg_harmonic` (`n.+1%:R^-1 -> 0`)
  give `n.+1%:R^-1 * (x n.+2)^-1 @ \oo --> 1`, `cvgV` gives `n.+1%:R * x n.+2 --> 1`,
  and `n.+2%:R * x n.+2 = (1 + n.+1%:R^-1) * (n.+1%:R * x n.+2)` with `cvgM`, `cvgD`,
  `cvg_harmonic` gives `n.+2%:R * x n.+2 --> 1`; finish with `cvg_shiftn` (N = 2) or
  `cvg_shiftS` twice to remove the shift.
* Expected `Print Assumptions`: only the statement's `R` and the three classical axioms
  of `mathcomp.classical` (`propositional_extensionality`,
  `functional_extensionality_dep`, `constructive_indefinite_description`).

Friction points to expect: `nbhs`/`near` goals when identifying limits, the `x 0` term
(never used: all sequences are shifted to start at index 1 or 2), and `ge n 1` being
Peano `le` rather than the boolean `(1 <= n)%N` (`/leP` or `ssrnat`'s `leP` converts).

## 6. Status of each file

| file | status |
|---|---|
| `putnam_1966_a3.v` | upstream text verbatim after a header comment (no compat lines: it would not compile with them either). **Does not compile** on Coq 8.18.0 (error at `--> 1`, section 2, check 2) nor on Rocq 9.1.1 (first error at the top-level `Variable`, check 0), by design of the `compile` verdict. |
| `putnam_1966_a3_corrected.v` | corrected statement, ends in `Proof. Admitted.`; **compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (check 0) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (check 1)**, no warning from its own lines on either; verifier ALL CHECKS PASSED on both; differs from upstream by the one token `(1 : R)` and the marked compat lines. |
| `putnam_1966_a3_statement_is_false.v` / `_vacuous.v` | not applicable (verdict `compile`; statement faithful, satisfiable hypotheses, true conclusion). |
| `putnam_1966_a3_corrected_proof.v` | not written in this phase (proof phase). Sketch in section 5. |
| `NOTES.md` | this file. |
