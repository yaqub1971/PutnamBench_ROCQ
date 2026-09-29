# putnam_1978_b2 -- notes

Audit verdict: **compile** (one-token fix; statement otherwise faithful). Upstream commit
4dbe26ef21563af851eedaeb82d936fe1f94fc52 of PutnamBench, file `coq/src/putnam_1978_b2.v`.

## 1. The problem

Putnam 1978 B2. Find

    sum_{i=1}^oo sum_{j=1}^oo 1 / (i^2 j + 2 i j + i j^2).

The answer is 7/4. (The denominator is i j (i + j + 2); summing over j by partial
fractions gives H_{i+2} / (i (i + 2)), H_k the k-th harmonic number, and the resulting
series over i telescopes to 7/4.)

## 2. Defect(s) in the upstream statement

The upstream file (kept verbatim, after a header comment, in `putnam_1978_b2.v`) is

```coq
Variable R : realType.
Definition putnam_1978_b2_solution : rat := 7/4.
Theorem putnam_1978_b2
    (f : nat -> R := fun n => \sum_(1 <= i < n.+1) (\sum_(1 <= j < n.+1) (1%R)/(i%:R ^+ 2 * j%:R + 2 * i%:R * j%:R + i%:R * j%:R ^+ 2)))
    : (f @ \oo --> ratr putnam_1978_b2_solution).
Proof. Admitted.
```

**Defect (the audited one): it does not compile.** The target of `-->` is
`ratr putnam_1978_b2_solution` without a type. `F --> y` is `cvg_to (nbhs F) (nbhs y)`,
so `y` must live in a filtered (topological) type; `ratr q` is only known to live in
*some* unit ring, and the two unification problems have no common solution. On Coq
8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 the error is (upstream line 17,
characters 19-47):

```
The term "ratr putnam_1978_b2_solution" has type "GRing.UnitRing.sort ?R"
while it is expected to have type "Filtered.sort ?s".
```

The audit table lists the same defect for 1966 A3, 1966 A6, 1969 B3, 2015 B4 and
2021 B2 (`--> <numeral or ratr ...>` without a type ascription).

**Re-reading the whole statement against the trap list of the brief (section 7.5):** no
further defect.

* Summation bounds: `\sum_(1 <= i < n.+1)` is i = 1..n (MathComp's `\sum_(m <= i < n)` is
  half-open), likewise for j, so `f n` is the square partial sum over 1 <= i, j <= n.
  The problem is 1-indexed and so is the encoding; the bound `n` is not used inside the
  summand (only the indices `i`, `j` are). `f 0 = 0` (empty sum), harmless for a limit.
  Checked concretely: f 1 = 1/4, f 2 = 59/120 (section 4).
* Square partial sums vs. the problem's iterated sum: every term is positive, so by
  Tonelli the double series (sum over N+ x N+) and the iterated sum have the same value
  in [0, +oo], and the square partial sums increase to it (squares exhaust N+ x N+).
  Hence "f n -> 7/4" is equivalent to "the iterated sum equals 7/4": the encoding is
  faithful, neither weaker nor stronger (it also rules out divergence, since a limit in
  R is required).
* Summand: `(1%R)/(i%:R ^+ 2 * j%:R + 2 * i%:R * j%:R + i%:R * j%:R ^+ 2)` is the real
  number 1 / (i^2 j + 2 i j + i j^2): `%:R` casts to R, `^+ 2` is the ring power with nat
  exponent 2 (the intended exponent), `2` is the ring numeral in R (ring_scope), `/` is
  field division in R. No nat division, no `Rpower`/`ln`, no `exprz`, no `Series` of a
  divergent series, no `sup`, no integrals. For i, j >= 1 the denominator is a positive
  integer, so no division by zero occurs anywhere in the sum.
* Answer: `putnam_1978_b2_solution : rat := 7/4` is rational division (checked:
  `7/4 == 7%:Q / 4%:Q` by computation), and `ratr` of it is the real 7/4 (checked:
  `ratr (7/4) = 7 / 4` in R). It is the problem's exact answer, not a bound.
* `(f : nat -> R := ...)` is a local *definition* used as intended (it names the partial
  sums); it is not a hypothesis that was meant to be assumed, so the `(h : Prop := ...)`
  trap does not apply.
* `@ \oo -->` is the ordinary limit n -> oo in R (not `+oo`-admitting, not one-sided).
* The theorem name matches the problem; `_solution` is named consistently.

**Rocq 9.1 / MathComp 2.5 compatibility (not a mathematical defect):** the upstream text
has the two constructs the repository README documents as fatal on the CI toolchain:
`Variable R : realType.` outside a `Section` (an error since Rocq 9.0; Coq 8.18 only
warns, and that warning appears in this machine's Coq 8.18 log at the `Variable` line;
under Rocq 9.1.1 compiling the upstream copy stops exactly there, with
`Error: Use of "Variable" or "Hypothesis" outside sections behaves as "#[local] Parameter"
or "#[local] Axiom". [declaration-outside-section,vernacular,default]`, so on the CI
toolchain the `-->` error is not even reached) and the import order
`all_algebra all_ssreflect`. The corrected file carries the repository's marked compat
lines for both.

## 3. The fix

`putnam_1978_b2_corrected.v` differs from the upstream text in exactly one statement
token (a type ascription), plus the marked compat lines. `diff` of the upstream file
against the body of the corrected file (header removed):

```diff
 From mathcomp Require Import reals topology sequences normedtype.
+Set Warnings "-notation-overridden". (* compat: ... *)
+From mathcomp Require Import ssralg. (* compat: ... *)
+Set Warnings "notation-overridden". (* compat: restore the default. *)
 From mathcomp Require Import classical_sets.
 ...
+Set Warnings "-declaration-outside-section,-local-declaration". (* compat: ... *)
 Variable R : realType.
 ...
-    : (f @ \oo --> ratr putnam_1978_b2_solution).
+    : (f @ \oo --> (ratr putnam_1978_b2_solution : R)).
```

(The ssralg compat block sits after the second import line and before
`From mathcomp Require Import classical_sets.`, as in the root file `putnam_1962_a2.v`
and in `extended/putnam_1966_a3`, whose import blocks have the same shape.)

Why the corrected statement is faithful: the ascription `(... : R)` only tells Coq the
type of the limit; the conclusion becomes "the square partial sums f n converge to the
real number 7/4", which (section 2) is equivalent to the problem's iterated sum being
7/4. Everything else is upstream's text, already faithful. Nothing is weakened, no
hypothesis is added or dropped.

Comparison with the Lean statement (`putnam_1978_b2.lean`):

```lean
abbrev putnam_1978_b2_solution : ℚ := sorry  -- 7 / 4
theorem putnam_1978_b2
: (∑' i : ℕ+, ∑' j : ℕ+, (1 : ℚ) / (i ^ 2 * j + 2 * i * j + i * j ^ 2) = putnam_1978_b2_solution)
```

Lean writes the literal iterated sum (`tsum` over positive naturals, in ℚ); the Rocq
statement writes the limit of square partial sums in R with the answer taken in `rat` and
cast by `ratr`. Same answer 7/4, same summand, same index range. The Rocq form is, if
anything, more robust: Lean's `tsum` is 0 for a non-summable family, whereas the Rocq
limit statement asserts convergence. We keep the upstream Rocq shape (minimal diff).

## 4. Sanity checks actually run

Two toolchains: **Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot
3.4.4** (Nix, `/opt/rocq91`, the CI toolchain) and **Coq 8.18.0 / MathComp 2.1.0 /
MathComp-Analysis 1.0.0 / Coquelicot 3.4.1** (Ubuntu 24.04).

0. **Rocq 9.1.1 compile of the corrected file.**
   `source /opt/rocq91/bin/rocq-env.sh && cd /home/user/PutnamBench_ROCQ/extended/putnam_1978_b2 && rocq compile -R . "" putnam_1978_b2_corrected.v`
   exits 0 and writes the `.vo`. All 30 warnings in the log point at line 42 of the file
   (the upstream `From mathcomp Require Import all_algebra all_ssreflect.` line: the
   `all_ssreflect` deprecation, ambiguous coercion paths, overridden notations); none at
   any other line. No `Error`.
1. **Coq 8.18.0 compile of the corrected file** (after deleting the `.vo` files):
   `coqc -R . "" putnam_1978_b2_corrected.v` exits 0; all 23 warnings point at line 42
   (the same import line); none at any other line. No `Error`.
2. **Upstream copy fails as described.** Coq 8.18.0: exit 1, the only error at file line
   53 (upstream line 17), characters 19-47, text as quoted in section 2; Coq 8.18's
   `local-declaration` warning appears at the `Variable` line (file line 49). Rocq 9.1.1:
   exit 1, first error at file line 49 (`Variable R : realType.`),
   `declaration-outside-section`.
3. **Byte identity.** `tail -c 652 putnam_1978_b2.v | cmp - <upstream file>` reports no
   difference (the upstream file is 652 bytes without a trailing newline, and so is the
   body of the copy). The upstream file also matches, byte for byte (`cmp`), a fresh
   download of `coq/src/putnam_1978_b2.v` at the pinned commit. Both deliverables were
   assembled from the upstream bytes by a script (string replacement with uniqueness
   assertions), not retyped; the `diff` in section 3 is the actual output.
4. **Shape and small values** (scratch file `sanity.v` in the scratch directory, same
   imports plus `ring lra` and `Import GRing.Theory Num.Theory.`, the statement's `f`
   and conclusion restated inside a `Section`; compiles with exit 0 on **both**
   toolchains, no `Admitted`):
   * `Set Printing All. Print concl.` for `concl := (f @ \oo --> (ratr sol : R))` shows
     `@cvg_to (Real.sort R) (@nbhs _ _ (@fmap nat (Real.sort R) f (@nbhs nat _ eventually))) (@nbhs (Real.sort R) (numFieldTopology.Real_sort__canonical__filter_Filtered R) (@ratr _ sol : Real.sort R))`,
     i.e. the ordinary limit in R.
   * `sol == 7%:Q / 4%:Q` (with `sol : rat := 7/4`): `by []`.
   * `(ratr sol : R) = 7 / 4`: `rewrite fmorph_div /= !ratr_nat`.
   * `concl = cvg_to (fmap f eventually) (nbhs (7 / 4 : R))`: by the previous lemma.
   * `f 0 = 0` (`big_geq`), `f 1 = 1 / 4` and `f 2 = 59 / 120` (unfolding the big sums
     with `big_nat_recr`/`big_nat1`, then `field`), `f 2 < 7 / 4` (`lra`).
     These agree with exact rational brute force in Python: f(1) = 1/4, f(2) = 59/120,
     f(3) = 93/140.
5. **Numerical check** (`numeric.py`, scratch directory; f(n) evaluated through the exact
   closed form f(n) = sum_{i<=n} (H_n - H_{n+i+2} + H_{i+2}) / (i (i+2)), itself checked
   against brute force at n = 5 and 20): f(10) = 1.167448, f(10^2) = 1.641494,
   f(10^3) = 1.734436, f(10^4) = 1.747981, f(10^5) = 1.749752, f(10^6) = 1.749971;
   1.75 - f(n) = 5.8e-1, 1.1e-1, 1.6e-2, 2.0e-3, 2.5e-4, 2.9e-5 (decay like ln n / n).
   The partial sums increase to 7/4, consistent with the statement.
6. **Proof-sketch identities** (`closed.py`, exact rationals): for n = 1..15,
   A(n) := sum_{i<=n} H_{i+2}/(i(i+2)) equals the closed form of section 5,
   f(n) = A(n) - E(n), and 0 <= E(n) <= H_n/(n+1). All true.
7. **Non-vacuity**: the theorem has no hypotheses (only the local definition of `f`),
   so there is nothing to satisfy; the conclusion is the true theorem (sections 4.5, 5).
8. `Print Assumptions`: not applicable in this phase (both files end in `Admitted`).
   No `_statement_is_false` / `_statement_is_vacuous` file: the verdict is `compile`,
   the statement is neither false nor vacuous.
9. No AI model names in the files (grep: no hit).

**Verifier, both toolchains** (`extended/verify.sh`, run after the final edits):

* Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix),
  `(source /opt/rocq91/bin/rocq-env.sh && cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1978_b2)`:

  ```
  toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
  NOTE putnam_1978_b2.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)
  OK   putnam_1978_b2_corrected.v compiles
  OK   putnam_1978_b2_corrected.v ends in Admitted (statement only)
  OK   putnam_1978_b2.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
  checked 1 problem folder(s), 0 with a proof file
  ALL CHECKS PASSED
  ```
* Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04),
  `(cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1978_b2)`:

  ```
  toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
  NOTE putnam_1978_b2.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)
  OK   putnam_1978_b2_corrected.v compiles
  OK   putnam_1978_b2_corrected.v ends in Admitted (statement only)
  OK   putnam_1978_b2.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
  checked 1 problem folder(s), 0 with a proof file
  ALL CHECKS PASSED
  ```
  (One earlier Coq 8.18 run printed `NOTE putnam_1978_b2.v: could not download upstream
  for comparison` instead of the identity line: `verify.sh` downloads into the shared
  `extended/ci_upstream/` directory and deletes it at the end, so a concurrent verifier
  run for another problem removed it mid-run. A direct `curl` of the same URL succeeded,
  and the rerun quoted above performed the comparison.)

## 5. Difficulty estimate and proof sketch

**Difficulty: 3 / 5.** Elementary mathematics, but a fair amount of big-operator
algebra (double sums, index shifts, telescoping) and one limit argument in
MathComp-Analysis.

Write t(i,j) = 1/(i j (i+j+2)) and H_k = sum_{m=1}^{k} 1/m. Everything below reduces
the limit to finite identities plus H_n / n -> 0.

1. Partial fractions: for i, j >= 1, t(i,j) = (1/(i(i+2))) (1/j - 1/(i+j+2)).
   Summing over j = 1..n (telescoping in blocks of i+2):
   sum_{j=1}^{n} (1/j - 1/(i+j+2)) = H_{i+2} - (H_{n+i+2} - H_n).
   Hence f(n) = A(n) - E(n) with
   A(n) = sum_{i=1}^{n} H_{i+2} / (i(i+2)),
   E(n) = sum_{i=1}^{n} (H_{n+i+2} - H_n) / (i(i+2)).
2. Closed form of A(n) (by induction on n, or by splitting 1/(i(i+2)) = (1/2)(1/i -
   1/(i+2)) and H_{i+2} = H_i + 1/(i+1) + 1/(i+2)):
   A(n) = 7/4 - (1/2) [ H_{n+1}/(n+1) + H_{n+2}/(n+2) + 1/(n+1) + (1/(n+1) + 1/(n+2))/2 ].
   (Checked with exact rationals for n <= 15, section 4.6.) The constant comes from
   H_1 + H_2/2 + sum 1/(i(i+1)) + sum 1/(i(i+2)) = 1 + 3/4 + 1 + 3/4 = 7/2, halved.
3. Bound on E(n): H_{n+i+2} - H_n is a sum of i+2 terms each <= 1/(n+1), so
   0 <= E(n) <= sum_{i=1}^{n} (i+2)/((n+1) i (i+2)) = H_n/(n+1).
4. H_n/(n+1) -> 0: H_n/n is the arithmetic mean of the sequence 1/k -> 0, so Cesaro
   gives it; or use the elementary bound H_n <= 2 sqrt n (induction) and squeeze.
5. Conclude with the squeeze theorem: A(n) - H_n/(n+1) <= f(n) <= A(n), and both
   bounds tend to 7/4.

Rocq plan (names checked in the MathComp-Analysis 1.16.0 sources of the CI toolchain and
in the installed 1.0.0 sources): `cesaro` and `cvg_harmonic` (the sequence
`harmonic n = n.+1%:R^-1 -> 0`; note this is 1/(n+1), not the harmonic number) in
`sequences.v`; `squeeze_cvgr` (`normed_module.v` in 1.16.0, `normedtype.v` in 1.0.0);
`cvgD`, `cvgB`, `cvgN` (`pseudometric_normed_Zmodule.v` / `normedtype.v`), `cvgM`,
`cvg_cst`; `telescope_sumr` (`ssralg.v`/`nmodule.v`), `big_nat_recr`, `big_split`,
`exchange_big`, `big_distrr`, `ler_sum`; `field`/`lra` from algebra-tactics for the
per-term identities (denominators are casts of positive nats: `pnatr_eq0`, `ltr0n`).
First rewrite `ratr putnam_1978_b2_solution` to `7 / 4` (`fmorph_div`, `ratr_nat`,
as in section 4.4). Expected `Print Assumptions`: only `R` and the three classical
axioms of `mathcomp.classical`.

Friction points: rewriting under the binder of the inner sum (use `eq_bigr` /
`under eq_bigr`), the half-open `1 <= i < n.+1` ranges vs. `'I_n` ordinals, and keeping
the nat-to-R casts normalised (`natrD`, `natrM`, `natrX`) before calling `field`.

## 6. Status of each file

| file | status |
|---|---|
| `putnam_1978_b2.v` | upstream text verbatim after a header comment (no compat lines: it would not compile with them either). **Does not compile** on Coq 8.18.0 (error at `--> ratr ...`) nor on Rocq 9.1.1 (first error at the top-level `Variable`), by design of the `compile` verdict (section 4.2). |
| `putnam_1978_b2_corrected.v` | corrected statement, ends in `Proof. Admitted.`; **compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0**, no warning from its own lines on either; verifier ALL CHECKS PASSED on both; differs from upstream by the ascription `( ... : R)` and the marked compat lines. |
| `putnam_1978_b2_statement_is_false.v` / `_vacuous.v` | not applicable (verdict `compile`; statement faithful and true). |
| `putnam_1978_b2_corrected_proof.v` | not written in this phase (proof phase). Sketch in section 5. |
| `NOTES.md` | this file. |
