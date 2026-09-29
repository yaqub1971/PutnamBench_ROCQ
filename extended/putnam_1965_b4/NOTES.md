# putnam_1965_b4 -- notes

## 1. The problem

Putnam 1965 B4. For real `x` and positive integers `n` let

    f(x, n) = (C(n,0) + C(n,2) x + C(n,4) x^2 + ...) / (C(n,1) + C(n,3) x + C(n,5) x^2 + ...).

Express `f(x, n+1)` as a rational function of `f(x, n)` and `x`, and find
`lim_{n -> oo} f(x, n)` for all `x` for which the limit exists. Answer:
`f(x, n+1) = (f(x, n) + x) / (f(x, n) + 1)`; the limit exists exactly for `x >= 0` and equals
`sqrt x` (it diverges for `x < 0`). The benchmark encodes the answer as the tuple
`putnam_1965_b4_solution = ((fun h x => h x + x, fun h x => h x + 1), ([set x | x >= 0], Num.sqrt))`
and states: for the fixed `n > 0`, `f (n+1) x = p (f n) x / q (f n) x` wherever
`v n x`, `v (n+1) x` and `q (f n) x` are nonzero; the set of `x` at which `f . x` converges
(to a real limit) is `s`; and for `x` in `s` the limit is `g x`.

## 2. Defects of the upstream statement

Upstream (`coq/src/putnam_1965_b4.v`, commit 4dbe26e) defines numerator and denominator by

    (hu : forall n : nat, gt n 0 -> forall x : R, u n x = \sum_(0 <= i < n%/2 .+1) ('C(n, 2 * i)%:R * x^i))
    (hv : forall n : nat, gt n 0 -> forall x : R, v n x = \sum_(0 <= i < (n.-1)%/2 .+1) ('C(n, 2 * (i.+1))%:R * x^i))

Two defects, both confirmed by Rocq (the pretty-printed type of the upstream theorem, shown
by `Print Assumptions` in the evidence file, reads `\sum_(0 <= i < n %/ 3)` and
`\sum_(0 <= i < n.-1 %/ 3) 'C(n, 2 * i.+1)%:R * x ^ i`):

1. **Precedence of `.+1`.** The postfix `.+1` binds tighter than `%/`, so `n%/2 .+1` is
   `n %/ (2.+1) = n %/ 3`, not `(n %/ 2).+1`; likewise `(n.-1)%/2 .+1` is `(n.-1) %/ 3`.
   So `u n x` is the empty sum `0` for `n <= 2`, `v n x` is `0` for `n <= 3`, and both are
   truncated for larger `n` (e.g. for `n = 1..8` the upstream numerator coefficient lists are
   `[], [], [1], [1], [1], [1;15], [1;21], [1;28]`, checked by `vm_compute`, see section 4).
2. **Wrong binomials in the denominator.** `'C(n, 2 * (i.+1))` is `C(n, 2i+2)` (even
   binomials, starting at `C(n,2)`), whereas the problem has the odd ones `C(n, 2i+1)`
   (`C(n,1), C(n,3), ...`).

Consequently the upstream theorem is **false** (audit verdict: false, machine-checked). At
`n = 5`, `x = 1`, with `u, v, f` the functions that `hu, hv, hf` prescribe:
`u 5 1 = C(5,0) = 1`, `v 5 1 = C(5,2) = 10`, `u 6 1 = C(6,0) + C(6,2) = 16`,
`v 6 1 = C(6,2) = 15`; the guards `10 <> 0`, `15 <> 0`, `1/10 + 1 <> 0` hold and the
recurrence conjunct asserts `16/15 = f 6 1 = (f 5 1 + 1)/(f 5 1 + 1) = 1`.
`putnam_1965_b4_statement_is_false.v` derives `False` from the admitted upstream theorem this
way.

The rest of the statement was re-read against the whole trap list of the brief (section 7.5)
and is faithful:

* `x^i` elaborates to `exprz x (Posz i)` (checked with `Set Printing All`), i.e. `x ^+ i`, an
  integer power with the summation index as exponent (not the bound, not a real power);
  `0 ^ 0 = 1`, so `u n 0 = 1`, `v n 0 = n`, as in the problem.
* `'C(n, 2 * i)` elaborates to `binomial n (muln 2 i)` (nat arithmetic), and in the fix
  `'C(n, 2 * i + 1)` to `binomial n (addn (muln 2 i) 1)`.
* `\sum_(0 <= i < k.+1)` is `i = 0..k` inclusive (the Lean `Finset.Icc 0 k`).
* `hf : f n x = u n x / v n x`: division by zero is `0` in MathComp, as in Lean; the
  recurrence conjunct is guarded by `v n x <> 0`, `v (n+1) x <> 0`, `q (f n) x <> 0`, so it
  never relies on that convention (the third guard is implied by the first two, harmless).
* `n` with `gt n 0` is the problem's positive integer `n` (1-indexed, no shift);
  `f 0 x` is unconstrained but a single term does not affect any limit.
* `f_seq x @ \oo --> l` with `l : R` is convergence to a *finite* real limit
  (`cvg_to (fmap (f_seq x) eventually) (nbhs l)` under `Set Printing All`), which is what
  "the limit converges" means; `s = [set x | exists l : R, ...]` is an equality of sets,
  i.e. both directions ("exactly for `x >= 0`"); `x >= 0` includes `x = 0`
  (`f(0, n) = 1/n -> 0 = sqrt 0`).
* `f_seq : ... := ...` is a genuine local definition, not a hypothesis in disguise; the
  solution tuple is destructured by `let '((p, q), (s, g)) := ...` correctly.

## 3. The fix

Exactly two lines of the statement change (apart from the header comment):

    before:  (hu : forall n : nat, gt n 0 -> forall x : R, u n x = \sum_(0 <= i < n%/2 .+1) ('C(n, 2 * i)%:R * x^i))
    after:   (hu : forall n : nat, gt n 0 -> forall x : R, u n x = \sum_(0 <= i < (n%/2).+1) ('C(n, 2 * i)%:R * x^i))

    before:  (hv : forall n : nat, gt n 0 -> forall x : R, v n x = \sum_(0 <= i < (n.-1)%/2 .+1) ('C(n, 2 * (i.+1))%:R * x^i))
    after:   (hv : forall n : nat, gt n 0 -> forall x : R, v n x = \sum_(0 <= i < ((n.-1)%/2).+1) ('C(n, 2 * i + 1)%:R * x^i))

`Set Printing All` shows the new bounds as `S (divn n 2)` and `S (divn (Nat.pred n) 2)`, and
the new coefficient as `binomial n (addn (muln 2 i) 1)`. So `u n x = sum_{i=0}^{n/2} C(n,2i) x^i`
and `v n x = sum_{i=0}^{(n-1)/2} C(n,2i+1) x^i` (floor divisions), exactly the numerator and the
denominator of the problem, with all their terms (the last index is the largest `i` with
`2i <= n`, resp. `2i+1 <= n`).

Comparison with the Lean statement (`putnam_1965_b4.lean`): Lean has
`u n x = ∑ i ∈ Finset.Icc 0 (n / 2), (n.choose (2 * i)) * x ^ i` and
`v n x = ∑ i ∈ Finset.Icc 0 ((n - 1) / 2), (n.choose (2 * i + 1)) * x ^ i`; the corrected Rocq
lines are the literal transcription (`Finset.Icc 0 k` = `0 <= i < k.+1`, `n - 1` = `n.-1`
for `n > 0`, `2 * i + 1` as in Lean). Everything else in the Rocq statement (solution tuple,
recurrence conjunct with its guards, limit set, limit function) already matched the Lean
statement and is kept unchanged; no deviation from Lean remains.

Library choice, names, hypothesis order, imports and scopes are upstream's. The compat lines
(the ssralg re-import triple after the second import line, and the `Set Warnings` line before
`Variable R : realType.`) are the repository's marked ones; both are needed on Rocq 9.1 (the
raw upstream file stops with `Error: Use of "Variable" or "Hypothesis" outside sections ...`,
and with only that line added it stops at `fun x => h x + 1` with
`The term "1" has type "BaseUMagma.sort ?s" while it is expected to have type "Algebra.BaseAddMagma.sort R"`).

## 4. Sanity checks (actually run)

1. **Compilation, both toolchains**, from inside this folder, in dependency order, after
   deleting all build products between toolchains:
   * Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (`rocq compile -R . "" <file>.v`):
     `putnam_1965_b4.v`, `putnam_1965_b4_corrected.v`, `putnam_1965_b4_statement_is_false.v`
     all exit 0; every warning (30 per file) is reported at the first
     `From mathcomp Require Import all_algebra all_ssreflect.` line; none from the files' own
     lines.
   * Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (`coqc -R . "" <file>.v`): the same
     three files exit 0; 23 warnings per file, all at that same import line.
2. **Statement integrity.** `putnam_1965_b4.v` with header and marked compat lines removed
   (the `strip` filter of `extended/verify.sh`) is byte-identical to the upstream file
   (`cmp`; the upstream file has no final newline, and neither has this copy). `diff` of the
   stripped upstream copy against the stripped corrected file shows exactly the two lines of
   section 3.
3. **Evidence.** `putnam_1965_b4_statement_is_false.v` compiles on both toolchains and its
   `Print Assumptions putnam_1965_b4_rocq_statement_is_false` lists exactly: the admitted
   upstream theorem `putnam_1965_b4`, `putnam_1965_b4.R : realType`, and
   `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`,
   `boolp.constructive_indefinite_description`.
4. **Elaboration** (`Set Printing All` on the compiled corrected theorem, Rocq 9.1): bounds
   `S (divn n 2)` / `S (divn (Nat.pred n) 2)`, coefficients `binomial n (muln 2 i)` /
   `binomial n (addn (muln 2 i) 1)`, powers `exprz x (Posz i)`, limits
   `cvg_to (fmap (f_seq x) (nbhs eventually)) (nbhs l)` with `l : R`, solution set
   `mkset (fun x => 0 <= x)`, limit function `Num.sqrt`.
5. **Scratch Rocq file** `sanity.v` (in the scratch directory, not a deliverable; it
   `Require`s `putnam_1965_b4_corrected` and defines `u`, `v`, `f` by the corrected
   hypotheses' text). It compiles with exit 0 on **both** Rocq 9.1.1 and Coq 8.18.0
   (`Print Assumptions rec2`: only the three `boolp` axioms and the statement's `R`). It proves:
   * non-vacuity: `hyps_ok` (the corrected `hu`, `hv`, `hf` hold for these `u, v, f`, by
     reflexivity, and `gt 2 0`), and a `Check` that the corrected theorem instantiates with
     them at `n = 2`;
   * coefficient lists in the statement's own index ranges for `n = 1..8`
     (`vm_compute`): numerator `[1] [1;1] [1;3] [1;6;1] [1;10;5] [1;15;15;1] [1;21;35;7]
     [1;28;70;28;1]`, denominator `[1] [2] [3;1] [4;4] [5;10;1] [6;20;6] [7;35;21;1]
     [8;56;56;8]` (the rows of Pascal's triangle split into even/odd positions), and, for
     comparison, the upstream lists (numerator `[] [] [1] [1] [1] [1;15] [1;21] [1;28]`,
     denominator `[] [] [] [6] [10] [15] [21;35] [28;70]`);
   * closed forms for symbolic `x`: `u 1 x = 1`, `v 1 x = 1`, `u 2 x = 1 + x`, `v 2 x = 2`,
     `u 3 x = 1 + 3x`, `v 3 x = 3 + x`;
   * the recurrence conjunct, with the statement's guards, for symbolic `x` at `n = 1`
     (`rec1`) and `n = 2` (`rec2`), by `field`;
   * `f 3 2 = 7/5 = (f 2 2 + 2)/(f 2 2 + 1)` (`rec_2_2`, guards discharged);
   * at the upstream counterexample point: `u 5 1 = v 5 1 = 16`, `u 6 1 = v 6 1 = 32`, so
     `f 6 1 = 1 = (f 5 1 + 1)/(f 5 1 + 1)` holds for the corrected encoding (`rec_5_1`);
   * `u n 0 = 1` and `v n 0 = n` for every `n` (so `f n 0 = 1/n -> 0 = sqrt 0`).
6. **Exact arithmetic check** (`check.py`, Python `fractions`, library convention `a/0 = 0`):
   * the corrected `u, v` equal the problem's numerator/denominator (sum over even/odd `k`)
     for `n = 1..39` at 46 rational `x` (including `0, 1, 2, -1, -3, 1/4` and 40 random ones);
   * the recurrence conjunct holds in all 1749 guarded cases (`n = 1..39`, same `x`), guards
     fail in 45; for the upstream encoding it fails in all 1656 guarded cases;
   * limits: `f(x, n)` for `n` near 200 is `0.0050...` at `x = 0` (`= 1/n`), `0.500000` at
     `x = 1/4`, `1.414214` at `x = 2`, `3.000000` at `x = 9`; for `x < 0` the exact values
     oscillate: `x = -1`: `1, 0, -1, 0, 1, 0, -1, 0, ...`; `x = -3`: `1, -1, 0, 1, -1, 0, ...`;
     `x = -1/2`: range `[-180.4, 62.7]` over `n <= 300`, no convergence -- consistent with the
     answer set `{x >= 0}` and limit `sqrt x`.

## 5. Difficulty and proof sketch for a future `putnam_1965_b4_corrected_proof.v`

Difficulty: **3/5** (all elementary, no deep library fact is missing, but three separate
parts with bigop bookkeeping and several MathComp-Analysis limit arguments; a few hundred
lines).

Sketch (fix `u, v, f` by the hypotheses; write `t = sqrt x` when `x >= 0`):

1. **Widening the sums.** Since `bin_small : n < m -> 'C(n, m) = 0`, for every `N >= n%/2 + 1`
   `u n x = \sum_(0 <= i < N) 'C(n, 2 i)%:R * x ^ i`, and similarly for `v` with
   `N >= (n.-1)%/2 + 1` (`big_cat_nat` + `big1` on the tail); take `N = n.+2`.
2. **Pascal recurrences** for `n > 0`: `u n.+1 x = u n x + x * v n x` and
   `v n.+1 x = u n x + v n x`. Split off `i = 0` (`big_ltn`), shift the index
   (`big_nat_recl` / `big_add1`), use `binS : 'C(n.+1, m.+1) = 'C(n, m.+1) + 'C(n, m)`
   (`2 (i+1) = (2 i + 1).+1`, `2 i + 1 = (2 i).+1`), `big_split`, and pull `x` out
   (`mulr_sumr`, `exprSz`/`exprS`).
3. **First conjunct.** With `v n x <> 0`: `(f n x + x)/(f n x + 1) = (u + x v)/(u + v)` =
   `u n.+1 x / v n.+1 x = f n.+1 x` (`field` with the guards, or `mulf_div`/`divfK`).
4. **Norm identity** (for `x < 0`): `u n.+1^2 - x v n.+1^2 = (1 - x)(u n^2 - x v n^2)` (from
   step 2 by `ring`), base `u 1 = v 1 = 1`, so `u n^2 - x v n^2 = (1 - x)^n > 0`: `u n x` and
   `v n x` never vanish together.
5. **Divergence for `x < 0`.** Suppose `f . x --> l`. If `v n x = 0` then `f n x = 0` and
   (step 2) `v n.+1 = u n = u n.+1 <> 0`, so `f n.+1 x = 1`; two consecutive terms at distance
   1 can occur only finitely often in a convergent (Cauchy) sequence, so eventually
   `v n x <> 0`, and then `f n.+1 x * (f n x + 1) = f n x + x` (algebra from step 2). Passing
   to the limit (`cvg_shiftS`, `cvgM`, `cvgD`, `cvg_unique`) gives `l (l + 1) = l + x`, i.e.
   `l^2 = x < 0`, impossible. Hence `s` contains no negative `x`.
6. **Convergence for `x > 0`.** Splitting the binomial theorem (`exprDn`) over even/odd `k`
   gives `(1 + t)^n = u n x + t v n x` and `(1 - t)^n = u n x - t v n x`, hence (with
   `rho = (1 - t)/(1 + t)`, `|rho| < 1`, `v n x > 0`)
   `f n x - t = 2 t rho^n / (1 - rho^n)`, which tends to `0` by `cvg_expr : |z| < 1 -> z ^+ n @ \oo --> 0`
   and `cvgV`/`cvgM`. (Alternative avoiding the even/odd split: prove the two identities by
   induction from step 2.) For `x = 0`: `f n 0 = 1/n` (`u n 0 = 1`, `v n 0 = n`, already
   checked in `sanity.v`), which tends to `0 = sqrt 0` (`cvg_harmonic` up to the shift
   `n <-> n.+1`).
7. **Set equality** `[set x | x >= 0] = [set x | exists l, ...]` by `seteqP`/`eqEsubset`:
   `>=` from steps 6 (witness `sqrt x`), `<=` from step 5 (`x < 0` impossible, `real` total
   order). The last conjunct is step 6 again (`x \in s` unfolds with `inE`/`in_setE`).

Library facts needed: `bin_small`, `binS`, `exprDn`, `big_ltn`, `big_cat_nat`, `big_split`,
`mulr_sumr`, `sqr_sqrtr`, `sqrtr_ge0`; MathComp-Analysis `cvg_expr`, `cvg_harmonic`,
`cvgD`, `cvgM`, `cvgV`, `cvg_shiftS`, `cvg_unique`/`cvg_lim`, `cvgrPdist_lt` (for the
"finitely many jumps of size 1" step), and `big_nat_recl`, `big_add1`, `exprSz`, `seteqP`,
`eqEsubset`, `in_setE`. Each of these names was found (by grep for its `Lemma`/`Theorem`
declaration) both in the MathComp 2.5.0 / MathComp-Analysis 1.16.0 sources and in the Coq 8.18
installation's MathComp 2.1.0 / MathComp-Analysis 1.0.0 sources; their exact signatures were
not re-checked. Expected `Print Assumptions`: the statement's `R` and the three `boolp`
axioms.

## 6. Status of the files

| file | status |
|---|---|
| `putnam_1965_b4.v` | upstream statement + header + the four marked compat lines; compiles on Rocq 9.1.1 and Coq 8.18.0; stripped text byte-identical to upstream |
| `putnam_1965_b4_corrected.v` | corrected statement (two lines differ from upstream); ends in `Proof. Admitted.`; compiles on Rocq 9.1.1 and Coq 8.18.0 with no warnings from its own lines |
| `putnam_1965_b4_statement_is_false.v` | derives `False` from the admitted upstream theorem at `n = 5`, `x = 1`; compiles on both toolchains; `Print Assumptions` as in section 4.3 |
| `putnam_1965_b4_corrected_proof.v` | not written (proofs are out of scope in this phase) |
| `NOTES.md` | this file |

Build products (`*.vo *.vos *.vok *.glob .*.aux`) were removed from the folder after the checks.

## 7. Verifier output

`(source /opt/rocq91/bin/rocq-env.sh && cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1965_b4)`:

    toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
    OK   putnam_1965_b4.v (upstream copy) compiles
    OK   putnam_1965_b4_corrected.v compiles
    OK   putnam_1965_b4_corrected.v ends in Admitted (statement only)
    OK   putnam_1965_b4_statement_is_false.v compiles
    OK   putnam_1965_b4_statement_is_false.v: assumes the admitted upstream theorem putnam_1965_b4 (False follows from it)
    OK   putnam_1965_b4.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
    checked 1 problem folder(s), 0 with a proof file
    ALL CHECKS PASSED

(A first run on Rocq 9.1 printed `NOTE putnam_1965_b4.v: could not download upstream for
comparison` after `curl: (23) Failure writing output to destination`, apparently because a
concurrent verifier run removed the shared `extended/ci_upstream/` folder while this one was
using it; it still ended in ALL CHECKS PASSED. The re-run above did the comparison.)

`(cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1965_b4)`:

    toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
    OK   putnam_1965_b4.v (upstream copy) compiles
    OK   putnam_1965_b4_corrected.v compiles
    OK   putnam_1965_b4_corrected.v ends in Admitted (statement only)
    OK   putnam_1965_b4_statement_is_false.v compiles
    OK   putnam_1965_b4_statement_is_false.v: assumes the admitted upstream theorem putnam_1965_b4 (False follows from it)
    OK   putnam_1965_b4.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
    checked 1 problem folder(s), 0 with a proof file
    ALL CHECKS PASSED
