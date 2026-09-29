# putnam_1979_a6 -- notes

Audit verdict: **naming** (plus a weakening of the bound, noted in the same audit row).
Upstream commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 of PutnamBench, file
`coq/src/putnam_1979_a6.v`. Files in this folder: `putnam_1979_a6.v` (upstream copy, evidence),
`putnam_1979_a6_corrected.v` (proposed fix, ends in `Proof. Admitted.`), this file. No
`_statement_is_false` / `_statement_is_vacuous` file: the upstream statement is neither false nor
vacuous (section 2).

## 1. The problem

Putnam 1979 A6. Let `p_0, ..., p_(n-1)` be points of `[0, 1]` (the original text indexes them
`p_1, ..., p_n` and writes the bound as `8n * sum_(i=1)^n 1/(2i - 1)`; the PutnamBench informal
statement re-indexes from 0). Prove that some `x` in `[0, 1]` satisfies

    sum_(i = 0)^(n-1) 1/|x - p_i|  <=  8n * sum_(i = 0)^(n-1) 1/(2i + 1).

(Implicitly `x` differs from every `p_i`, so that each term is a real number.) The informal
file gives no solution.

## 2. Defect(s) in the upstream statement

The upstream text (kept verbatim, after a header comment and four marked compat lines, in
`putnam_1979_a6.v`) is

```coq
Variable R : realType.
Theorem putnam_1979_b6
    (p : seq R)
    (hp : all (fun x => 0 <= x <= 1) p)
    : exists x : R, 0 <= x <= 1 /\ (all (fun i => x != i) p) /\ (\sum_(i <- p) 1/`|x - i|) <= 8*(size p)%:R*(\sum_(0 <= i < (size p).+1) (1%R)/(2*(i%:R) + 1)).
Proof. Admitted.
```

**Defect 1 (naming, the audit verdict).** The theorem is called `putnam_1979_b6`, the name of a
different problem (1979 B6), instead of `putnam_1979_a6`.

**Defect 2 (weakening, also in the audit row).** The inner sum of the bound is
`\sum_(0 <= i < (size p).+1)`, i.e. over `i = 0, ..., n` (`n + 1` terms, `n = size p`), instead of
`i = 0, ..., n - 1`. The extra term `1/(2n + 1)` enlarges the right-hand side by `8n/(2n + 1)` for
every `n >= 1`: for `n = 1` the upstream bound is `8 * (1 + 1/3) = 32/3` while the problem's is `8`
(both values machine-checked, section 4). So the upstream theorem is strictly weaker than the
problem. It is still TRUE (it follows from the problem's statement, machine-checked implication
in section 4), hence not false; its only hypothesis `hp` is satisfiable (e.g. `p = [:: 0; 1/2; 1]`,
checked), hence not vacuous. Therefore no evidence file.

**Re-reading the whole statement against the trap list of the brief (section 7.5):** no further
defect.

* The left-hand side `\sum_(i <- p) 1/`|x - i|` sums `1/|x - p_i|` over the entries of the list
  `p` (repetitions allowed, as in the problem). Absolute value present.
* Division by zero: in MathComp `1/0 = 0`, so without a side condition `x = p_i` would silently
  drop a term (for one point, `x = p_0` would give left-hand side `0`; checked as `why_neq`,
  section 4). The upstream conjunct `all (fun i => x != i) p` excludes this, exactly as the Lean
  statement's `∀ i ∈ Finset.range n, x ≠ p i`. It only strengthens the claim. Kept.
* `0 <= x <= 1` and `hp : all (fun x => 0 <= x <= 1) p` are the closed interval `[0, 1]`
  (not `<`).
* `8*(size p)%:R*(...)` is `8 * n * (...)`; all numerals, `%:R` casts and `/` are in `ring_scope`
  on `R`; `2*(i%:R) + 1` is `2i + 1` on `R` (no `nat` division or subtraction, no `^`, no
  logarithm, no series, no `sup`).
* The index of the bound's sum is used (`i%:R`), not the bound. The only indexing issue is the
  upper limit `(size p).+1` (defect 2).
* `n = 0` (empty `p`): both sides are `0`, `x = 0` works; the problem has no `n >= 1` hypothesis
  to add or remove, and the statement is not weakened by allowing `n = 0`.

**Rocq 9.1 / MathComp 2.5 compatibility (not a mathematical defect).** The verbatim upstream file
does not compile on the CI toolchain: Rocq 9.1.1 rejects the top-level `Variable R : realType.`
("Use of "Variable" or "Hypothesis" outside sections behaves as "#[local] Parameter" or
"#[local] Axiom"."); with only that compat line added, it then stops at the `1` of `x <= 1`
("The term "1" has type "BaseUMagma.sort ?s" while it is expected to have type ...", MathComp
2.5's `all_ssreflect` imported after `all_algebra` overrides the ring notation `1`). Hence both
files carry compat kinds (1) (three lines after the upstream import lines) and (2) (one line
before `Variable R`). The verbatim upstream file compiles on Coq 8.18.0 / MathComp 2.1.0 (with
the usual library warnings plus a `local-declaration` warning at the `Variable` line).

## 3. The fix

`putnam_1979_a6_corrected.v` differs from `putnam_1979_a6.v` (header comments and the identical
`(* compat: *)` lines removed) in exactly two lines:

```diff
-Theorem putnam_1979_b6
+Theorem putnam_1979_a6
     (p : seq R)
     (hp : all (fun x => 0 <= x <= 1) p)
-    : exists x : R, 0 <= x <= 1 /\ (all (fun i => x != i) p) /\ (\sum_(i <- p) 1/`|x - i|) <= 8*(size p)%:R*(\sum_(0 <= i < (size p).+1) (1%R)/(2*(i%:R) + 1)).
+    : exists x : R, 0 <= x <= 1 /\ (all (fun i => x != i) p) /\ (\sum_(i <- p) 1/`|x - i|) <= 8*(size p)%:R*(\sum_(0 <= i < (size p)) (1%R)/(2*(i%:R) + 1)).
```

(`diff` output: `11c11` and `14c14`; on line 14 only `(size p).+1` -> `(size p)` changes.)

Why it is faithful: the bound is now `8n * sum_(i = 0)^(n-1) 1/(2i + 1)`, which is the informal
statement's bound and, after the shift `i -> i + 1`, the original competition's
`8n * sum_(i=1)^n 1/(2i - 1)`. Everything else was re-checked (section 2) and kept.

Comparison with the Lean statement (`putnam_1979_a6.lean`):

```lean
theorem putnam_1979_a6 (n : ℕ) (p : ℕ → ℝ) (hp : ∀ i ∈ Finset.range n, p i ∈ Icc 0 1) :
    ∃ x ∈ Icc 0 1, (∀ i ∈ Finset.range n, x ≠ p i) ∧
      ∑ i ∈ Finset.range n, 1/|x - p i| ≤ 8*n*∑ i ∈ Finset.range n, (1 : ℝ)/(2*i + 1)
```

The corrected Rocq statement agrees with it conjunct by conjunct: `Finset.range n` (`0..n-1`)
corresponds to `\sum_(0 <= i < size p)` for the bound and to `\sum_(i <- p)` / `all ... p` over
the `n = size p` entries of the list for the points. The only representational difference is
kept from upstream: the points are a list `p : seq R` rather than a function `ℕ → ℝ` restricted
to `range n`, which is equivalent (any finite family of points is a list and conversely).

## 4. Sanity checks run (scratch files under the work directory, not in this folder)

All of the following were compiled on BOTH toolchains (Rocq 9.1.1 / MathComp 2.5.0 /
MathComp-Analysis 1.16.0 and Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0), exit 0:

1. Compilation of the two deliverables in this folder (details and verifier output in section 6):
   `rocq compile -R . "" putnam_1979_a6.v` and `... putnam_1979_a6_corrected.v`: exit 0, all 30
   warnings at the first import line (library warnings), none from the files' own lines. Coq
   8.18.0 (`coqc`, after deleting the `.vo` files): exit 0, all 23 warnings at the first import
   line. The raw upstream file (no compat lines) fails on Rocq 9.1.1 with the `Variable` error
   quoted in section 2 and, with only the `Variable` compat line, with the `1` error; it compiles
   on Coq 8.18.0.
2. `sanity.v` (a `Section` with `Variable R : realType` and two definitions `concl_corr p` and
   `concl_up p` whose bodies are the corrected and the upstream conclusions copied verbatim):
   * `corr_implies_up : concl_corr p -> concl_up p`: the corrected conclusion implies the upstream
     one (`big_nat_recr` and nonnegativity of the extra term). Proved, `Print Assumptions`: only
     `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`,
     `boolp.constructive_indefinite_description`.
   * `rhs1_corr`: for `p = [:: 0]` the corrected right-hand side equals `8`; `rhs1_up`: the
     upstream right-hand side equals `32/3`. Proved (shows the two statements really differ).
   * `inst1 : concl_corr [:: 1/2]` (witness `x = 0`: `1/|0 - 1/2| = 2 <= 8`) and
     `inst2 : concl_corr [:: 0; 1]` (witness `x = 1/2`: `2 + 2 = 4 <= 8*2*(1 + 1/3) = 64/3`).
     Proved: small instances of the corrected statement hold, with a point `x` distinct from all
     `p_i`.
   * `why_neq (a : R) : \sum_(i <- [:: a]) 1/`|a - i| = 0`: proved; shows that without the
     conjunct `x != p_i` the statement would be trivial for one point (MathComp's `1/0 = 0`).
   * `hp_sat : all (fun x : R => 0 <= x <= 1) [:: 0; 1/2; 1]`: proved; the hypothesis is
     satisfiable (non-vacuity).
3. `link.v` (`Require sanity putnam_1979_a6 putnam_1979_a6_corrected.`): the terms
   `putnam_1979_a6_corrected.putnam_1979_a6 hp : sanity.concl_corr p` and
   `putnam_1979_a6.putnam_1979_b6 hp : sanity.concl_up p` type-check, i.e. the definitions used in
   `sanity.v` are, by conversion, exactly the two theorems' conclusions; and
   `corr_to_up := fun p hp => sanity.corr_implies_up (link_corr p hp) : sanity.concl_up p` derives
   the upstream conclusion from the admitted corrected theorem. `Print Assumptions corr_to_up`:
   `putnam_1979_a6_corrected.putnam_1979_a6`, `putnam_1979_a6_corrected.R` and the three `boolp`
   axioms.

## 5. Difficulty and proof sketch

Difficulty for a full Rocq proof: **4** (a genuine combinatorial construction with a covering
argument and a summation-by-parts estimate; no deep analysis, but a lot of finite bookkeeping over
`seq R`, floors and big operators).

Proof sketch (one route; the constants have been checked on paper). Let `n = size p >= 1`
(`n = 0`: take `x = 0`). Put `h = 1/(2n)` and split `[0, 1]` into the `2n` cells
`C_k = [k h, (k+1) h]`, `k = 0..2n-1`, with midpoints `x_k = (k + 1/2) h`; assign each `p_i` to one
cell (e.g. `k = min(floor(2n p_i), 2n - 1)`), and let `c_k` be the number of points in `C_k`.
For a cell `m` let `N_m(r)` be the number of points in the cells `k` with `|k - m| <= r`.

1. *Good cell.* Call `m` good if `N_m(r) <= 2r` for all `r >= 0` (for `r = 0`: `C_m` is empty).
   A good cell exists: otherwise every `m` has a window `W_m = [m - r_m, m + r_m]` with at least
   `2 r_m + 1 >= |W_m ∩ {0..2n-1}|` points. These windows cover the `2n` cells; by the 1-D
   covering lemma choose a subfamily covering all cells with every cell in at most two chosen
   windows. Then `2n <= sum |W_i ∩ cells| <= sum (points in W_i) <= 2n`, and the first
   inequality is an equality only if the chosen windows are disjoint, in which case the last
   sum is `<= n < 2n`. Contradiction.
2. *Distances.* Take `x = x_m` for a good `m`. Then `x ∈ [0, 1]`; a point in cell `k != m` is at
   distance `>= (|k - m| - 1/2) h >= h/2 > 0` from `x` (so `x != p_i`), hence
   `sum_i 1/|x - p_i| <= 4n * sum_(k != m) c_k / (2|k - m| - 1)`.
3. *Summation by parts.* With `w(d) = 1/(2d - 1)` decreasing and `N_m(r) <= min(2r, n)`,
   `sum_(k != m) c_k w(|k - m|) = sum_(r >= 1) N_m(r) (w(r) - w(r+1)) <= sum_(r >= 1) min(2r, n)
   (w(r) - w(r+1)) <= 2 sum_(r = 1)^(ceil(n/2)) w(r) <= 2 sum_(j = 1)^n 1/(2j - 1)`.
4. Hence `sum_i 1/|x - p_i| <= 8n sum_(j=1)^n 1/(2j - 1) = 8n sum_(i=0)^(n-1) 1/(2i + 1)`.

Library facts needed: `floor` on a `realType` (`Num.floor`/`floorP` style lemmas in MathComp
2.5 / `archimedean`), big-operator manipulation over `seq` and `nat` ranges (`big_nat_recr`,
`partition_big`/`big_mkcond`, `ler_sum`), `ler_pdivrMr`-style division inequalities, and a
hand-written discrete covering lemma (induction on the number of windows) and Abel summation
over `nat` ranges; nothing from `ftc` or topology is required, so the proof should be
achievable on both toolchains.

## 6. Status of each file

| file | status |
|---|---|
| `putnam_1979_a6.v` | upstream statement verbatim (apart from the header and 4 marked compat lines; `strip` of the header and compat lines gives the upstream file byte-for-byte, modulo the missing final newline that upstream also lacks). Compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04). |
| `putnam_1979_a6_corrected.v` | corrected statement (`Proof. Admitted.`). Compiles on both toolchains, no warning from its own lines. |
| evidence file | none (upstream statement is true and not vacuous; section 2). |
| `putnam_1979_a6_corrected_proof.v` | not written (out of scope for this phase). |

Verifier output (`bash verify.sh putnam_1979_a6`), Rocq 9.1.1 (script sourced):

```
toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
### putnam_1979_a6
OK   putnam_1979_a6.v (upstream copy) compiles
OK   putnam_1979_a6_corrected.v compiles
OK   putnam_1979_a6_corrected.v ends in Admitted (statement only)
curl: (23) Failure writing output to destination
NOTE putnam_1979_a6.v: could not download upstream for comparison
checked 1 problem folder(s), 0 with a proof file
ALL CHECKS PASSED
```

Coq 8.18.0 (plain PATH):

```
toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
### putnam_1979_a6
OK   putnam_1979_a6.v (upstream copy) compiles
OK   putnam_1979_a6_corrected.v compiles
OK   putnam_1979_a6_corrected.v ends in Admitted (statement only)
curl: (23) Failure writing output to destination
NOTE putnam_1979_a6.v: could not download upstream for comparison
checked 1 problem folder(s), 0 with a proof file
ALL CHECKS PASSED
```

The verifier could not fetch the upstream file in this sandbox (the `NOTE` line), so its step 4
was replaced by the same comparison run by hand against the local verbatim copy of the upstream
file at the pinned commit: `diff <(awk '{print}' upstream/coq/putnam_1979_a6.v) <(strip
putnam_1979_a6.v)` with the verifier's own `strip` function prints nothing (identical).
