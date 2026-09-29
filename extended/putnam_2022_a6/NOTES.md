# putnam_2022_a6 -- notes

Audit verdict: **vacuous (machine-checked)**. Upstream commit
4dbe26ef21563af851eedaeb82d936fe1f94fc52 of PutnamBench, file `coq/src/putnam_2022_a6.v`.

## 1. The problem

Putnam 2022 A6. Let n be a positive integer. Determine the largest integer m such that there
exist reals -1 < x_1 < x_2 < ... < x_{2n} < 1 for which the sum of the lengths of the n
intervals [x_1^(2k-1), x_2^(2k-1)], [x_3^(2k-1), x_4^(2k-1)], ..., [x_{2n-1}^(2k-1), x_{2n}^(2k-1)]
equals 1 for every integer k with 1 <= k <= m. Answer: **m = n**.

In the Rocq statement the problem's n is called `N`, the statement's `n := mul N 2` is the
number of points (2N), and `s : 'I_n -> R` lists x_1, ..., x_{2N} as `s` at the ordinals
0, ..., 2N-1 (`nth i0 (enum 'I_n) j` is the ordinal j for j < n).

## 2. Defects in the upstream statement

The upstream text (kept verbatim, after a header comment, in `putnam_2022_a6.v`) is

```coq
Require Import Nat Reals Coquelicot.Hierarchy. From mathcomp Require Import div fintype seq ssralg ssrbool ssrnat ssrnum .
Definition putnam_2022_a6_solution := fun n : nat => n.
Theorem putnam_2022_a6
    (N : nat)
    (M : nat)
    (n := mul N 2)
    (i0 : 'I_n)
    (sumIntervals : ('I_n -> R) -> nat -> R := fun s k => sum_n (fun i => (((s (nth i0 (enum 'I_n) (i+1))))^(2*k-1) - ((s (nth i0 (enum 'I_n) i)))^(2*k-1))) (n-1))
    (valid : nat -> ('I_n -> R) -> Prop := fun m s => forall (k: nat), and (le 1 k) (le k m) -> sumIntervals s k = 1)
    (hvalid : nat -> Prop := fun m => exists (s : 'I_n -> R), (forall (i : 'I_n),  (s i < s (ordS i)) /\ s (nth i0 (enum 'I_n) 0) > -1 /\ s (nth i0 (enum 'I_n) (n-1)) < 1) -> valid m s)
    (hM : hvalid M)
    (hMub : forall m : nat, hvalid m -> le m M)
    : M = putnam_2022_a6_solution n.
Proof. Admitted. 
```

(`Set Printing All` on this machine confirms that everything lives in the standard-library
reals: `sum_n` is Coquelicot's over `R_AbelianMonoid`, `^` is `Rpow_def.pow` with the `nat`
exponent `subn (muln 2 k) 1`, `<` is `Rlt`, and `lt`/`le` on indices are Peano's.)

1. **Vacuous (the audited defect).** `hvalid m` is
   `exists s, (ordering conditions) -> valid m s`. Any `s` that violates the ordering makes
   the implication true; the constant `s = 0` fails `s i0 < s (ordS i0)` (0 < 0). So
   `hvalid m` holds for every `m`, and `hMub (S M)` gives `S M <= M`. Machine-checked in
   `putnam_2022_a6_statement_is_vacuous.v`: the upstream Theorem verbatim, closed by a
   three-line proof that uses only this contradiction.
2. **Unsatisfiable ordering.** `forall i, s i < s (ordS i)` uses `ordS`, the *cyclic*
   successor on `'I_n` (`ordS` of the last ordinal is 0). A cyclic strict chain
   s 0 < s 1 < ... < s (n-1) < s 0 is impossible, so even with `/\` in place of `->` no
   `s` would qualify and the set of valid m would be empty (the statement would then be
   vacuous through `hM` instead).
3. **Wrong interval sum.** `sum_n f (n-1)` is inclusive: it adds the 2N consecutive
   differences s(x_{i+1})^(2k-1) - s(x_i)^(2k-1) for i = 0..2N-1, a telescoping sum, and at
   i = 2N-1 it reads `nth i0 (enum 'I_n) (2N)`, out of range, which returns the default
   `i0`. The problem sums only the N differences x_{2i}^(2k-1) - x_{2i-1}^(2k-1)
   (i = 1..N), the lengths of the N intervals.
4. **Wrong answer.** The conclusion `M = putnam_2022_a6_solution n` applies the identity
   solution to `n = 2N`, i.e. claims the answer 2N. The answer is N (the problem's n).

Re-reading against the rest of the trap list (brief section 7.5): no `nat` division; the
`nat` exponent of `pow` is right here (the exponents 2k-1 are odd naturals, and `pow`
handles negative bases correctly, unlike `Rpower`); `2*k-1` in `nat` is fine because
k >= 1; `n-1` and `N-1` are fine because N >= 1 (see below); strict inequalities as in the
problem; `sumIntervals`, `valid`, `hvalid` are local *definitions* by design and `hM`,
`hMub` are genuine hypotheses; no `Series`, limits, integrals, `sup`, `Q`, `int`.
Positivity of the problem's n: there is no explicit `N > 0`, but the binder `i0 : 'I_n`
requires an inhabitant of `'I_(2N)`, which exists iff N >= 1, so the hypothesis is present
implicitly (for N = 0 the theorem is trivially true, as it must be since the problem
excludes n = 0). "Largest integer m" is encoded over `nat`: every negative integer has the
property trivially (no k to check), and the answer n >= 1 is a natural, so this is harmless.

## 3. The fix

`putnam_2022_a6_corrected.v` differs from the upstream text in exactly three lines (no
compat lines are needed: the file does not use MathComp ring notations or a top-level
`Variable`, and compiles unchanged on Rocq 9.1):

```diff
-    (sumIntervals : ('I_n -> R) -> nat -> R := fun s k => sum_n (fun i => (((s (nth i0 (enum 'I_n) (i+1))))^(2*k-1) - ((s (nth i0 (enum 'I_n) i)))^(2*k-1))) (n-1))
+    (sumIntervals : ('I_n -> R) -> nat -> R := fun s k => sum_n (fun i => (((s (nth i0 (enum 'I_n) (2*i+1))))^(2*k-1) - ((s (nth i0 (enum 'I_n) (2*i))))^(2*k-1))) (N-1))
-    (hvalid : nat -> Prop := fun m => exists (s : 'I_n -> R), (forall (i : 'I_n),  (s i < s (ordS i)) /\ s (nth i0 (enum 'I_n) 0) > -1 /\ s (nth i0 (enum 'I_n) (n-1)) < 1) -> valid m s)
+    (hvalid : nat -> Prop := fun m => exists (s : 'I_n -> R), (forall (i : 'I_n),  (forall (j : 'I_n), lt i j -> s i < s j) /\ s (nth i0 (enum 'I_n) 0) > -1 /\ s (nth i0 (enum 'I_n) (n-1)) < 1) /\ valid m s)
-    : M = putnam_2022_a6_solution n.
+    : M = putnam_2022_a6_solution N.
```

Why this is faithful:

* `sumIntervals s k` is now sum_{i=0}^{N-1} (s_{2i+1}^(2k-1) - s_{2i}^(2k-1)) (0-indexed
  points, `sum_n` inclusive up to N-1), i.e. sum_{i=1}^{N} (x_{2i}^(2k-1) - x_{2i-1}^(2k-1))
  in the problem's 1-indexing: the total length of the N intervals. All indices are
  <= 2N-1, so the default `i0` of `nth` is never used.
* `hvalid m` now says: there is `s` that is strictly increasing
  (`forall i j, i < j -> s i < s j`), with x_1 = s 0 > -1 and x_{2N} = s (2N-1) < 1, AND
  satisfying the interval condition for k = 1..m (`valid m s`, unchanged). The two end
  conditions stay inside `forall (i : 'I_n), ...` as upstream had them; since `'I_n` is
  inhabited (by `i0`), `forall i, (A i /\ B /\ C)` is equivalent to
  `(forall i, A i) /\ B /\ C`, so this is exactly -1 < x_1 < ... < x_{2N} < 1.
* The conclusion states the answer N.
* The shape `hM : hvalid M`, `hMub : forall m, hvalid m -> m <= M`, conclusion
  `M = answer` is upstream's and is kept (minimal diff). The set {m | hvalid m} is
  downward closed and equals {0, ..., N}, so it has a greatest element and the statement
  holds for exactly one value of the solution; proving it requires both halves of the
  problem (hMub at N needs a configuration for m = N; hM needs the bound M <= N).
* Lean comparison: `IsGreatest {m | ∃ x : ℕ → ℝ, StrictMono x ∧ -1 < x 1 ∧ x (2 * n) < 1 ∧
  ∀ k ∈ Icc 1 m, ∑ i ∈ Icc 1 n, (x (2 * i) ^ (2 * k - 1) - x (2 * i - 1) ^ (2 * k - 1)) = 1} n`.
  The corrected Rocq statement describes the same set (Lean's `x` is 1-indexed on all of
  ℕ, strictly monotone everywhere, which is equivalent after restricting/extending; the
  Rocq `s` is a finite 0-indexed family). It deviates from Lean only in keeping upstream's
  "M greatest implies M = answer" shape instead of `IsGreatest`, and in keeping `N`
  positive implicitly through `i0` (Lean: `hn : 0 < n`).

## 4. Sanity checks actually run

All files compiled on both toolchains: Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis
1.16.0 / Coquelicot 3.4.4 (Nix, `rocq compile -R . ""`) and Coq 8.18.0 / MathComp 2.1.0 /
MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04, `coqc -R . ""`), deleting the
`.vo` files between toolchains.

1. **Compilation, no own-line warnings.** `putnam_2022_a6.v`, `putnam_2022_a6_corrected.v`,
   `putnam_2022_a6_statement_is_vacuous.v` all exit 0 on both toolchains. Every warning in
   the logs points at the single import line (Rocq 9.1: 27 warnings incl. "Loading Stdlib
   without prefix is deprecated", ambiguous coercion paths, overridden notations, hidden
   scope keys; Coq 8.18: 25). No warning at any other line.
2. **Byte identity.** The body of `putnam_2022_a6.v` after the header (and the blank line
   after it) is byte-identical to the upstream file (`cmp` reports no difference); the
   corrected file was produced from the upstream bytes by five exact string replacements
   (each asserted to occur once), and `diff` shows only the three lines of section 3.
3. **Elaboration.** `Set Printing All. Check putnam_2022_a6.` on the corrected module shows
   `sum_n` over `R_AbelianMonoid` of `Rminus (pow (s (nth i0 (enum ..) (addn (muln 2 i) 1))) (subn (muln 2 k) 1)) (pow (s (nth i0 (enum ..) (muln 2 i))) ..)`
   up to `subn N 1`, the ordering `forall j, lt (nat_of_ord i) (nat_of_ord j) -> Rlt (s i) (s j)`,
   and the conclusion `@eq nat M (putnam_2022_a6_solution N)`.
4. **Vacuity of the upstream statement** (evidence file): the upstream Theorem verbatim is
   closed by `exfalso; apply (Nat.nle_succ_diag_l M); apply hMub; exists (fun _ => 0); ...`.
   `Print Assumptions putnam_2022_a6` prints only `ClassicalDedekindReals.sig_forall_dec`
   and `FunctionalExtensionality.functional_extensionality_dep` (stdlib reals axioms,
   reached through `Rlt_irrefl`), on both toolchains.
5. **The corrected statement PROVED at N = 1** (scratch file `sanity_N1.v`, not part of the
   deliverables): the corrected Theorem's binders copied verbatim (checked with `grep -xF`)
   plus an extra hypothesis `hN1 : N = 1`, proved `M = putnam_2022_a6_solution N`
   (i.e. M = 1). Upper half: two intervals-worth of conditions x_2 - x_1 = 1 and
   x_2^3 - x_1^3 = 1 force x_1 (x_1 + 1) = 0, impossible for -1 < x_1 < x_2 < 1 (`nra`).
   Lower half: s = (-1/2, 1/2) is a configuration for m = 1. A second lemma
   `hyps_hold_at_N1_M1` proves `hvalid 1 /\ forall m, hvalid m -> m <= 1` at N = 1: the
   hypotheses hM, hMub are satisfiable (M = 1), so the corrected statement is not vacuous,
   and with upstream's answer (solution applied to 2N = 2) the conclusion 1 = 2 would be
   false. Compiles (exit 0) on Rocq 9.1.1 and on Coq 8.18.0; `Print Assumptions` of both
   lemmas: `sig_forall_dec`, `functional_extensionality_dep` only.
6. **The configuration for m = N at N = 2** (scratch file `sanity_N2.v`): with the
   corrected let-binders verbatim and `hN2 : N = 2`, proved `hvalid 2` using
   x = (-b, -a, a, b), a = (sqrt 5 - 1)/4, b = (sqrt 5 + 1)/4 (this is the construction
   x_j = -cos(j pi / 5)): strictly increasing, -1 < -b, b < 1, and the new pairing sum gives
   2(b - a) = 1 (k = 1) and 2(b^3 - a^3) = 1 (k = 2). This exercises the (2i, 2i+1)
   pairing with more than one interval. Compiles on Rocq 9.1.1 and Coq 8.18.0;
   `Print Assumptions`: `sig_not_dec`, `sig_forall_dec`, `functional_extensionality_dep`.
7. **Verifier** (quoted verdict lines):

   Rocq 9.1.1 (`source /opt/rocq91/bin/rocq-env.sh && cd extended && bash verify.sh putnam_2022_a6`):
   ```
   toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
   OK   putnam_2022_a6.v (upstream copy) compiles
   OK   putnam_2022_a6_corrected.v compiles
   OK   putnam_2022_a6_corrected.v ends in Admitted (statement only)
   OK   putnam_2022_a6_statement_is_vacuous.v compiles
   OK   putnam_2022_a6_statement_is_vacuous.v: only library axioms / the statement's R: ClassicalDedekindReals.sig_forall_dec FunctionalExtensionality.functional_extensionality_dep
   OK   putnam_2022_a6.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
   ALL CHECKS PASSED
   ```
   Coq 8.18.0 (`cd extended && bash verify.sh putnam_2022_a6`):
   ```
   toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
   OK   putnam_2022_a6.v (upstream copy) compiles
   OK   putnam_2022_a6_corrected.v compiles
   OK   putnam_2022_a6_corrected.v ends in Admitted (statement only)
   OK   putnam_2022_a6_statement_is_vacuous.v compiles
   OK   putnam_2022_a6_statement_is_vacuous.v: only library axioms / the statement's R: ClassicalDedekindReals.sig_forall_dec FunctionalExtensionality.functional_extensionality_dep
   OK   putnam_2022_a6.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
   ALL CHECKS PASSED
   ```
   (A first Coq 8.18 run printed `NOTE putnam_2022_a6.v: could not download upstream for
   comparison` after a transient `curl: (23) Failure writing output`; the rerun quoted
   above performed the comparison and passed.)

## 5. Difficulty estimate and proof sketch

**Difficulty: 5 / 5** (an A6: both halves need real ideas, and the Rocq side needs
integration or polynomial-antiderivative bookkeeping, a sign-change/orthogonality argument
and trigonometric sums).

Write E = union of the intervals [x_{2i-1}, x_{2i}] and P_k(t) = (2k-1) t^(2k-2). The
condition for k is sum_i (x_{2i}^(2k-1) - x_{2i-1}^(2k-1)) = 1, i.e.
integral over E of P_k = 1 = integral over [0, 1] of P_k; by linearity, for every even
polynomial P of degree <= 2m-2, integral_E P = integral_0^1 P.

* **Upper bound m <= n.** Let phi(t) = 1_E(t) + 1_E(-t) - 1 on (0, 1). Then
  integral_0^1 phi(t) Q(t^2) dt = 0 for every polynomial Q of degree <= m-1. phi takes
  values in {-1, 0, 1}, equals -1 near t = 1 (E is inside (-1, 1)), and only jumps at the
  points |x_j|, by a total variation of at most 2n; each sign change of phi (from +1 to -1
  or back) costs variation 2, so phi changes sign at most n times on (0, 1), at points
  0 < c_1 < ... < c_r < 1 with r <= n. If m >= n+1 take Q(u) = prod_{l=1}^{r} (u - c_l^2)
  (degree r <= n <= m-1): phi(t) Q(t^2) has constant sign and is not a.e. zero, so its
  integral is nonzero, a contradiction. (Discrete variant avoiding measure theory:
  integral_E P for a polynomial P is sum_i (G(x_{2i}) - G(x_{2i-1})) with G an
  antiderivative, and the sign argument can be run on the finitely many subintervals
  cut out by the points +-x_j and +-c_l.)
* **Existence for m = n.** Take x_j = -cos(j pi / (2n+1)), j = 1..2n (strictly increasing,
  in (-1, 1)); with x_0 = -1 the condition for k becomes
  sum_{j=0}^{2n} (-1)^j x_j^p = 0 for p = 2k-1. Since p is odd, (-1)^j x_j^p =
  -cos^p(j (2n+2) pi / (2n+1)) and j -> j (n+1) permutes the residues mod 2n+1, so the sum
  is -sum_{j=0}^{2n} cos^p(2 pi j / (2n+1)); expanding cos^p theta into cos(q theta) with
  q odd, 0 < q <= p < 2n+1, each sum_j cos(2 pi q j / (2n+1)) vanishes (roots of unity,
  or the telescoping identity 2 sin(pi q/N) sum_j cos(2 pi q j/N) = 0). For n = 1 this is
  (-1/2, 1/2), for n = 2 the witness of check 6.

Rocq plan and library facts: stay with standard-library reals / Coquelicot as the
statement does. Useful: Coquelicot `sum_n`, `sum_Sn`, `sum_O`, `sum_n_m` lemmas;
`RInt`, `RInt_Chasles`, `is_RInt_derive`/`RInt_Derive` for polynomial antiderivatives
(or avoid integrals entirely with explicit antiderivatives and `pow` algebra);
MathComp `nth_enum_ord`, `ltn_ord`, `ltP` to move between ordinals and naturals; a
polynomial with prescribed roots can be a `fold_right` product of `(u - c)` over a
`list R`; the sign-change count needs an induction over the sorted breakpoints.
Existence needs stdlib trigonometry (`cos`, `sin`, `cos_plus`, `sin_minus`, `PI` facts,
`cos_decreasing_1` for monotonicity) and the power-reduction formula for odd powers of
cosine, the most tedious part. Expected `Print Assumptions`: only
`ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec`,
`FunctionalExtensionality.functional_extensionality_dep` (plus `Classical_Prop.classic`
if a classical lemma is used).

## 6. Status of each file

| file | status |
|---|---|
| `putnam_2022_a6.v` | upstream text byte-identical after a header comment (no compat lines needed). Compiles on Rocq 9.1.1 and Coq 8.18.0. Vacuous (and unfaithful: wrong interval sum, cyclic ordering, answer 2N). |
| `putnam_2022_a6_corrected.v` | corrected statement, ends in `Proof. Admitted.`; three statement lines changed (section 3); compiles on Rocq 9.1.1 and Coq 8.18.0 with no own-line warnings. Instance N = 1 proved and N = 2 configuration checked in scratch files (section 4). |
| `putnam_2022_a6_statement_is_vacuous.v` | upstream Theorem verbatim closed by a proof using only the contradiction; compiles on both toolchains; `Print Assumptions`: two stdlib-reals axioms only. |
| `putnam_2022_a6_corrected_proof.v` | not written (proofs are out of scope for this phase). Sketch in section 5. |
| `NOTES.md` | this file. |
