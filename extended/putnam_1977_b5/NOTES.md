# putnam_1977_b5 -- notes

## 1. The problem

Putnam 1977 B5. Let `a_1, ..., a_n` be real numbers with `n > 1`, and let `A` satisfy

    A + sum_{i=1}^n a_i^2 < (1/(n-1)) * (sum_{i=1}^n a_i)^2.

Prove that `A < 2 a_i a_j` for all `i, j` with `1 <= i < j <= n`.
(PutnamBench gives no informal solution. A proof is sketched in section 5.)

## 2. Defect of the upstream statement

Upstream (`coq/src/putnam_1977_b5.v`, commit 4dbe26e):

    Variable R : realType.
    Theorem putnam_1977_b5
        (a : seq R)
        (A : R)
        (ha : gt (size a) 1)
        (hA : A + \sum_(i <- a) (i ^+ 2) <= 1/((size a)%:R - 1) * (\sum_(i <- a) i) ^+ 2)
        : pairwise (fun x y => A < 2 * x * y) a.

The hypothesis `hA` uses `<=`. The problem (and the Lean statement) has a strict `<`.
With the non-strict hypothesis the theorem is **false** (audit verdict: false,
machine-checked). Take `n = 2`, `a = (1, 1)`, `A = 2`. Then the hypothesis holds with
equality: `2 + (1 + 1) = 4 = 1/(2 - 1) * (1 + 1)^2`. The conclusion asserts
`2 < 2 * 1 * 1`, which is false. `putnam_1977_b5_statement_is_false.v` derives `False`
this way.

I re-read the rest of the statement against the trap list of the brief (section 7.5) and
found it faithful:

* `ha : gt (size a) 1` is the `nat` comparison `size a > 1`. `Set Printing All` shows
  `gt (@size _ a) (S O)`, so the `1` is the `nat` 1 even under `ring_scope`. This is
  `n > 1` with `n = size a`.
* `1/((size a)%:R - 1)` is the field division of `R`, with `(size a)%:R - 1 >= 1 > 0`
  under `ha`. So there is no `nat` division, no division by 0, and no `int` arithmetic.
* `i ^+ 2` is the ring power with a `nat` exponent 2. That is the intended square.
* Both `\sum_(i <- a)` range over all entries of `a`, i.e. `i = 1..n`. There is no
  index/bound confusion and no inclusive-range slip.
* `pairwise (fun x y => A < 2 * x * y) a` is MathComp's `pairwise`:
  `pairwise r (x :: s) = all (r x) s && pairwise r s`. It holds iff `r (nth i) (nth j)`
  for all positions `i < j < size a` (lemma `pairwiseP`). That is exactly "for all
  `1 <= i < j <= n`". The conclusion is strict, as in the problem.
* There are no local `:=` definitions, `Q` equalities, limits, series, logarithms or
  real exponents in the statement.
* A side effect of the upstream `Set Implicit Arguments` is that `a` and `A` are implicit
  arguments of the theorem. This changes nothing mathematically.

The only defect is the non-strict `<=` in `hA`.

## 3. The fix

Apart from the header comment, `putnam_1977_b5_corrected.v` differs from `putnam_1977_b5.v`
(the upstream copy, which has the same compat lines) in exactly one line:

    -    (hA : A + \sum_(i <- a) (i ^+ 2) <= 1/((size a)%:R - 1) * (\sum_(i <- a) i) ^+ 2)
    +    (hA : A + \sum_(i <- a) (i ^+ 2) < 1/((size a)%:R - 1) * (\sum_(i <- a) i) ^+ 2)

* This is the strict inequality of the informal statement. The Lean statement has the
  same strict hypothesis: `hA : A + ∑ i : Fin n, (a i)^2 < (1/((n : ℝ) - 1))*(∑ i : Fin n, a i)^2`.
  Lean encodes the numbers as `a : Fin n → ℝ` with the conclusion
  `∀ i j : Fin n, i < j → A < 2*(a i)*(a j)`. The Rocq statement uses `a : seq R` with
  `n = size a` and `pairwise`. The two say the same thing, so I kept upstream's
  encoding.
* Under `Set Printing All` on Rocq 9.1, the types of the upstream and the corrected
  theorem differ only by `@Order.le` becoming `@Order.lt` in `hA` (apart from the module
  prefix of `R`). I checked this with a diff of the two printed types.
* Nothing is weakened. A strict hypothesis is what the problem assumes, no hypothesis is
  removed, and the conclusion is unchanged.

Compat lines (the same in all three files, copied from the root files):

* The `Set Warnings "-declaration-outside-section,-local-declaration"` line before
  `Variable R : realType.` is needed. Without it the upstream file fails on Rocq 9.1.1 at
  that line with "Use of "Variable" or "Hypothesis" outside sections behaves as
  "#[local] Parameter" or "#[local] Axiom"" (checked on the raw upstream file).
* The three ssralg re-import lines are needed too. With only the Variable compat line,
  the file fails on Rocq 9.1.1 at the `1` of `1/((size a)%:R - 1)` with "The term "1" has
  type "BaseUMagma.sort ?s1" while it is expected to have type ..." (checked).
* On Coq 8.18.0 both are no-ops, except that the Variable line also silences the
  `local-declaration` warning that the raw upstream file emits there. The raw upstream
  file compiles on Coq 8.18.0 with that one extra warning (checked).

## 4. Sanity checks (all actually run)

Toolchains: (a) Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4
(Nix, `/opt/rocq91`); (b) Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 /
Coquelicot 3.4.1 (Ubuntu 24.04). The build products were deleted between the two.

1. **Compilation** from inside this folder, in dependency order (`putnam_1977_b5.v`,
   `putnam_1977_b5_corrected.v`, `putnam_1977_b5_statement_is_false.v`). All three exit 0 on
   both toolchains. The only warnings are at each file's first import line
   (`From mathcomp Require Import all_algebra all_ssreflect.`): 30 warnings on (a), 23 on
   (b), all from MathComp itself. None come from the files' own lines.
2. **Raw upstream:** on (a) it fails at `Variable R` (see section 3). On (b) it compiles,
   with the extra `local-declaration` warning at line 10.
3. **Evidence file:** `Print Assumptions putnam_1977_b5_rocq_statement_is_false` prints
   (on both toolchains) the admitted upstream theorem `putnam_1977_b5`, the three
   `boolp` axioms (`propositional_extensionality`, `functional_extensionality_dep`,
   `constructive_indefinite_description`) and the Variable `putnam_1977_b5.R : realType`.
   Nothing else is printed.
4. **Statement diff:** `Set Printing All` types of the upstream and corrected theorems
   were diffed on (a). The only change is `Order.le` -> `Order.lt`.
5. **Scratch checks of the corrected statement** (a scratch file that `Require`s the
   corrected file, compiled on (a) and (b); not part of the deliverables):
   * non-vacuity: `a = [1; 1]`, `A = 1` satisfies `ha` and the strict `hA`
     (`1 + 2 < 4`), proved with `lra`. The conclusion `1 < 2*1*1` holds there.
   * not trivial: for `a = [1; 1]`, `A = 3`, the conclusion `pairwise (A < 2xy)` is false
     (proved). So the hypothesis is doing work.
   * `n = 3`, `a = [1; 1; 1]`: from the corrected `hA` (`A + 3 < 9/2`) the conclusion
     follows (proved with `lra`).
   * the corrected statement for all `n = 2` instances, `a = [x; y]` with arbitrary
     `x, y, A`: proved with `nra` (`hA` reads `A + x^2 + y^2 < (x+y)^2`, i.e.
     `A < 2xy`).
6. **Verifier** (`extended/verify.sh putnam_1977_b5`), run under both toolchains:

   Rocq 9.1.1 (`source /opt/rocq91/bin/rocq-env.sh && bash verify.sh putnam_1977_b5`):

       toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
       OK   putnam_1977_b5.v (upstream copy) compiles
       OK   putnam_1977_b5_corrected.v compiles
       OK   putnam_1977_b5_corrected.v ends in Admitted (statement only)
       OK   putnam_1977_b5_statement_is_false.v compiles
       OK   putnam_1977_b5_statement_is_false.v: assumes the admitted upstream theorem putnam_1977_b5 (False follows from it)
       OK   putnam_1977_b5.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
       ALL CHECKS PASSED

   Coq 8.18.0 (`bash verify.sh putnam_1977_b5`):

       toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
       OK   putnam_1977_b5.v (upstream copy) compiles
       OK   putnam_1977_b5_corrected.v compiles
       OK   putnam_1977_b5_corrected.v ends in Admitted (statement only)
       OK   putnam_1977_b5_statement_is_false.v compiles
       OK   putnam_1977_b5_statement_is_false.v: assumes the admitted upstream theorem putnam_1977_b5 (False follows from it)
       OK   putnam_1977_b5.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
       ALL CHECKS PASSED

## 5. Difficulty and proof sketch

Difficulty: **2 / 5** (elementary; the work is list bookkeeping in MathComp).

Math: fix positions `i < j`. Apply Cauchy–Schwarz (or QM–AM) to the `n - 1` numbers
`a_i + a_j` and `a_k` (`k ≠ i, j`):

    (sum_k a_k)^2 = ((a_i + a_j) + sum_{k≠i,j} a_k)^2
                 <= (n - 1) * ((a_i + a_j)^2 + sum_{k≠i,j} a_k^2)
                  = (n - 1) * (sum_k a_k^2 + 2 a_i a_j).

Dividing by `n - 1 > 0` gives `(1/(n-1)) (sum a)^2 - sum a^2 <= 2 a_i a_j`, and with the
strict `hA`, `A < 2 a_i a_j`.

Rocq plan:
1. `apply/(pairwiseP 0) => i j Hi Hj Hij` (MathComp `seq.pairwiseP`) turns the goal into
   `A < 2 * nth 0 a i * nth 0 a j` for `i < j < size a`.
2. Split the sums: with `x = nth 0 a i`, `y = nth 0 a j`, and `b` the list `a` with
   positions `i` and `j` removed, show `perm_eq a (x :: y :: b)` (e.g. via
   `perm_to_rem`/`rem`, or by `take`/`drop` decomposition: `cat_take_drop`, `drop_nth`).
   Then `perm_big` gives `\sum_(k <- a) f k = f x + f y + \sum_(k <- b) f k`, and
   `size b = size a - 2`.
3. Cauchy–Schwarz for a list: `(\sum_(k <- c) k)^2 <= (size c)%:R * \sum_(k <- c) k^2`,
   by induction on `c` (`big_cons`, then `nra`-style algebra using
   `2 s x <= (m) x^2 + s^2 / m`, or more simply the identity
   `m * S2 - S1^2 = (1/2) sum_{k,l} (c_k - c_l)^2`). Apply it to `c = (x + y) :: b`.
4. Conclude with `ltr_pdivlMl`/`mulrC` rewrites to clear `1/(n-1)` (`n - 1 > 0` from
   `ha` via `ltr1n`/`subr_gt0`), then `lra`/`nra`.

Library facts: `pairwiseP`, `perm_big`, `perm_to_rem` (or `cat_take_drop`, `drop_nth`),
`big_cons`, `size_rem`, `ltr_pdivlMl` / `ler_pdivlMl`, `natrB`, `lra`/`nra` from
algebra-tactics. The whole proof should be well under 100 lines.

## 6. Status of each file

| file | status |
|---|---|
| `putnam_1977_b5.v` | upstream statement verbatim + header + marked compat lines; compiles on (a) and (b); ends in `Admitted` |
| `putnam_1977_b5_corrected.v` | corrected statement (one line changed: `<=` -> `<` in `hA`); compiles on (a) and (b) with no warnings from its own lines; ends in `Admitted` |
| `putnam_1977_b5_statement_is_false.v` | derivation of `False` from the upstream theorem (`n = 2`, `a = (1, 1)`, `A = 2`); compiles on (a) and (b); `Print Assumptions` as in section 4 |
| `putnam_1977_b5_corrected_proof.v` | not written (proofs are out of scope for this phase) |
