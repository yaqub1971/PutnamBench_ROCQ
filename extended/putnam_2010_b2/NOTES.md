# putnam_2010_b2 -- notes

## 1. The problem

Putnam 2010 B2. `A`, `B`, `C` are noncollinear points in the plane with integer coordinates
such that the distances `AB`, `AC` and `BC` are integers. What is the smallest possible value
of `AB`? The answer is **3**. It is attained by the 3-4-5 triangle `A = (0,0)`, `B = (3,0)`,
`C = (0,4)`. `AB = 1` and `AB = 2` are impossible. The reason is the strict triangle inequality
`|AC - BC| < AB`, combined with a parity argument on `AC^2 - BC^2`.

## 2. Defect of the upstream statement

Upstream (`coq/src/putnam_2010_b2.v`, commit 4dbe26e) defines

    (noncollinear: (R * R) -> (R * R) -> (R * R) -> Prop := fun A B C => let (a, b) := A in let (c, d) := B in let (e, f) := C in
        ~exists (s t : R), (s * (c - a) + t * (e - a), s * (d - b) + t * (f - b)) = (0, 0))

With `A = (a,b)`, `B = (c,d)`, `C = (e,f)` the pair is `s (B - A) + t (C - A)`. The body says
that no pair `(s, t)` makes it vanish. But `s = t = 0` always does, so `noncollinear A B C` is
**false for every** `A, B, C`. As a result `p A B C` (whose first conjunct is `noncollinear A B C`)
never holds. The hypothesis

    (hm : exists (A B C: R * R), p A B C /\ dist A B = m)

is unsatisfiable, and the theorem is provable for any value of `putnam_2010_b2_solution` with
no mathematics. This is the audit verdict (vacuous, machine-checked).
`putnam_2010_b2_statement_is_vacuous.v` proves the verbatim upstream theorem in two tactic lines.

The rest of the statement was re-read against the trap list of the brief (section 7.5) and
found faithful:

* `putnam_2010_b2_solution := 3` is a real number. The file opens `R` scope, and
  `Check putnam_2010_b2_solution` prints `: R`. It is also forced by `m = putnam_2010_b2_solution`
  with `m : R`. No `nat`/`Z` numeral slip.
* `dist` is `dist_euc a b c d = sqrt (Rsqr (a - c) + Rsqr (b - d))` from `Rgeom`, the Euclidean
  distance. There is no missing square root and no `pow` with a wrong exponent.
* `int_val P` means `P = (IZR x, IZR y)` for integers `x`, `y`: integer coordinates. The three
  distance conditions are `dist = IZR z` for integers: integer distances `AB`, `AC`, `BC`,
  exactly the three of the problem.
* All of `dist`, `int_val`, `noncollinear` and `p` are genuine definitions used as such (`:=`),
  and `m`, `hm`, `hmlb` are genuine binders. No hypothesis is disguised as a local definition.
* "Smallest possible value of `AB`" is encoded as: for every `m` that is attained (`hm`) and is
  a lower bound (`hmlb`, `dist A B >= m`), `m = 3`. The Lean statement uses the stronger-looking
  `IsLeast {AB | ...} 3`. The two are equivalent here, because the set of attainable `AB` is a
  nonempty (3-4-5) set of positive integers and so has a least element. This is the usual
  PutnamBench Rocq shape for "smallest value", and it was kept (minimal diff).
* `>=` in `hmlb` is right (a non-strict lower bound).

The only defect is the one the audit names.

## 3. The fix

One line of the statement changes (the body of `noncollinear`):

    before:          ~exists (s t : R), (s * (c - a) + t * (e - a), s * (d - b) + t * (f - b)) = (0, 0))
    after:           ~exists (s t : R), (s <> 0 \/ t <> 0) /\ (s * (c - a) + t * (e - a), s * (d - b) + t * (f - b)) = (0, 0))

Now `noncollinear A B C` says that no nontrivial combination `s (B - A) + t (C - A)`, with
`(s, t) <> (0, 0)`, vanishes. In other words, `B - A` and `C - A` are linearly independent,
which holds exactly when `A`, `B`, `C` are not collinear. As in the problem, it also excludes
coincident points (`A = B` gives `s = 1, t = 0`). This is the meaning of the Lean statement's
`¬Collinear ℝ {A, B, C}`: Mathlib calls three points collinear when they lie on a common line,
and that includes coincident points. `Set Printing All` on the compiled corrected theorem shows the
new body as `not (ex s, ex t, and (or (not (s = IZR Z0)) (not (t = IZR Z0))) (pair ... = pair ...))`.
So the `exists` scopes over both conjuncts and the `0` is the real zero, as intended.

Everything else is upstream's: the same `Require`/`Open Scope` lines, the same solution
definition, the same theorem name and binders in the same order, the same conclusion. No
compat lines are needed in any file, because the files use only the standard library. The Lean
statement is followed in substance: its noncollinearity, integer coordinates, integer `AB`,
`AC`, `BC`, and answer 3. The file deviates from it only in keeping upstream's
"attained + lower bound implies `m = 3`" shape instead of `IsLeast` (see section 2).

## 4. Sanity checks

Toolchains: Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix, the
primary one) and Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1
(Ubuntu 24.04).

1. Compilation, from inside this folder, in the order upstream copy, corrected file, evidence
   file. The build products were deleted between the two toolchains.
   * Rocq 9.1.1 (`rocq compile -R . "" <file>.v`): all three exit 0. Each file emits only three
     warnings, "Loading Stdlib without prefix is deprecated" for `Reals`, `Rgeom` and `ZArith`,
     all at its `Require Import Reals Rgeom ZArith.` line. No warning comes from the files' own lines.
   * Coq 8.18.0 (`coqc -R . "" <file>.v`): all three exit 0 with no warnings at all.
2. Statement integrity: running `diff` between the upstream file and the header-stripped
   corrected file shows exactly the one line quoted in section 3. The verifier (item 6) checks
   that the header-stripped upstream copy is identical to PutnamBench 4dbe26e.
3. Evidence: `putnam_2010_b2_statement_is_vacuous.v` is the verbatim upstream statement closed by
   `destruct hm as [[a b] [[c d] [[e f] [[hnc _] _]]]]. exfalso; apply hnc; exists 0, 0; f_equal; ring.`
   It compiles on both toolchains. On both, its `Print Assumptions putnam_2010_b2` lists only
   `ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec` and
   `FunctionalExtensionality.functional_extensionality_dep`, the axioms behind the standard
   library's reals, which `ring` uses for `0 * x + 0 * y = 0`.
4. Non-vacuity and small cases: `sanity.v` is in the scratch directory and is not a deliverable.
   It restates the corrected `dist`, `int_val`, `noncollinear` and `p` as top-level
   `Definition`s, copied character for character from the corrected binders. It compiles with
   exit 0 on both toolchains, and proves:
   * `witness : p (0, 0) (3, 0) (0, 4) /\ dist (0, 0) (3, 0) = 3`. The integer distances are
     `AB = 3`, `AC = 4`, `BC = 5`, via `sqrt_square`. Noncollinearity reduces to `3 s = 0 /\ 4 t = 0`
     contradicting `s <> 0 \/ t <> 0` (`lra`). So `hm` is satisfiable with `m = 3`, and
     `hmlb`'s bound at `m = 3` is attained.
   * `collinear_rejected : ~ noncollinear (0, 0) (1, 1) (2, 2)` (witness `s = 2, t = -1`) and
     `degenerate_rejected : ~ noncollinear (0, 0) (0, 0) (5, 7)` (witness `s = 1, t = 0`). The
     corrected predicate does reject collinear and degenerate triples.
   * `zero_excluded : ~ p (0, 0) (0, 0) (3, 4)`. This triple has integer coordinates and integer
     distances 0, 5, 5, and would give `AB = 0` without the noncollinearity condition. The
     corrected `p` excludes it, so the statement does not collapse to `m = 0`.
   * `up_never : forall A B C, ~ noncollinear_up A B C`, with the upstream body: the defect
     itself, as a lemma.
   * `Print Assumptions witness`: only the three standard-library real-number axioms.
   The corrected statement is not trivially true. Its content is the lower bound `AB >= 3`, a
   genuine number-theoretic fact (see section 5).
5. Elaboration check: `Set Printing All` / `Check` of the compiled corrected theorem, on Rocq
   9.1.1. The result is quoted in section 3.
6. Verifier, run after all edits, verdict lines quoted verbatim:
   * `(source /opt/rocq91/bin/rocq-env.sh && cd extended && bash verify.sh putnam_2010_b2)`,
     toolchain `The Rocq Prover, version 9.1.1  (rocq compile)`:

         OK   putnam_2010_b2.v (upstream copy) compiles
         OK   putnam_2010_b2_corrected.v compiles
         OK   putnam_2010_b2_corrected.v ends in Admitted (statement only)
         OK   putnam_2010_b2_statement_is_vacuous.v compiles
         OK   putnam_2010_b2_statement_is_vacuous.v: only library axioms / the statement's R: ClassicalDedekindReals.sig_not_dec ClassicalDedekindReals.sig_forall_dec FunctionalExtensionality.functional_extensionality_dep
         OK   putnam_2010_b2.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
         ALL CHECKS PASSED

   * `(cd extended && bash verify.sh putnam_2010_b2)`, toolchain
     `The Coq Proof Assistant, version 8.18.0  (coqc)`:

         OK   putnam_2010_b2.v (upstream copy) compiles
         OK   putnam_2010_b2_corrected.v compiles
         OK   putnam_2010_b2_corrected.v ends in Admitted (statement only)
         OK   putnam_2010_b2_statement_is_vacuous.v compiles
         OK   putnam_2010_b2_statement_is_vacuous.v: only library axioms / the statement's R: ClassicalDedekindReals.sig_not_dec ClassicalDedekindReals.sig_forall_dec FunctionalExtensionality.functional_extensionality_dep
         OK   putnam_2010_b2.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
         ALL CHECKS PASSED

## 5. Difficulty and proof sketch for `putnam_2010_b2_corrected_proof.v`

Difficulty: **3/5**. The mathematics is elementary. The work lies in moving from the real-number
encoding (`sqrt`, `IZR`, pairs destructured by `let`) to a pure integer problem, and then in a
finite case split closed by `nia`/`lia`.

Sketch (standard library only; `Lra`, `Lia`, and `Psatz` for `nia`):

1. **Upper bound (`m <= 3`)**: apply `hmlb` to the witness `(0,0), (3,0), (0,4)`, as in
   `sanity.v` (`sqrt_square`, `lra`). This gives `3 >= m`.
2. **Transfer to integers**: from `hm` obtain `A, B, C` with `p A B C` and `m = dist A B`.
   Destructure `int_val` to get `A = (IZR a1, IZR a2)` and so on. Set `u = B - A = (p1, q1)` and
   `v = C - A = (x, y)` in `Z`. From `dist A B = IZR k` obtain `IZR (p1^2 + q1^2) = IZR k ^ 2`
   and `0 <= IZR k`, using `sqrt_pos`, `pow2_sqrt`/`sqrt_sqrt` and `plus_IZR`/`mult_IZR`, then
   `eq_IZR` and `le_IZR`. The same gives `x^2 + y^2 = l^2` and `(x - p1)^2 + (y - q1)^2 = n^2`
   with `l, n >= 0`. Noncollinearity implies `p1 * y - q1 * x <> 0` in `Z`. Proof by
   contraposition: if the cross product is 0, the pair `s = IZR x, t = - IZR p1` works when
   `(x, p1) <> (0, 0)`, and otherwise `s = IZR y, t = - IZR q1` or `s = 1, t = 0` does; each case
   is closed by `lra`/`nra` after `IZR` rewriting. In particular `k <> 0`.
3. **Integer lemma**: if `k >= 0`, `p1^2 + q1^2 = k^2`, `x^2 + y^2 = l^2`,
   `(x-p1)^2 + (y-q1)^2 = n^2`, `l, n >= 0` and `p1 y - q1 x <> 0`, then `k >= 3`.
   * `k = 0` contradicts the cross product.
   * `k = 1`: `(p1, q1)` is one of `(±1, 0)`, `(0, ±1)` (`nia` from the bounds `|p1|, |q1| <= 1`).
     By symmetry take `(1, 0)`. Then `y <> 0` and `l^2 - n^2 = 2x - 1` is odd, so `l <> n`. If
     `l >= n + 1`, then `2x - 1 >= 2n + 1`, so `n <= x - 1` and `n^2 <= (x-1)^2 < (x-1)^2 + y^2 = n^2`.
     The case `n >= l + 1` is symmetric. Each step is `nia` with the right hints.
   * `k = 2`: `(p1, q1)` is one of `(±2, 0)`, `(0, ±2)` (the sums of two squares equal to 4). Take
     `(2, 0)`. Then `l^2 - n^2 = 4x - 4`. If `l = n`, then `x = 1` and `1 + y^2 = l^2`, which
     forces `y = 0` (`(l-y)(l+y) = 1`) and contradicts noncollinearity. If `|l - n| = 1`, then
     `l + n = |4x - 4|` is even while `l + n = 2 min(l, n) + 1` is odd. If `|l - n| >= 2`, it
     contradicts the strict triangle inequality `|l - n| < 2`, which follows as in the `k = 1`
     case from `y <> 0`.
   * A uniform alternative for `k <= 2` is `16 * Area^2 = 4 k^2 l^2 - (k^2 + l^2 - n^2)^2 =
     4 (p1 y - q1 x)^2 > 0`. This gives `|l - n| < k` and `l + n > k`, followed by the parity
     argument.
4. **Conclusion**: `m = IZR k` with `k >= 3` gives `m >= 3`, and step 1 gives `m <= 3`, so `m = 3`
   (`lra`).

Library facts: `sqrt_square`, `sqrt_pos`, `sqrt_sqrt`, `pow2_sqrt`, `Rsqr_sqrt`, `IZR` ring
morphism lemmas (`plus_IZR`, `mult_IZR`, `minus_IZR`, `opp_IZR`), `eq_IZR`, `le_IZR`, `lt_IZR`,
and `lia`/`nia`/`lra`/`nra`. Expected `Print Assumptions`: only the three standard-library
real-number axioms, plus `Classical_Prop.classic` if a classical case split is used.

## 6. Status of the files

| file | status |
|---|---|
| `putnam_2010_b2.v` | upstream statement + header comment, no compat lines; compiles on Rocq 9.1.1 and Coq 8.18.0; header-stripped text identical to upstream 4dbe26e (verifier) |
| `putnam_2010_b2_corrected.v` | corrected statement, one line differs from upstream; compiles on Rocq 9.1.1 (warnings only at the `Require` line) and Coq 8.18.0 (no warnings); ends in `Proof. Admitted.` |
| `putnam_2010_b2_statement_is_vacuous.v` | upstream theorem verbatim, proved from the contradiction in `hm` alone; compiles on Rocq 9.1.1 and Coq 8.18.0; `Print Assumptions` lists only the three standard-library real-number axioms |
| `putnam_2010_b2_corrected_proof.v` | not written in this phase (proof phase) |
| `NOTES.md` | this file |

Build products (`*.vo *.vos *.vok *.glob .*.aux`) were removed from the folder after the checks.
