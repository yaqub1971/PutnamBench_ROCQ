# putnam_2015_b4 -- notes

Audit verdict: **compile** (one-token fix; statement otherwise faithful). Upstream commit
4dbe26ef21563af851eedaeb82d936fe1f94fc52 of PutnamBench, file `coq/src/putnam_2015_b4.v`.

## 1. The problem

Putnam 2015 B4. Let T be the set of all triples (a, b, c) of positive integers for which
there exist triangles with side lengths a, b, c. Express
sum_{(a,b,c) in T} 2^a / (3^b 5^c) as a rational number in lowest terms. The answer is
**17/21**.

## 2. Defect(s) in the upstream statement

The upstream file (kept verbatim, after a header comment, in `putnam_2015_b4.v`) is

```coq
Variable R : realType.
Definition putnam_2015_b4_solution : int * int := (17%Z, 21%Z).
Theorem putnam_2015_b4
    (tri_fun : nat -> nat -> nat -> R := fun i j k : nat =>
        if (ltn i (Nat.add j k)) && (ltn j (Nat.add i k)) && (ltn k (Nat.add i j)) then (2 ^+ i) / ((3 ^+ j * 5 ^+ k)) else 0)
    (f : nat -> R := fun n : nat =>
        \sum_(1 <= i < n)
        (\sum_(1 <= j < n)
        (\sum_(1 <= k < n)
        (tri_fun i j k))))
    (C : rat)
    (hf : (fun n : nat => f n) @ \oo --> ratr C)
    : (numq C, denq C) = putnam_2015_b4_solution.
Proof. Admitted.
```

**Defect (the audited one): it does not compile.** The target of `-->` in `hf` is
`ratr C`. `F --> y` is `cvg_to (nbhs F) (nbhs y)`, so `y` must live in a filtered
(topological) type; `ratr C` is only known to live in *some* unit ring (the codomain of
`ratr` is implicit), and the two unification problems have no common solution. On
Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 the error is (upstream line 25,
characters 41-47; line 65 of the copy with its header):

```
The term "ratr C" has type "GRing.UnitRing.sort ?R"
while it is expected to have type "Filtered.sort ?s".
```

This is the same defect the audit lists for 1966 A3, 1966 A6, 1969 B3, 1978 B2 and
2021 B2 (`--> <numeral or ratr ...>` without a type ascription).

**Re-reading the whole statement against the trap list of the brief (section 7.5):**
no further defect.

* Triangle condition: `ltn i (Nat.add j k) && ltn j (Nat.add i k) && ltn k (Nat.add i j)`
  is the three STRICT triangle inequalities on `nat` (no `nat` subtraction anywhere), i.e.
  a non-degenerate triangle, which is what "there exist triangles with side lengths a, b,
  c" means and what the answer 17/21 requires. (Check 5 below: with non-strict
  inequalities the cube partial sums at n = 60 are about 2.3333, not 17/21 = 0.8095.)
* Term: `2 ^+ i / (3 ^+ j * 5 ^+ k)` is `2^a / (3^b 5^c)` in `R` (`^+` with a `nat`
  exponent is exactly right here: the exponents are the integer sides). a <-> i, b <-> j,
  c <-> k in the right roles (check 4 evaluates the terms).
* Index ranges: `\sum_(1 <= i < n)` etc. range over 1..n-1: positive integers only, no
  0 side, and the bound `n` is used only as a bound, never inside the summand. Because
  the upper bound is exclusive, f n is the sum over the cube [1, n-1]^3; the terms are
  nonnegative and the cubes exhaust all triples, so lim f n is the sum over T (exhaustion
  by cubes is legitimate for a nonnegative series; no conditional-convergence issue).
* Limit: `(fun n => f n) @ \oo --> (ratr C : R)` is the ordinary limit in `R`
  (check 3 prints it), not a `+oo`-admitting notion; there is no `Series`/`sum_n`,
  `sup`, `Rpower`/`ln`, `exprz`, `int` division or `Q`-Leibniz-equality trap: C is a
  MathComp `rat` (a canonical reduced representation), `ratr` its image in `R`.
* Conclusion: `(numq C, denq C) = (17%Z, 21%Z)` in `int * int` (`%Z` is MathComp's
  `int_scope`, `Delimit Scope int_scope with Z` in `ssrint.v`). `numq`/`denq` are the
  numerator and positive denominator of the reduced form, so this says "C = 17/21 in
  lowest terms", exactly the problem's request (check 2: 34/42 gives the same pair, 17/20
  does not).
* Shape: the statement is "for every rational C, if the partial sums converge to C, then
  C = 17/21". It does not separately assert that the series converges; this is the
  usual PutnamBench encoding of "compute the sum" (the audit rated it faithful) and it is
  not vacuous: the series does converge to the rational 17/21 (check 5 and section 5), so
  the hypotheses are satisfiable with C = 17/21, and any proof has to establish
  f n --> 17/21 and use uniqueness of limits. Kept as upstream (minimal diff).
* `tri_fun` and `f` are `(x : T := ...)` local definitions that are *meant* as
  definitions (not hypotheses); `hf` is a genuine hypothesis. Theorem name and
  `_solution` name match the problem (no `naming` issue).

**Rocq 9.1 / MathComp 2.5 compatibility (not a mathematical defect):** the upstream text
has the two constructs the repository README documents as fatal on the CI toolchain:
`Variable R : realType.` outside a `Section` (an error since Rocq 9.0; under Rocq 9.1.1
compiling the upstream copy stops exactly there, line 54 of the copy, with
`Error: Use of "Variable" or "Hypothesis" outside sections behaves as "#[local] Parameter"
or "#[local] Axiom". [declaration-outside-section,vernacular,default]`, so on the CI
toolchain the `--> ratr C` error is not even reached; Coq 8.18 only warns there) and the
import order `all_algebra all_ssreflect` (MathComp 2.5's `all_ssreflect` overrides the
ring notations `1` and `%:R`). The corrected file carries the repository's marked compat
lines for both.

## 3. The fix

`putnam_2015_b4_corrected.v` differs from the upstream text in exactly one statement
token (the ascription), plus the marked compat lines (output of `diff upstream body`):

```diff
 From mathcomp Require Import reals normedtype sequences topology.
+Set Warnings "-notation-overridden". (* compat: ... *)
+From mathcomp Require Import ssralg. (* compat: ... *)
+Set Warnings "notation-overridden". (* compat: restore the default. *)
 From mathcomp Require Import classical_sets.
 ...
+Set Warnings "-declaration-outside-section,-local-declaration". (* compat: ... *)
 Variable R : realType.
 ...
-    (hf : (fun n : nat => f n) @ \oo --> ratr C)
+    (hf : (fun n : nat => f n) @ \oo --> (ratr C : R))
```

(The ssralg compat block sits after the second import line and before
`From mathcomp Require Import classical_sets.`, as in the root file `putnam_1962_a2.v`
and in `extended/putnam_1966_a3`.) Both files were assembled by a script from the
upstream bytes, not retyped.

Why the corrected statement is faithful: the ascription `(ratr C : R)` only tells Coq the
type of the limit; `hf` becomes "the partial sums f n converge to the real number C",
which is what the upstream author meant. Everything else is upstream's text, already
faithful (section 2). Nothing is weakened; no hypothesis is added or dropped.

Comparison with the Lean statement (`putnam_2015_b4.lean`):

```lean
abbrev putnam_2015_b4_solution : ℤ × ℕ := sorry -- (17, 21)
theorem putnam_2015_b4 (quotientof : ℚ → (ℤ × ℕ)) (hquotientof : ∀ q : ℚ, quotientof q = (q.num, q.den))
: quotientof (∑' t : (Fin 3 → ℤ), if (∀ n : Fin 3, t n > 0) ∧ t 0 < t 1 + t 2 ∧ t 1 < t 2 + t 0 ∧ t 2 < t 0 + t 1
then 2^(t 0)/(3^(t 1)*5^(t 2)) else 0) = putnam_2015_b4_solution
```

Same triangle condition (positive entries, strict inequalities), same term, same answer
read off as (numerator, denominator) = (17, 21). The Rocq statement differs in form: it
uses the limit of cube partial sums instead of `tsum` and quantifies over the rational C
with a convergence hypothesis instead of asserting the value of the sum directly. For a
nonnegative summable family both describe the same number, so the two are equivalent
formalisations of the problem; the corrected file keeps upstream's Rocq form (minimal
diff) and deviates from the Lean statement only in this encoding.

## 4. Sanity checks actually run

Two toolchains: **Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot
3.4.4** (Nix, `/opt/rocq91`, the CI toolchain) and **Coq 8.18.0 / MathComp 2.1.0 /
MathComp-Analysis 1.0.0 / Coquelicot 3.4.1** (Ubuntu 24.04).

1. **Compilation of the two deliverables** (from inside the problem folder, `.vo` files
   deleted between toolchains):
   * Rocq 9.1.1, `rocq compile -R . "" putnam_2015_b4_corrected.v`: exit 0; all 30
     warnings in the log point at line 42 (the upstream
     `From mathcomp Require Import all_algebra all_ssreflect.` line: `all_ssreflect`
     deprecation, ambiguous coercion paths, overridden notations); no warning and no error
     at any other line.
   * Coq 8.18.0, `coqc -R . "" putnam_2015_b4_corrected.v`: exit 0; all 23 warnings point
     at line 42 (same import line); nothing at any other line.
   * Upstream copy `putnam_2015_b4.v`: Rocq 9.1.1 exit 1, first error at line 54
     (`Variable R : realType.`, `declaration-outside-section`); Coq 8.18.0 exit 1, error at
     line 65 characters 41-47 (the `ratr C` of `hf`), text as quoted in section 2, plus
     the `local-declaration` warning at line 54. This matches the audit's build log.
   * Byte identity: `tail -c 973 putnam_2015_b4.v | cmp - upstream/coq/putnam_2015_b4.v`
     reports no difference (the upstream file is 973 bytes without a trailing newline).
2. **Answer encoding** (scratch file `work/putnam_2015_b4/sanity.v`, compiled with exit 0
   on BOTH Rocq 9.1.1 and Coq 8.18.0; it repeats the upstream imports with the ssralg
   compat block and adds `ring lra`):
   `(numq (17%:Q / 21%:Q), denq (17%:Q / 21%:Q)) = putnam_2015_b4_solution` and the same
   for `34%:Q / 42%:Q` close by `vm_compute`; `(numq (17%:Q / 20%:Q), denq (17%:Q / 20%:Q))
   <> putnam_2015_b4_solution` closes by `vm_compute`. So the conclusion holds exactly
   when C = 17/21, whatever representation of C one starts from.
3. **Shape of hf** (same file, inside a `Section` with `Variable R : realType` and `Let`
   copies of `tri_fun` and `f` taken verbatim from the statement):
   `Definition concl C := (fun n : nat => f n) @ \oo --> (ratr C : R)` elaborates, and
   `Set Printing All. Print concl.` (Rocq 9.1.1) shows
   `cvg_to (nbhs (fmap (fun n => f n) (nbhs eventually))) (nbhs (ratr C : Real.sort R))`
   (with `numFieldTopology.Real_sort__canonical__filter_Filtered R` as the filter
   structure), i.e. the ordinary limit in `R`;
   `concl C = cvg_to (fmap f eventually) (nbhs (ratr C : R))` closes by `reflexivity`.
4. **Small values of f** (same file, both toolchains): `f 2 = 2 / 15` and
   `f 3 = 68 / 225` are proved (`rewrite /f /tri_fun unlock /=`, then `field`). The goal
   after unfolding `f 3` is
   `2/(3*5) + 2/(3*3*(5*5)) + (2*2/(3*(5*5)) + (2*2/(3*3*5) + 2*2/(3*3*(5*5)))) = 68/225`,
   i.e. exactly the five triangles (1,1,1), (1,2,2), (2,1,2), (2,2,1), (2,2,2) of the cube
   {1,2}^3, with the degenerate (1,1,2), (1,2,1), (2,1,1) correctly dropped, and a, b, c
   attached to 2, 3, 5 as in the problem.
5. **Numerical convergence** (`work/putnam_2015_b4/numeric_check.py`, exact `Fraction`
   arithmetic, same index ranges and strict inequalities as the statement): f 2 = 2/15,
   f 3 = 68/225 (agrees with check 4), f 4 = 1522/3375; f 10 = 0.775677, f 20 = 0.808935,
   f 40 = 0.80952363, f 60 = 0.8095238094705; 17/21 - f 60 = 5.3e-11. The partial sums
   increase to 17/21 = 0.8095238095238. So the hypotheses of the corrected theorem are
   satisfiable (C = 17/21) and its conclusion is the problem's answer. With non-strict
   triangle inequalities the value at n = 60 would be about 2.33333 (so strictness
   matters and upstream has it right).
6. **No model names** in the `.v` files or in this file.
7. `Print Assumptions`: not applicable in this phase (both files end in `Admitted`).
   No `_statement_is_false` / `_statement_is_vacuous` file: the verdict is `compile`,
   the statement is neither false nor vacuous (check 5 exhibits C = 17/21 satisfying the
   hypotheses, and the conclusion is then true).

**Verifier, both toolchains** (`extended/verify.sh`, run after the final edits):

* Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix),
  `(source /opt/rocq91/bin/rocq-env.sh && cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_2015_b4)`:
  ```
  toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
  NOTE putnam_2015_b4.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)
  OK   putnam_2015_b4_corrected.v compiles
  OK   putnam_2015_b4_corrected.v ends in Admitted (statement only)
  OK   putnam_2015_b4.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
  ALL CHECKS PASSED
  ```
  (the NOTE's error is Rocq >= 9.0 rejecting the top-level `Variable R : realType.`).
* Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04),
  `(cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_2015_b4)`:
  ```
  toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
  NOTE putnam_2015_b4.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)
  OK   putnam_2015_b4_corrected.v compiles
  OK   putnam_2015_b4_corrected.v ends in Admitted (statement only)
  OK   putnam_2015_b4.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
  ALL CHECKS PASSED
  ```
  (here the NOTE's error is the `ratr C` one quoted in section 2).

## 5. Difficulty estimate and proof sketch

**Difficulty: 4 / 5.** The mathematics is a short computation, but the Rocq proof has
to reindex finite triple sums under a parity split and pass to a limit in
MathComp-Analysis, which is heavy bookkeeping.

Mathematical proof. For positive integers with strict triangle inequalities put
x = b + c - a, y = a + c - b, z = a + b - c: positive integers of the same parity, and
conversely a = (y+z)/2, b = (x+z)/2, c = (x+y)/2. Hence T is the disjoint union of
{(v+w, u+w, u+v) : u, v, w >= 1} (x, y, z even) and {(v+w+1, u+w+1, u+v+1) : u, v, w >= 0}
(x, y, z odd), and the term factors as 2^a/(3^b 5^c) = (1/15)^u (2/5)^v (2/3)^w times
2/15 in the odd case. So

  S = (1/14)(2/3)(2) + (2/15)(15/14)(5/3)(3) = 2/21 + 5/7 = 17/21.

Rocq plan (lemma names checked to exist in both the MathComp 2.5.0 / MathComp-Analysis
1.16.0 sources and the installed MathComp 2.1.0 / MathComp-Analysis 1.0.0 sources:
`squeeze_cvgr` (normedtype / normed_module), `cvg_geometric_series`, `geometric_seriesE`,
`nondecreasing_cvgn` (sequences), `cvg_unique`, `cvg_lim` (topology / separation_axioms),
`exchange_big`, `big_nat_widen` (bigop), `fmorph_inj` (ssralg), `ler_rat` (rat)):

1. Upper bound: for every n, f n <= 17/21. Map each triple counted in f n to its
   (u, v, w) (injective, lands in [0, n)^3), so f n is bounded by the two finite triple
   products of geometric partial sums, each <= its closed-form value.
2. Lower bound: for every N, f (2N + 2) >= G1(N) + G2(N), where G1, G2 are the products
   of geometric partial sums over u, v, w < N (every such (u, v, w) gives a triangle with
   sides < 2N + 2). `cvg_geometric_series`/`geometric_seriesE` and `cvgM`/`cvgD` give
   G1(N) + G2(N) --> 17/21.
3. f is nondecreasing (nonnegative terms, `big_nat_widen`), so the squeeze on the
   subsequence plus monotonicity gives f --> 17/21 (`squeeze_cvgr`, or
   `nondecreasing_cvgn` with the bounds and `cvg_lim`).
4. `cvg_unique` with `hf` gives `ratr C = ratr (17%:Q / 21%:Q)`; injectivity of `ratr`
   (`fmorph_inj`, or `ler_rat` twice with `le_anti`) gives `C = 17/21`; finish with
   `vm_compute` (check 2 shows this closes).

The fiddly part is steps 1-2: building the reindexing (the parity split and the
bijection with (u, v, w)) as `reindex`/`partition_big` manipulations of `\sum_(1 <= i < n)`
triple sums, with `nat` arithmetic side conditions (`lia`/`zify`). An alternative for
step 1 is to bound f n by the full double-geometric closed form directly via
`ler_sum` over the image set.

Expected `Print Assumptions` for a future proof: only the statement's `R` and the three
classical axioms of `mathcomp.classical` (`propositional_extensionality`,
`functional_extensionality_dep`, `constructive_indefinite_description`).

## 6. Status of each file

| file | status |
|---|---|
| `putnam_2015_b4.v` | upstream text verbatim after a header comment (no compat lines: it would not compile with them either). **Does not compile** on Coq 8.18.0 (error at `--> ratr C`) nor on Rocq 9.1.1 (first error at the top-level `Variable`), by design of the `compile` verdict (check 1). |
| `putnam_2015_b4_corrected.v` | corrected statement, ends in `Proof. Admitted.`; **compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0**, no warning from its own lines on either; verifier ALL CHECKS PASSED on both; differs from upstream by the ascription `(ratr C : R)` and the marked compat lines. |
| `putnam_2015_b4_statement_is_false.v` / `_vacuous.v` | not applicable (verdict `compile`; statement faithful, satisfiable hypotheses, true conclusion). |
| `putnam_2015_b4_corrected_proof.v` | not written in this phase (proof phase). Sketch in section 5. |
| `NOTES.md` | this file. |
