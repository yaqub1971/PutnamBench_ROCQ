# putnam_1964_a6 -- notes

## 1. The problem

Putnam 1964 A6. Let `S` be a finite set of collinear points and let `k` be the largest
distance between two points of `S`. Suppose that whenever two points of `S` are a distance
`d < k` apart, some other pair of points of `S` is also a distance `d` apart. Prove that if
two pairs of points of `S` are distances `a` and `b` apart, then `a / b` is rational.
(PutnamBench gives no informal solution; a proof is sketched in section 5.)

## 2. Defect of the upstream statement

Upstream (`coq/src/putnam_1964_a6.v`, commit 4dbe26e):

    Variable R : realType.
    Theorem putnam_1964_a6
        (T : set R)
        (pairs : set (R * R) := [set p : R * R | p.1 \in T /\ p.2 \in T /\ p.1 < p.2])
        (distance : (R * R) -> R := fun p => p.2 - p.1)
        (hrepdist : forall p : R * R, p \in pairs ->
            (exists m : R * R, m \in pairs /\ distance m > distance p) ->
            (exists q : R * R, q \in pairs /\ q <> p /\ distance p = distance q))
        : forall p q : R * R, (p \in pairs /\ q \in pairs /\ q <> p) ->
            exists n d : int, d <> 0 /\ distance p / distance q = (n%:~R)/(d%:~R).

The point set `T : set R` is arbitrary: the word **finite** of the problem (Lean:
`S : Finset ℝ`) is not encoded. Without it the theorem is **false** (audit verdict: false):
take `T = [set: R]`. Then `hrepdist` holds, since for every pair `p` the translate
`(p.1 + 1, p.2 + 1)` is a different pair at the same distance, and the conclusion for the
pairs `p = (0, sqrt 2)`, `q = (0, 1)` says that `sqrt 2 = n / d` with integers `n`, `d <> 0`.
`putnam_1964_a6_statement_is_false.v` derives `False` this way (irrationality of `sqrt 2` by
the parity of the 2-adic valuation, `logn 2`, of `2 b^2 = a^2`).

I re-read the rest of the statement against the trap list of the brief (section 7.5) and
found it faithful:

* `pairs` is the set of ordered pairs `(a, b)` of points of `T` with `a < b`. These
  correspond one to one to the unordered pairs of distinct points. The strict `<` is right,
  because a "pair of points" means two distinct points.
* `distance p = p.2 - p.1` is the distance of the two points and is positive on `pairs`, so
  `distance q` is never 0 in the conclusion.
* `hrepdist`: "there is a pair `m` with `distance m > distance p`" is, for a finite set with
  its maximum distance `k` attained, exactly "`d < k`" (strict, as in the problem). The
  witness `q` must be a *different* pair (`q <> p`) at the same distance. It may share a
  point with `p`, as the problem allows ("another pair of points"). Lean has the same
  hypothesis.
* The conclusion `exists n d : int, d <> 0 /\ distance p / distance q = n%:~R / d%:~R` says
  that the ratio is rational. The division is the field division of `R`, not `int` division:
  `Set Printing All` shows `GRing.inv` of `R` applied to `intmul 1 d`. The restriction to
  `q <> p` loses nothing (for `q = p` the ratio is 1), and Lean has the same `q ≠ p`.
* `pairs` and `distance` are genuine local definitions (`:=`), used as abbreviations. They
  are not hypotheses in disguise.
* There is no `nat` division, `^`, `Rpower`/`ln`, `Series`, limit, integral, sum, `Q`
  equality or indexing in the statement.
* A side effect of the upstream `Set Implicit Arguments` is that `T`, `p`, `q` are implicit
  arguments of the theorem (`About`: `Arguments putnam_1964_a6 [T] hT hrepdist [p q] _` for
  the corrected one). This changes nothing mathematically.

The only defect is the missing finiteness.

## 3. The fix

Apart from the header comment, `putnam_1964_a6_corrected.v` differs from `putnam_1964_a6.v`
(the upstream copy, which has the same compat lines) in one changed line and one added line:

    -From mathcomp Require Import classical_sets.
    +From mathcomp Require Import classical_sets cardinality.

     Theorem putnam_1964_a6
         (T : set R)
    +    (hT : finite_set T)
         (pairs : set (R * R) := ...

* `finite_set` is MathComp-Analysis' finiteness predicate
  (`Definition finite_set {T} (A : set T) := exists n, A #= `I_n.`, the same definition in
  `mathcomp.classical.cardinality` of MathComp-Analysis 1.0.0 and 1.16.0). It is not
  available through upstream's imports: on Rocq 9.1 without the new import, `Locate` finds
  `mathcomp.classical.cardinality.finite_set` but the bare name is "not found". Adding
  `cardinality` to the `classical_sets` import line is the form the upstream corpus itself
  uses: `putnam_1980_a5.v` (whose conclusion is a `finite_set`), and also `putnam_1974_a1.v`
  and `putnam_2015_b5.v` (which use `#<=` / `#=`), all with
  `From mathcomp Require Import classical_sets cardinality.` (checked by `grep` over the
  upstream `coq/` directory: `putnam_1980_a5.v` is the only upstream file that uses
  `finite_set`).
* The hypothesis sits right after `(T : set R)`, which mirrors Lean's `(S : Finset ℝ)`. The
  Lean statement is the model: it encodes finiteness by the type of `S` and is otherwise
  the same statement (same `pairs`, `distance`, `hrepdist`, and `q ≠ p → ∃ r : ℚ, ... = r`).
  Using `finite_set T` keeps upstream's `set R` encoding and names unchanged. Switching to
  `{fset R}` would be a larger diff for the same meaning.
* Under `Set Printing All` on Rocq 9.1, the type of the corrected theorem differs from
  the upstream one only by the added binder `(_ : @cardinality.finite_set (reals.Real.sort R) T)`.
  So the extra import changes the meaning of nothing else.
* Nothing is weakened: no hypothesis removed, the conclusion unchanged. The added
  hypothesis is stated explicitly in the problem.

Compat lines (the same in all three files, copied from the root files): the
`Set Warnings "-declaration-outside-section,-local-declaration"` line before
`Variable R : realType.` is needed. Without it the upstream file does not compile on Rocq
9.1.1 ("Use of "Variable" or "Hypothesis" outside sections behaves as "#[local] Parameter"
..."). On Coq 8.18 it also silences the `local-declaration` warning that the Variable line
emits there.

The three ssralg re-import lines are in a different position. This statement writes
neither `1` nor `%:R`. On Rocq 9.1 the upstream copy also compiles without them, and its
type under `Set Printing All` is identical with and without them (checked). They are kept,
as in the root `putnam_1962_*` files and the other MathComp-Analysis folders here, so that
the ring notations mean the same on every MathComp version. The evidence file does need
them: its own proof uses `1` on `R`, and without the re-import it fails on MathComp 2.5 with
"The term "1" has type "BaseUMagma.sort ?s0" while it is expected to have type ...".

## 4. Sanity checks (all actually run)

Toolchains: (a) Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix,
`/opt/rocq91`); (b) Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1
(Ubuntu 24.04). The build products were deleted between the two.

1. **Compilation** from inside this folder, in dependency order (`putnam_1964_a6.v`,
   `putnam_1964_a6_corrected.v`, `putnam_1964_a6_statement_is_false.v`). All three exit 0 on
   both toolchains. The only warnings are at each file's first import line
   (`From mathcomp Require Import all_algebra all_ssreflect.`): 30 warnings on (a), 23 on
   (b), all from MathComp itself. None come from the files' own lines.
2. **Raw upstream on (a):** the verbatim upstream file fails at line 12 (`Variable R`) with
   the `declaration-outside-section` error. This is why the compat line is needed.
3. **Upstream copy integrity:** header and compat lines removed, `putnam_1964_a6.v` is
   byte-identical to the upstream file (Python comparison, including the missing final
   newline). The upstream file downloaded from GitHub at commit 4dbe26e is `cmp`-identical
   to the input copy.
4. **Semantic diff** (`Set Printing All`, Rocq 9.1): the upstream theorem type is the same
   with and without the ssralg re-import. The corrected type equals the upstream type plus
   the binder `(_ : cardinality.finite_set T)`.
5. **Evidence** `putnam_1964_a6_statement_is_false.v` compiles on (a) and (b).
   `Print Assumptions putnam_1964_a6_rocq_statement_is_false` lists exactly the admitted
   upstream theorem `putnam_1964_a6`, the three `boolp` axioms
   (`propositional_extensionality`, `functional_extensionality_dep`,
   `constructive_indefinite_description`) and `putnam_1964_a6.R : realType`, on both.
6. **Non-vacuity and non-triviality of the corrected statement.** I wrote a scratch file
   `sanity.v` (in the scratch directory, `work/putnam_1964_a6/t3/sanity.v`, not a
   deliverable). It `Require`s the compiled `putnam_1964_a6_corrected` and compiles with
   exit 0 and no own-line warnings on both (a) and (b). It was re-run against the final
   corrected file after the last header edit, with the same outcome. It proves:
   * (A) `corrected_applies_to_T012`: the corrected theorem applied to `T = [set 0; 1; 2]`.
     Both `hT` (by `finite_set3`) and `hrepdist` are discharged *in their exact form*: the
     pairs at distance 1 are `(0,1)` and `(1,2)`, which are twins, and `(0,2)` has the
     maximal distance. The premise `p \in pairs /\ q \in pairs /\ q <> p` holds for
     `p = (0,2)`, `q = (0,1)`. So the hypotheses are satisfiable and the conclusion is not
     vacuous. `Print Assumptions`: the admitted corrected theorem, the three `boolp`
     axioms, `R`.
   * (B) `conclusion_fails_for_T_without_hrepdist`: for the finite set
     `T = [set 0; 1; 1 + sqrt 2]` the conclusion fails for `p = (1, 1 + sqrt 2)`,
     `q = (0, 1)`, because the ratio is `sqrt 2`. This `T` violates `hrepdist`: the pair
     `(0,1)` at distance `1 < 1 + sqrt 2` has no twin. So finiteness alone does not give
     the conclusion, `hrepdist` is essential, and the corrected statement is not
     trivially true. `Print Assumptions`: only the three `boolp` axioms and `R`.
   * (C) `setT_not_finite : ~ finite_set [set: R]` (via `finite_preimage` along the
     injection `n |-> n%:R` and `infinite_nat`). So the refuting instance
     `T = [set: R]` of the evidence file is excluded by the new hypothesis.
     `Print Assumptions`: only the three `boolp` axioms and `R`.
7. **Verifier** (`extended/verify.sh putnam_1964_a6`), run last, under both toolchains,
   after the final header and NOTES edits (the files were also recompiled on both
   toolchains after those edits: all three exit 0, with warnings only at the first import
   line, which is line 57 of the corrected file, line 41 of the upstream copy and line 30
   of the evidence file):
   * Rocq 9.1.1 (`source /opt/rocq91/bin/rocq-env.sh && bash verify.sh putnam_1964_a6`):

         toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
         OK   putnam_1964_a6.v (upstream copy) compiles
         OK   putnam_1964_a6_corrected.v compiles
         OK   putnam_1964_a6_corrected.v ends in Admitted (statement only)
         OK   putnam_1964_a6_statement_is_false.v compiles
         OK   putnam_1964_a6_statement_is_false.v: assumes the admitted upstream theorem putnam_1964_a6 (False follows from it)
         curl: (23) Failure writing output to destination
         NOTE putnam_1964_a6.v: could not download upstream for comparison
         ALL CHECKS PASSED

     The NOTE is not about this folder's content. The verifier downloads into the
     shared directory `extended/ci_upstream`, and its line 173 (`rm -rf ci_upstream`)
     deletes that directory at the end of every run, so a verifier run for another problem
     going on at the same time can remove it mid-download. To get a clean run I copied
     `verify.sh` and this folder (`diff -r`: identical) to a scratch directory and ran the
     verifier there under Rocq 9.1.1. The download and the comparison both succeeded:

         OK   putnam_1964_a6.v (upstream copy) compiles
         OK   putnam_1964_a6_corrected.v compiles
         OK   putnam_1964_a6_corrected.v ends in Admitted (statement only)
         OK   putnam_1964_a6_statement_is_false.v compiles
         OK   putnam_1964_a6_statement_is_false.v: assumes the admitted upstream theorem putnam_1964_a6 (False follows from it)
         OK   putnam_1964_a6.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
         ALL CHECKS PASSED
   * Coq 8.18.0 (`bash verify.sh putnam_1964_a6`):

         toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
         OK   putnam_1964_a6.v (upstream copy) compiles
         OK   putnam_1964_a6_corrected.v compiles
         OK   putnam_1964_a6_corrected.v ends in Admitted (statement only)
         OK   putnam_1964_a6_statement_is_false.v compiles
         OK   putnam_1964_a6_statement_is_false.v: assumes the admitted upstream theorem putnam_1964_a6 (False follows from it)
         OK   putnam_1964_a6.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
         ALL CHECKS PASSED

## 5. Difficulty and proof sketch for a future `putnam_1964_a6_corrected_proof.v`

Difficulty: **4/5**. The combinatorial core is short. The hard part is doing a small piece
of linear algebra over `Q` inside `R` (a `Q`-linear functional on the `Q`-span of finitely
many reals), which MathComp does not provide ready-made: `R` is not a `vectType` over
`rat`. Finite sets, maxima and case analysis add bookkeeping.

Mathematical proof. Write the points as `x_1 < ... < x_n` (`n >= 2`, otherwise there are no
pairs), `k = x_n - x_1`. Note that `(x_1, x_n)` is the only pair at distance `k`.

1. *Claim:* every `x - x_1` (`x` in `T`) lies in `Q k`. Then every distance is `r k` with
   `r` rational and positive, so `distance p / distance q = r / s` is rational. For the final
   form use `ratr r = (numq r)%:~R / (denq r)%:~R` (the definition of `ratr`) with
   `denq_neq0`.
2. *Proof of the claim, by contradiction.* Let `V` be the `Q`-span of the differences
   `x - x_1`. Suppose some difference is not in `Q k`. Run the greedy basis extraction on
   the list `k, (x - x_1)_x`: keep an element iff it is not in the `Q`-span of the elements
   kept before it (classical decidability, `pselect`). This gives `b_1 = k, ..., b_m` with
   `m >= 2`. Let `W = span(b_1..b_{m-1})` and `y = b_m`. Then `y ∉ W` and `V = W + Q y`.
   Define `f(v)` as the unique rational `c` with `v - c y ∈ W`. It is unique because
   `y ∉ W`. `f` is additive on `V`, with `f(k) = 0` and `f(y) = 1`. No full basis or
   coordinates are needed, only "span of a finite list" as
   `[set v | exists c : seq rat, v = \sum_i ratr c_i * b_i]`.
3. Put `F(x) = f(x - x_1)` on `T`. Then `F(x_1) = 0 = f(k) = F(x_n)`, and `F` takes the value
   1, so `M = max F > min F = m` on the finite set `T`. Let `A = {F = M}` and `B = {F = m}`,
   `a* = max A`, `b* = min B`. The points `a*` and `b*` differ, and `{a*, b*} <> {x_1, x_n}`
   because `F(x_1) = F(x_n)`. So the pair `p` formed by `a*` and `b*` has distance `< k`,
   with `(x_1, x_n)` as the witness `m` of `hrepdist`. `hrepdist` gives a pair
   `(c, d) <> p` with `d - c = |a* - b*|`.
4. Additivity gives `F(d) - F(c) = f(d - c) = ±(M - m)`, the sign being that of
   `a* - b*`. Since `m <= F <= M`, the pair `(c, d)` has one point in `A` and one in `B`,
   and its "`A`-point minus `B`-point" equals `a* - b*`. The `A`-point is `<= a*` and the
   `B`-point is `>= b*`, so they are exactly `a*` and `b*`. Then `(c, d) = p`,
   contradiction.

Library facts it needs:
* `finite_set` to an enumeration: `finite_fsetP` / `finite_setP` of `cardinality`.
* Maxima and minima over a finite set: `\big[Order.max/_]_`, or `fset` / `seq` arg-max
  lemmas.
* `ratr` as a ring morphism: `rmorphD`, `rmorphM`, `fmorph_div`.
* `numq` / `denq`.
* `pselect` / `asboolP` for classical decisions.
* `lra` / `field` from algebra-tactics for the arithmetic.

Expected `Print Assumptions`: the statement's `Variable R` and the three `boolp` axioms.

## 6. Status of the files

| file | status |
|---|---|
| `putnam_1964_a6.v` | upstream statement plus header and marked compat lines; body byte-identical to upstream; compiles on Rocq 9.1.1 and Coq 8.18.0 |
| `putnam_1964_a6_corrected.v` | corrected statement (`hT : finite_set T` added, `cardinality` imported); ends in `Proof. Admitted.`; compiles with no own-line warnings on Rocq 9.1.1 and Coq 8.18.0 |
| `putnam_1964_a6_statement_is_false.v` | derives `False` from the admitted upstream theorem with `T = [set: R]` and the pairs `(0, sqrt 2)`, `(0, 1)`; compiles on both; `Print Assumptions` = upstream theorem + `boolp` axioms + `R` |
| `putnam_1964_a6_corrected_proof.v` | not written (proofs are out of scope for this phase) |
| `NOTES.md` | this file |

Build products (`*.vo *.vos *.vok *.glob .*.aux`) and logs were removed from the folder after
the checks. The verifier removes them on success, and the folder was checked afterwards.
