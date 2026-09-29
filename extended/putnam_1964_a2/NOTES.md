# putnam_1964_a2 -- notes

## 1. The problem

Putnam 1964 A2. Let `alpha` be a real number. Find all continuous real-valued functions
`f : [0, 1] -> (0, +oo)` such that `int_0^1 f(x) dx = 1`, `int_0^1 x f(x) dx = alpha` and
`int_0^1 x^2 f(x) dx = alpha^2`. Answer: there are none. (Reason: for such an `f`,
`int_0^1 (x - alpha)^2 f(x) dx = alpha^2 - 2 alpha * alpha + alpha^2 * 1 = 0`, but the
integrand is continuous, nonnegative, and positive except at the single point
`x = alpha`, so its integral is positive.) PutnamBench encodes the answer as
`putnam_1964_a2_solution alpha = set0` and states that it is equal to the set of all
functions satisfying the conditions.

## 2. Defect of the upstream statement

Audit verdict: **false**. Upstream (`coq/src/putnam_1964_a2.v`, commit 4dbe26e):

    Definition putnam_1964_a2_solution := fun a : R => (set0 : set (R -> R)).
    Theorem putnam_1964_a2
        (alpha : R)
        : putnam_1964_a2_solution alpha = [set f : R -> R | 
            (forall x : R, 0 <= x <= 1 -> (f x > 0)
            /\ {within [set x | 0 <= x <= 1], continuous f}) 
            /\ \int[mu]_(x in [set x | 0 <= x <= 1]) (x * f x) = alpha
            /\ \int[mu]_(x in [set x | 0 <= x <= 1]) (x ^+ 2 * f x) = alpha ^+ 2].

The first condition of the problem, `int_0^1 f(x) dx = 1`, is missing from the set. The
informal statement and PutnamBench's Lean statement of the same problem both have it
(`∫ x in (0)..1, f x = 1`). Without it the set is not empty. The constant function
`f = 4/3` is positive and continuous. With `alpha = 2/3` it gives
`int_0^1 x f = 2/3 = alpha` and `int_0^1 x^2 f = 4/9 = alpha^2`. The theorem claims the
set is `set0`, so it is **false**.

`putnam_1964_a2_statement_is_false.v` machine-checks this. It avoids evaluating integrals
in closed form. Let `i1 = int_0^1 x dx` and `i2 = int_0^1 x^2 dx`. The witness is the
constant `c = i2 / i1^2` with `alpha = c * i1`:
`int_0^1 x c = c i1 = alpha` and `int_0^1 x^2 c = c i2 = c^2 i1^2 = alpha^2`. By calculus
`i1 = 1/2` and `i2 = 1/3`, which gives exactly the audit's pair `c = 4/3`,
`alpha = 2/3`. These two values are standard calculus and were *not* machine-checked; the
proof only needs `i1, i2 > 0`.

I re-read the whole statement against the trap list of the brief (section 7.5). The
missing condition is the only defect:

* Integration domain `[set x | 0 <= x <= 1]` is `[0, 1]`, of type `R`, with `mu` =
  Lebesgue measure. The integral `\int[mu]_(x in D) g x` in `ring_scope` is `Rintegral`,
  the finite part of the Lebesgue integral (it is 0 for an infinite integral). Every
  function in the set is continuous on the compact interval `[0, 1]`, hence bounded and
  integrable. So each `Rintegral` in the set is the ordinary integral, and the finite-part
  convention adds or removes no member.
* The exponents `x ^+ 2` and `alpha ^+ 2` are `nat` powers with exponent 2, as meant.
  There is no `nat` division, `Rpower`/`ln`, series, limit, `sum_n`, `'I_n` indexing,
  absolute value, `sup` or local definition (`:=`) to get wrong.
* Positivity is `f x > 0` (strict), matching the codomain `(0, +oo)`. The interval is
  closed (`0 <= x <= 1`), as in the problem.
* Continuity is `{within [set x | 0 <= x <= 1], continuous f}`, i.e. continuity of the
  restriction to the subspace `[0, 1]` (Lean: `ContinuousOn f (Icc 0 1)`). It sits
  *inside* `forall x, 0 <= x <= 1 -> ...` together with positivity. Because `[0, 1]` is
  not empty, this is equivalent to stating it once, so the quirk is harmless.
* `f : R -> R` is unconstrained outside `[0, 1]`, as in the Lean encoding. For the
  answer `set0` this does not matter.
* `alpha` is universally quantified ("let alpha be a real number"). The answer
  `fun a => set0` is the problem's answer (Lean: `fun _ ↦ ∅`). The theorem name is
  correct.
* Toolchain issues, which are not mathematical: the upstream file does not compile on
  Rocq 9.1 ("Use of Variable or Hypothesis outside sections behaves as #[local]
  Parameter", error at line 13). On MathComp 2.5 the import order also breaks the ring
  notation `1`. Both are handled by the repository's marked compat lines.

## 3. The fix

One line is added. Nothing else changes except the header and the marked compat lines:

    before:
            /\ {within [set x | 0 <= x <= 1], continuous f}) 
            /\ \int[mu]_(x in [set x | 0 <= x <= 1]) (x * f x) = alpha
    after:
            /\ {within [set x | 0 <= x <= 1], continuous f}) 
            /\ \int[mu]_(x in [set x | 0 <= x <= 1]) (f x) = 1
            /\ \int[mu]_(x in [set x | 0 <= x <= 1]) (x * f x) = alpha

The new conjunct uses the same real-valued integral over the same set as the two moment
conditions. `Set Printing All` shows it as
`@eq _ (Rintegral.Rintegral ... mu (mkset (fun x => 0 <= x <= 1)) (fun x => f x)) (GRing.one ...)`
on both toolchains, so the `1` is the ring's one and not a `nat`. It goes where the
problem and the Lean statement put it: after positivity/continuity, before the two
moment conditions. The Lean statement is
`{f | (∀ x ∈ Icc 0 1, f x > 0) ∧ ContinuousOn f (Icc 0 1) ∧ ∫ x in (0)..1, f x = 1 ∧ ∫ x in (0)..1, x * f x = α ∧ ∫ x in (0)..1, x^2 * f x = α^2}`
with `∅` as the answer.

The corrected Rocq statement matches it conjunct for conjunct. It differs only in ways
inherited from upstream that do not change the meaning:
* positivity and continuity are nested in one `forall`;
* it uses the Lebesgue integral over `[0, 1]` rather than Lean's interval integral over
  `(0, 1]`, which has the same value for integrable functions.

With the condition restored the statement says exactly what the problem says, and it is
true (section 1).

Compat lines (identical wording to the root 1962 files):
* the three `ssralg` re-import lines, after the second `From mathcomp` line, because the
  statement uses ring numerals `0`, `1`;
* `Set Warnings "-declaration-outside-section,-local-declaration"` before
  `Variable R : realType.`.

The derivative-notation compat line does not apply (no `f^`()`).

## 4. Sanity checks (all actually run; outcomes as observed)

1. **Compilation, both toolchains, in dependency order**
   (`rocq compile -R . "" <file>.v` after sourcing `/opt/rocq91/bin/rocq-env.sh`, then
   `coqc -R . "" <file>.v` after deleting the build products):

   | file | Rocq 9.1.1 / MC 2.5.0 / MCA 1.16.0 | Coq 8.18.0 / MC 2.1.0 / MCA 1.0.0 |
   |---|---|---|
   | `putnam_1964_a2.v` | exit 0; 30 warnings, all at the first import line (line 44) | exit 0; 23 warnings, all at line 44 |
   | `putnam_1964_a2_corrected.v` | exit 0; 30 warnings, all at line 51 (first import) | exit 0; 23 warnings, all at line 51 |
   | `putnam_1964_a2_statement_is_false.v` | exit 0; 30 at line 35 (first import) + 1 at line 40 (the import loading `realfun`: incompatible notation prefixes) | exit 0; 23 at line 35 |

   No warning comes from a file's own lines. The upstream file *without* compat lines
   fails on Rocq 9.1.1 (the Variable error at line 13). On Coq 8.18.0 it compiles with
   23 library warnings plus a `local-declaration` warning at line 13, which the compat
   line silences.
2. **Statement integrity.** Strip the header box and the marked compat lines from
   `putnam_1964_a2.v` (a Python script mirroring `verify.sh`'s `strip`). The result is
   byte-identical to the input `upstream/coq/putnam_1964_a2.v`, including the missing
   final newline and the trailing spaces after `[set f : R -> R |` and `continuous f})`.
   `diff putnam_1964_a2.v putnam_1964_a2_corrected.v` shows only header lines and the
   one added line.
3. **Elaboration of the new conjunct.** A scratch file `Require`s the corrected module
   and prints `Check putnam_1964_a2` under `Set Printing All`. On both toolchains the
   added conjunct is `Rintegral mu [0,1] (fun x => f x) = GRing.one R`.
4. **Evidence file.** It compiles on both toolchains. `Print Assumptions
   putnam_1964_a2_rocq_statement_is_false` prints exactly:
   * the admitted upstream theorem `putnam_1964_a2 : forall alpha : R, ...`;
   * `boolp.propositional_extensionality`;
   * `boolp.functional_extensionality_dep`;
   * `boolp.constructive_indefinite_description`;
   * `putnam_1964_a2.R : realType`.

   The facts the proof establishes on the way:
   * `x^n` is integrable on `[0, 1]` (`continuous_compact_integrable`);
   * `0 <= int_0^1 x^n <= mu [0,1] = 1`, so each such integral is finite;
   * `i2 <= i1`;
   * `i2 >= 1/8`, by Markov's inequality `le_integral_abse` at the level `1/4`, whose
     superlevel set in `[0, 1]` is `[1/2, 1]`, of Lebesgue measure `1/2`
     (`lebesgue_measure_itv`).
5. **Non-vacuity / non-triviality of the corrected statement.** A scratch file
   `work/putnam_1964_a2/t91/sanity.v` `Require`s the corrected module. It compiled with
   exit 0 on both toolchains and proves two lemmas:
   * `first_three_conditions_satisfiable`: `(fun _ => 1)` belongs to the corrected set
     with its last conjunct dropped, taking `alpha := \int[mu]_(x in [0,1]) (x * 1)`.
     It is positive, continuous within `[0, 1]` (`cst_continuous`), has integral 1
     (`integral_cst` with `mu [0,1] = 1`), and meets the first-moment condition. So the
     conditions before the `alpha^2` condition are jointly satisfiable. `Print
     Assumptions`: only the three `boolp` axioms and `R`.
   * `sketch_identity : a ^+ 2 - 2 * a * a + a ^+ 2 * 1 = 0`, proved by `ring`. This is
     the algebra step of the proof sketch.

   Together with check 4, dropping either the restored condition `int f = 1` or the
   `alpha^2` condition makes the set non-empty. The answer `set0` really depends on all
   the conditions, so the corrected statement is not trivially true.
6. **Verifier**, run under both toolchains:

       (source /opt/rocq91/bin/rocq-env.sh && cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1964_a2)
       toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
       OK   putnam_1964_a2.v (upstream copy) compiles
       OK   putnam_1964_a2_corrected.v compiles
       OK   putnam_1964_a2_corrected.v ends in Admitted (statement only)
       OK   putnam_1964_a2_statement_is_false.v compiles
       OK   putnam_1964_a2_statement_is_false.v: assumes the admitted upstream theorem putnam_1964_a2 (False follows from it)
       OK   putnam_1964_a2.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
       ALL CHECKS PASSED

       (cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1964_a2)
       toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
       OK   putnam_1964_a2.v (upstream copy) compiles
       OK   putnam_1964_a2_corrected.v compiles
       OK   putnam_1964_a2_corrected.v ends in Admitted (statement only)
       OK   putnam_1964_a2_statement_is_false.v compiles
       OK   putnam_1964_a2_statement_is_false.v: assumes the admitted upstream theorem putnam_1964_a2 (False follows from it)
       OK   putnam_1964_a2.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
       ALL CHECKS PASSED

## 5. Difficulty and proof sketch for a future `putnam_1964_a2_corrected_proof.v`

Difficulty: **3/5**. The mathematics is a one-liner. The work is MathComp-Analysis
integration plumbing: integrability of products of functions that are only continuous
within `[0, 1]`, linearity of the integral, and positivity of the integral of a
continuous function that is positive somewhere.

Sketch:
1. `rewrite /putnam_1964_a2_solution`, then `apply/seteqP; split => // f`. It remains to
   show that no `f` satisfies the conditions: assume the four conjuncts and derive
   `False`. Instantiate the first conjunct at `x = 0` to extract the continuity of `f`
   within `[0, 1]`. Positivity stays as `forall x in [0, 1], 0 < f x`.
2. Integrability. `x^k * f x` (k = 0, 1, 2) and `(x - alpha)^2 * f x` are continuous
   within `[0, 1]`: products of `cf` with `x |-> x^k`, which is continuous on `R` and
   hence within the subspace by `continuous_subspaceT`. Use `continuousM` on the
   subspace, or `continuous_within_itvP` if pointwise reasoning is easier. Then
   `continuous_compact_integrable` with `segment_compact` and `set_itvcc` gives
   integrability of each `EFin \o g`.
3. Linearity. `(x - alpha)^2 f = x^2 f - 2 alpha (x f) + alpha^2 f`, so
   `int (x - alpha)^2 f = alpha^2 - 2 alpha^2 + alpha^2 = 0`. Use `integralD`,
   `integralB`, `integralZl` in `\bar R` plus `fineD`/`fineB`/`fineM` on the finite
   integrals, or on MCA 1.16 `RintegralD`/`RintegralB`/`RintegralZl` from
   `lebesgue_Rintegral`.
4. Positivity. Choose an interior point `x0` of `(0, 1)` with `x0 <> alpha` (say `1/4`,
   or `3/4` if `alpha = 1/4`). Then `g x0 = (x0 - alpha)^2 f x0 > 0`. Continuity of `g`
   at `x0` (from `continuous_within_itvP`, interior case) gives `delta > 0` with
   `[x0 - delta, x0 + delta]` inside `(0, 1)` and `g >= g x0 / 2` there. Markov's
   inequality `le_integral_abse` (exactly as in the evidence file) then gives
   `int g >= (g x0 / 2) * 2 delta > 0`, using `lebesgue_measure_itv` for the interval's
   measure. Alternatively use `ge0_subset_integral` (MCA 1.16) / `subset_integral`
   (MCA 1.0.0). This contradicts step 3.

Library facts: `continuous_compact_integrable`, `segment_compact`, `set_itvcc`,
`measurable_itv`, `lebesgue_measure_itv`, `integralD`/`integralB`/`integralZl`,
`le_integral_abse`, `continuous_within_itvP`, `integral_ge0`/`ge0_le_integral`.

Portability: several of these changed names or arities between MathComp-Analysis 1.0.0
and 1.16.0 (`subset_integral` -> `ge0_subset_integral`,
`integral_fune_fin_num` -> `integrable_fin_num` (deprecated), `EFin_measurable_fun` ->
`measurable_EFinP`, one hypothesis fewer in `ge0_le_integral`). A proof meant to compile
on both toolchains should stick to the names common to both, as the evidence file does.

## 6. Status of the files

| file | status |
|---|---|
| `putnam_1964_a2.v` | upstream statement, byte-identical apart from header and the 4 marked compat lines; ends in `Admitted`; compiles on Rocq 9.1.1 and Coq 8.18.0 |
| `putnam_1964_a2_corrected.v` | corrected statement (one line added); ends in `Proof. Admitted.`; compiles on Rocq 9.1.1 and Coq 8.18.0 with no warnings from its own lines |
| `putnam_1964_a2_statement_is_false.v` | derivation of `False` from the admitted upstream theorem; compiles on Rocq 9.1.1 and Coq 8.18.0; `Print Assumptions` = upstream theorem + 3 `boolp` axioms + `R` |
| `putnam_1964_a2_corrected_proof.v` | not written (proofs are out of scope for this phase) |
| `NOTES.md` | this file |

An earlier, interrupted attempt left drafts in this folder:
* Its statement files were reused after line-by-line review. Headers were rewritten,
  and the trailing newline that the upstream file does not have was removed.
* Its evidence draft did not compile on Rocq 9.1 / MathComp-Analysis 1.16.0, because
  `subset_integral` was renamed and `integral_fune_fin_num` is deprecated. The evidence
  file was rewritten with lemma names common to both toolchains.
