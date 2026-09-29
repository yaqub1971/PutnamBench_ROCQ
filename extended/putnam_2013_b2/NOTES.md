# putnam_2013_b2 -- notes

## 1. The problem

Putnam 2013 B2. Let `C = union_{N >= 1} C_N`, where `C_N` is the set of "cosine
polynomials" `f(x) = 1 + sum_{n=1}^N a_n cos(2 pi n x)` such that (i) `f(x) >= 0` for all
real `x` and (ii) `a_n = 0` whenever `n` is a multiple of 3. Determine the maximum value of
`f(0)` as `f` ranges over `C`, and prove that the maximum is attained. Answer: **3**,
attained by `f(x) = 1 + (4/3) cos(2 pi x) + (2/3) cos(4 pi x) = (1 + 2 cos(2 pi x))^2 / 3`.

## 2. Defect of the upstream statement

Upstream (`coq/src/putnam_2013_b2.v`, commit 4dbe26e):

    Theorem putnam_2013_b2
        (E: Ensemble (R -> R) := fun f => forall (x : R), exists (a : nat -> R) (N : nat), f x = 1 + sum_n_m (fun n => a n * cos (2 * PI * INR n * x)) 1 N /\ f x >= 0 /\ 
        forall (n: nat), n mod 3 = 0%nat -> a n = 0)
        (m: R)
        (hm : exists f: R -> R, E f /\ f 0 = m)
        (hmub : forall f : R -> R, E f -> f 0 <= m)
        : m = putnam_2013_b2_solution.

In `E` the quantifier prefix is `forall x, exists a N`: the coefficient sequence `a` and
the degree `N` may be chosen separately for every point `x`. So `E` is not the set of
cosine polynomials at all; it contains every function whose value at each point can be
written as `1 + sum_{n=1}^N a_n cos(2 pi n x)` for *some* coefficients. For example
`g(x) = 1 + c cos(2 pi x)^2` lies in `E` for every `c >= 0`: at the point `x` take `N = 1`,
`a_1 = c cos(2 pi x)` and `a_n = 0` otherwise; `g >= 0`; and `g(0) = 1 + c`. Hence `f(0)` is
unbounded on `E`, no maximum `m` exists, and hypothesis `hmub` is unsatisfiable (with
`c = |m|` it gives `1 + |m| <= m`). The theorem is **vacuous**, as the audit verdict says
(vacuous, machine-checked). `putnam_2013_b2_statement_is_vacuous.v` proves the upstream
theorem verbatim from `hmub` alone by exactly this argument (`hm` is cleared).

Re-reading the rest of the statement against the trap list of the brief (section 7.5):

* `sum_n_m (...) 1 N` is Coquelicot's inclusive sum `n = 1, ..., N`: correct.
* `cos (2 * PI * INR n * x)` is `cos(2 pi n x)`: correct; no `nat` division, no `pow`, no
  `Rpower`/`ln`, no `Series`/limits, no integrals.
* `N : nat` allows `N = 0`, which gives the empty sum (`sum_n_m_zero`), i.e. the constant
  function `1`. The problem has `N >= 1`, but the constant `1` is also in `C_1` (with
  `a_1 = 0`) and `C_N` is contained in `C_{N+1}`, so the set of functions (and of values
  `f(0)`) is unchanged. Not a defect.
* `forall n, n mod 3 = 0 -> a n = 0` also constrains `a 0` and the `a n` with `n > N`;
  neither enters `f`, and `a` is free otherwise, so this is exactly condition (ii).
  `n mod 3 = 0` is "3 divides n" (Stdlib `Nat.modulo`; for `n = 0` it is `0 = 0`).
* `f x >= 0` for all `x`: condition (i).
* `E` is a genuine local definition (`:=`), meant as a definition, not a hypothesis in
  disguise.
* `putnam_2013_b2_solution : R := 3` is the real number 3 (`R` is bound to `R_scope`).
* Shape of the conclusion: `hm` ("m is a value f(0), f in E") and `hmub` ("m is an upper
  bound") say that `m` is the maximum, and the conclusion is `m = 3`. See section 3 for why
  this shape is kept.

No other defect was found.

## 3. The fix

One line changes (the first line of the definition of `E`); the quantifier prefixes are
swapped:

    before:     (E: Ensemble (R -> R) := fun f => forall (x : R), exists (a : nat -> R) (N : nat), f x = 1 + sum_n_m (fun n => a n * cos (2 * PI * INR n * x)) 1 N /\ f x >= 0 /\ 
    after:      (E: Ensemble (R -> R) := fun f => exists (a : nat -> R) (N : nat), forall (x : R), f x = 1 + sum_n_m (fun n => a n * cos (2 * PI * INR n * x)) 1 N /\ f x >= 0 /\ 

(the trailing space after `/\` is upstream's and is kept; the next line
`forall (n: nat), n mod 3 = 0%nat -> a n = 0)` is unchanged). Now `E f` says: there are one
coefficient sequence `a` and one `N` such that for all `x`, `f x = 1 + sum_{n=1}^N a_n
cos(2 pi n x)`, `f x >= 0`, and `a_n = 0` for all multiples `n` of 3. The last conjunct does
not depend on `x`; sitting under `forall x` it is equivalent to stating it once (R is
inhabited), and it is left there so that the diff stays a single line. This is the
problem's `C`.

Comparison with the Lean statement (`putnam_2013_b2.lean`): Lean defines `CN N` as the set
of `f` with `forall x, f x >= 0` and one list `a` of length `N + 1` (with `a[n] = 0` for
`3 | n`) such that `forall x, f x = 1 + sum_{n in Icc 1 N} a[n] cos(2 pi n x)`, and takes
the union over `N >= 1`. The corrected `E` has the same quantifier structure (coefficients
chosen once per `f`); it differs only in using a sequence `nat -> R` instead of a list and
in allowing `N = 0`, which as explained above does not change the set.

What was deliberately NOT changed: the upstream conclusion shape. Lean states
`IsGreatest {f 0 | f in C} 3`, i.e. "3 is attained and is an upper bound". The Rocq shape
"for every m that is attained and is an upper bound, m = 3" is the corpus's standard
encoding of "determine the maximum"; the audit accepted it wherever its two hypotheses were
correctly encoded (it flagged 1981 B2 only because the attainment clause there was broken,
and its criterion for "incomplete" is that the statement no longer determines the answer).
Here the answer is determined: the extremal function `(1 + 2 cos(2 pi x))^2 / 3` is in the
corrected `E` with `f(0) = 3` (machine-checked, section 4), so given the problem's bound
`f(0) <= 3`, `m = 3` satisfies both `hm` and `hmub`, and the same statement with any other
answer is false. The upstream shape does not by itself assert that the maximum exists; any
proof of it must nevertheless establish both the bound and `3 <= m` (for which the witness
is the natural route). Switching to the `IsGreatest` form would rewrite the whole theorem
header, which the minimal-diff rule does not call for; if the maintainers prefer it, the
conclusion `(exists f, E f /\ f 0 = putnam_2013_b2_solution) /\ (forall f, E f -> f 0 <=
putnam_2013_b2_solution)` with `m`, `hm`, `hmub` removed would be the drop-in alternative.

No compat lines are needed in any of the files: they use only the standard library and
Coquelicot (no `Variable`, no MathComp notations, no derivative notation).

## 4. Sanity checks (all actually run)

Toolchains: Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4
(Nix, primary) and Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1
(Ubuntu 24.04). Every item below that compiles something was run on both, with build
products deleted when switching toolchains.

1. Compilation, from inside this folder, in the order `putnam_2013_b2.v`,
   `putnam_2013_b2_corrected.v`, `putnam_2013_b2_statement_is_vacuous.v`: all exit 0 on
   `rocq compile -R . ""` (Rocq 9.1.1) and on `coqc -R . ""` (Coq 8.18.0). The only warnings
   are at the `Require Import Ensembles Finite_sets Reals Coquelicot.Coquelicot.` line: on
   Rocq 9.1.1 three "Loading Stdlib without prefix is deprecated" warnings plus Coquelicot's
   "New coercion path [real; Finite] : Rbar >-> Rbar" ambiguous-path warning; on Coq 8.18.0
   only the latter. None come from the files' own lines.
2. Statement integrity: `putnam_2013_b2.v` minus its 28-line header is byte-identical to
   the upstream file (`cmp` silent; the verifier's `strip` + `diff` also empty). The `diff`
   of the header-stripped upstream copy against the header-stripped corrected file is
   exactly the one line quoted in section 3. The statement lines of the evidence file
   (`Require`, `Definition`, `Theorem` block) are identical to upstream's.
3. Evidence: `putnam_2013_b2_statement_is_vacuous.v` proves the upstream theorem, verbatim,
   from `hmub` alone (proof: `clear hm`, then `g(x) = 1 + |m| cos(2 pi x)^2` is shown to be
   in `E` with `N = 1` and `a = fun n => match n with 1 => |m| cos(2 pi x) | _ => 0 end`,
   and `hmub g` gives `1 + |m| <= m <= |m|`). On both toolchains its `Print Assumptions`
   lists exactly `ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec`,
   `FunctionalExtensionality.functional_extensionality_dep` (the axioms of the standard
   library's reals) and nothing else.
4. Scratch file `probe.v` (not a deliverable), with `Ecorr` = the corrected `E` copied
   verbatim as a top-level `Definition`; compiles with exit 0 on both toolchains:
   * `hm_satisfiable : exists f, Ecorr f /\ f 0 = 3`, with the extremal function
     `fext x = 1 + 4/3 cos(2 pi x) + 2/3 cos(2 pi 2 x)`, coefficients
     `match n with 1 => 4/3 | 2 => 2/3 | _ => 0 end`, `N = 2`; nonnegativity via
     `cos_2a_cos` and `fext x = (1 + 2 cos(2 pi x))^2 / 3`; `fext 0 = 3`. So the corrected
     hypotheses are satisfiable in `hm` with the answer `m = 3`, and the corrected `E`
     contains the problem's extremal polynomial. `Print Assumptions`: the three reals axioms
     only.
   * `nonneg_bites : ~ Ecorr (fun x => 1 + 2 cos(2 pi x))` (it is `-1` at `x = 1/2`):
     condition (i) is effective.
   * `N0_const`: with `N = 0` the encoded function is the constant `1`.
   * `N1_shape`: for `N = 1` the coefficient is now pinned down globally
     (`f(0) - 1 = -(f(1/2) - 1)`), in contrast with the upstream pointwise choice.
5. Scratch file `probe2.v`: `Require corr probe.` (corr = the corrected statement), then
   `corr_is_about_Ecorr`, the corrected theorem with its let-bound `E` replaced by
   `probe.Ecorr`, closed by `exact corr.putnam_2013_b2` (so the deliverable's `E` is
   convertible with the checked `Ecorr`), and `witness_lower : (forall f, Ecorr f -> f 0 <=
   m) -> 3 <= m`. Compiles with exit 0 on both toolchains.
6. Non-triviality (an argument, not a machine check): the corrected statement is not provable the upstream way: an `f` in the
   corrected `E` has fixed coefficients, and the upper bound `f(0) <= 3` is the actual
   content of the problem (the vacuity proof relies on the x-dependent coefficient, which
   the corrected `E` no longer allows).
7. Verifier, run after all edits, verdict lines verbatim:
   * `(source /opt/rocq91/bin/rocq-env.sh && cd extended && bash verify.sh putnam_2013_b2)`,
     toolchain `The Rocq Prover, version 9.1.1  (rocq compile)`:

         OK   putnam_2013_b2.v (upstream copy) compiles
         OK   putnam_2013_b2_corrected.v compiles
         OK   putnam_2013_b2_corrected.v ends in Admitted (statement only)
         OK   putnam_2013_b2_statement_is_vacuous.v compiles
         OK   putnam_2013_b2_statement_is_vacuous.v: only library axioms / the statement's R: ClassicalDedekindReals.sig_not_dec ClassicalDedekindReals.sig_forall_dec FunctionalExtensionality.functional_extensionality_dep 
         OK   putnam_2013_b2.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
         ALL CHECKS PASSED

   * `(cd extended && bash verify.sh putnam_2013_b2)`, toolchain
     `The Coq Proof Assistant, version 8.18.0  (coqc)`:

         OK   putnam_2013_b2.v (upstream copy) compiles
         OK   putnam_2013_b2_corrected.v compiles
         OK   putnam_2013_b2_corrected.v ends in Admitted (statement only)
         OK   putnam_2013_b2_statement_is_vacuous.v compiles
         OK   putnam_2013_b2_statement_is_vacuous.v: only library axioms / the statement's R: ClassicalDedekindReals.sig_not_dec ClassicalDedekindReals.sig_forall_dec FunctionalExtensionality.functional_extensionality_dep 
         OK   putnam_2013_b2.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
         ALL CHECKS PASSED

## 5. Difficulty and proof sketch for `putnam_2013_b2_corrected_proof.v`

Difficulty: **2/5** (short classical argument; the Rocq work is finite-sum bookkeeping with
Coquelicot's `sum_n_m` and a few exact cosine values). The sketch below has NOT been
machine-checked; only the witness part (step 1) was, in `probe.v`.

Let `E`, `m`, `hm`, `hmub` be as in the statement.

1. Lower bound `3 <= m`: apply `hmub` to `fext` (the witness of `probe.v`: `fext_in`,
   `fext_0`, proved with `sum_n_Sm`, `sum_n_n`, `cos_2a_cos`, `Rle_0_sqr`, `field`, `lra`).
2. Upper bound `m <= 3`: from `hm` get `f` with `f 0 = m` and its `a`, `N`. Key identity:
   `f(0) + f(1/3) + f(2/3) = 3 + sum_{n=1}^N a_n (1 + cos(2 pi n/3) + cos(4 pi n/3)) = 3`,
   because for `3 | n` the coefficient `a_n` is 0, and for `3 ∤ n` the bracket is
   `1 + 2 * (-1/2) = 0`. With `f(1/3), f(2/3) >= 0` this gives `f(0) <= 3`.
   In Rocq:
   * combine the three sums with `sum_n_m_plus` (twice) and show every summand is 0 with
     `sum_n_m_ext_loc` + `sum_n_m_const_zero`;
   * for each `n`, write `n = 3 k + r` (`Nat.div_mod`, `r = n mod 3 < 3`); case `r = 0`:
     `a n = 0` by the hypothesis; cases `r = 1, 2`: reduce
     `cos(2 PI INR n (1/3))` and `cos(2 PI INR n (2/3))` modulo `2 pi` with
     `cos_period : cos (x + 2 * INR k * PI) = cos x` (after rewriting `INR (3k + r)` with
     `plus_INR`, `mult_INR`), then evaluate with `cos_2PI3 : cos (2 * (PI / 3)) = -1 / 2`
     and `cos(4 pi / 3) = cos(2 pi - 2 pi/3) = -1/2` (`cos_minus`/`cos_2PI`, or
     `cos(4 pi/3) = cos(2 (2 pi/3)) = 2 (1/4) - 1` via `cos_2a_cos`), and at `x = 0` use
     `Rmult_0_r`, `cos_0`;
   * conclude with `lra` from the identity and the two nonnegativity facts at `x = 1/3`,
     `x = 2/3` (from the `f x >= 0` conjunct).
3. `m = 3` by `Rle_antisym`.

Library facts needed: Coquelicot `sum_n_m_plus`, `sum_n_m_ext_loc`, `sum_n_m_const_zero`,
`sum_n_n`, `sum_n_Sm` (all in `Hierarchy.v`); Stdlib `cos_period`, `cos_2PI3`, `cos_0`,
`cos_2a_cos`, `plus_INR`, `mult_INR`, `Nat.div_mod`, `Nat.mod_upper_bound`, `lra`, `lia`.
Expected `Print Assumptions`: the three axioms of the standard library's reals only.

## 6. Status of the files

| file | status |
|---|---|
| `putnam_2013_b2.v` | upstream statement + header comment, no compat lines; compiles on Rocq 9.1.1 and Coq 8.18.0; header-stripped text byte-identical to upstream |
| `putnam_2013_b2_corrected.v` | corrected statement, one line differs from upstream (quantifier order in `E`); compiles on Rocq 9.1.1 and Coq 8.18.0 with no warnings from its own lines; ends in `Proof. Admitted.` |
| `putnam_2013_b2_statement_is_vacuous.v` | upstream theorem verbatim, proved from `hmub` alone; compiles on Rocq 9.1.1 and Coq 8.18.0; `Print Assumptions` lists only the three reals axioms on both |
| `putnam_2013_b2_corrected_proof.v` | not written in this phase (proof phase) |
| `NOTES.md` | this file |

Build products (`*.vo *.vos *.vok *.glob .*.aux`) were removed from the folder after the checks.
