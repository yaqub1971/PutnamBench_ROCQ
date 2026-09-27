# Three defective Rocq/Coq statements: putnam_1962_b5 (false), putnam_1962_a6 (contradictory hypotheses), putnam_1962_a2 (incomplete answer, false) — and the files no longer compile on Rocq 9.1 / MathComp 2.5

Benchmark commit: 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20)
Environments used to check: Coq 8.18.0, MathComp 2.1.0, MathComp-Analysis 1.0.0 (Ubuntu 24.04
packages, with MathComp-Analysis 1.0.0 for section 3); and Rocq 9.1.0 with MathComp 2.5 and
MathComp-Analysis 1.16.0 (Rocq Platform 2026.07, macOS).

While attempting the Rocq statements of the 1962 problems, I found three that cannot be
solved as written. For B5 and A6 the Lean and Isabelle statements are fine and the errors
are confined to the `coq/src` files; for A2 the Lean statement was evidently repaired at
some point (its solution set has four cases) while the Rocq and Isabelle files kept the
original one-case answer.

## 1. putnam_1962_b5.v: the statement is false

The problem asks to prove, for every integer n > 1,

    (3n + 1) / (2n + 2)  <  (1/n)^n + (2/n)^n + ... + (n/n)^n  <  2.

The Lean and Isabelle files state this bound correctly (`(3 * n + 1) / (2 * n + 2)`).
The Rocq file has

    (3 * (n%:R + 1) + 1) / (2 * n%:R + 2) < sumf n < 2

i.e. (3n + 4) / (2n + 2), which is *larger* than the sum for small n. At n = 2 the
statement asserts 5/3 < 5/4. So no proof of the file as written can exist.

Evidence: the attached `putnam_1962_b5_statement_is_false.v` loads the unmodified
statement (with its `Admitted`) and derives `False` from it at n = 2 in three lines.
`Print Assumptions` shows that the derivation depends only on the admitted theorem
itself, the `realType` variable, and the classical axioms that `mathcomp.reals`
already introduces (propositional/functional extensionality, indefinite description).

Fix (one token): replace `3 * (n%:R + 1) + 1` by `3 * n%:R + 1`. The attached
`putnam_1962_b5_corrected.v` is the file with only that change. The corrected
statement is provable: I have a compiled, axiom-free (beyond the classical axioms of
`mathcomp.reals`) proof of exactly the corrected file, checked under Coq 8.18.0 /
MathComp 2.1.0 / MathComp-Analysis 1.0.0, and can share it with the maintainers
privately, following the leaderboard's request not to post proofs publicly.

## 2. putnam_1962_a6.v: the hypotheses are contradictory (theorem vacuously true)

The hypothesis `hSScond` is meant to encode "for every rational r, exactly one of
r ∈ A, −r ∈ A, r = 0 holds". Two things go wrong.

(a) The second conjunct is `~(A r \/ A (-r))`; it should be `~(A r /\ A (-r))`.
    As written it says that neither `A r` nor `A (-r)` ever holds, which together
    with the first conjunct forces `r = 0` for every r, e.g. `1 = 0`. The hypotheses
    are therefore unsatisfiable and the theorem is provable in one line without any
    mathematics. The attached `putnam_1962_a6_statement_is_vacuous.v` is the
    unmodified statement closed by exactly such a proof (`Print Assumptions`:
    closed under the global context).

(b) `r = 0` is Leibniz equality on `Q`, but `Q` fractions are not canonical:
    `0#2 <> 0` although `0#2 == 0`. Even with (a) fixed, at r = 0#2 the terms `A r`
    and `A (-r)` are the *same* proposition (`-(0#2)` computes to `0#2`), so
    "exactly one of A r, A (-r)" is impossible and the hypotheses are again
    unsatisfiable. The equality should be `r == 0` (Qeq).

Fix: the attached `putnam_1962_a6_corrected.v` makes both changes
(`\/` → `/\` in the second conjunct, and `r = 0` → `r == 0` throughout).
With these, the hypotheses are satisfied by the positive rationals, and
Qeq-compatibility of `A` follows from the hypotheses, so no further hypothesis is
needed for the conclusion `A = (fun r : Q => r > 0)`.

## 3. putnam_1962_a2.v: the solution set is incomplete, so the theorem is false

The problem asks for every f on an interval with left endpoint 0 such that, for every
x > 0 in it, the average of f over [0, x] equals sqrt (f 0 * f x). The Rocq file encodes
the condition as

    P s f <-> (forall x, f x >= 0) /\ forall x, x \in s ->
              1/x * \int[mu]_(t in [set t | 0 <= t <= x]) f t = Num.sqrt (f 0 * f x)

(`\int` here is MathComp-Analysis' real-valued `Rintegral`, the finite part of the Lebesgue
integral, which is 0 when the integral is infinite) and gives the answer as

    putnam_1962_a2_solution = [set f | exists a c, a >= 0 /\ f = fun x => a / (1 - c * x) ^ 2].

The theorem then claims (second conjunct) that every f satisfying P on (0, e) agrees with
a member of that set on [0, e). This is false: take f0 = the indicator of the single point
0 (f0 0 = 1, f0 x = 0 otherwise). It is nonnegative and its integral over every [0, x]
is 0 because {0} has Lebesgue measure 0, so its average is 0 = sqrt (f0 0 * f0 x) for
every x <> 0, i.e. f0 satisfies P on (0, 1). But no a / (1 - c x)^2 agrees with f0 on
[0, 1): f0 0 = 1 forces a = 1, and then 1 / (1 - c x)^2 = 0 forces 1 - c x = 0, which
cannot hold at both x = 1/2 and x = 1/3. (The first conjunct fails the same way with the
indicator of the point 1/2 and f 0 = 0.)

Evidence: the attached `putnam_1962_a2_statement_is_false.v` loads the statement (with its
`Admitted`) and derives `False` from it exactly as above; `Print Assumptions` shows only the
admitted theorem, the `realType` variable and the classical axioms of `mathcomp.reals`.
Checked under both environments listed at the top.

The Lean statement of this problem already has the answer these examples require:

    {f | (∃ a c, 0 ≤ a ∧ f = fun x ↦ a / (1 - c * x) ^ 2) ∨
         (∃ a c, 0 ≤ a ∧ 0 < c ∧ f = fun x ↦ if x < 1 / c then a / (1 - c * x) ^ 2 else 0) ∨
         (0 ≤ f ∧ ∀ x, 0 < x → f x = 0) ∨
         (∃ e > 0, f 0 = 0 ∧ 0 ≤ f ∧ ∀ x ∈ Ioo 0 e, (⨍ t in Ico 0 x, f t) = 0)}

(the second case is needed because a non-integrable f has integral 0 in both Lean's
Bochner integral and Rocq's `Rintegral`, so the truncation of a / (1 - c x)^2 past x = 1/c
also satisfies P). Fix: the attached `putnam_1962_a2_corrected.v` transcribes this
four-case solution set to Rocq; the rest of the file is unchanged. I have not attempted
a proof of the corrected statement. The Isabelle file uses the same one-case answer as
the Rocq file and appears to have the same problem.

## 4. The files do not compile at all on Rocq 9.1 / MathComp 2.5

This is independent of the mathematical defects and is probably not specific to these
files. Under the current Rocq Platform (Rocq 9.1.0, MathComp 2.5) `putnam_1962_b5.v` as
published fails for two reasons (the first also stops `putnam_1962_a2.v`):

(a) `Variable R : realType.` is declared outside any `Section`. Rocq 9.0 turned the
    `declaration-outside-section` warning into an error, so compilation stops at that
    line:

        Error: Use of "Variable" or "Hypothesis" outside sections behaves as
        "#[local] Parameter" or "#[local] Axiom".

    Every file in `coq/src` that declares a top-level `Variable` or `Hypothesis` will
    fail the same way. Possible fixes: put the declaration in a `Section`, write
    `Parameter`, or add `Set Warnings "-declaration-outside-section".`

(b) The import order `From mathcomp Require Import all_algebra all_ssreflect.`, used
    throughout `coq/src`, interacts badly with MathComp 2.5. Since 2.5, `all_ssreflect`
    is a deprecated umbrella that re-declares the `ring_scope` notations `1`, `- 1` and
    `_%:R`; imported *after* `all_algebra` it overrides the `ssralg` versions, and the
    statement's `i%:R / N%:R` no longer typechecks:

        Error: The term "1" has type "BaseUMagma.sort ?s" while it is expected to have
        type "Algebra.BaseAddUMagma.sort ?V".

    Files that only use `nat` (e.g. 1962 A5, 1963 A2) are unaffected; any file that
    uses `1`, `-1` or `%:R` in `ring_scope` will fail. Verified fixes: write the imports
    in the usual order `all_ssreflect all_algebra`, or add
    `From mathcomp Require Import ssralg.` after them.

(c) `putnam_1962_a4.v` (and presumably every other file that writes derivatives with
    MathComp-Analysis's ``f^`()`` / ``f^`(2)`` notation) fails on the MathComp-Analysis
    that current platforms ship. Since MathComp-Analysis 1.9.0 (February 2025) these
    notations exist only in `classical_set_scope`, which the statement never opens:

        Error: Unknown interpretation for notation "_ ^` ()".

    Fix: add `Local Open Scope classical_set_scope.` to the preamble (before
    `Local Open Scope ring_scope.`, so that the ring notations keep precedence).

A smaller, related point: `Require Import Ensembles QArith` (1962 A6 and, presumably,
other files) now produces "Loading Stdlib without prefix is deprecated"; Rocq 9 wants
`From Stdlib Require Import Ensembles QArith`. That is only a warning today.

Because of (a) and (b), the attached B5 and A2 files carry a few lines marked
`(* compat: ... *)` (a `Set Warnings` line before the `Variable`, and a re-import of
`ssralg` after the upstream imports, bracketed by `Set Warnings` lines) so that they can
be compiled on both toolchains; apart from those marked lines, `putnam_1962_b5.v` and
`putnam_1962_a2.v` are the upstream files verbatim, `putnam_1962_b5_corrected.v` differs
from its original in exactly one line of the statement, and `putnam_1962_a2_corrected.v`
only in the definition of the solution set (each file also starts with an explanatory
header comment). The proofs of 1962 B2 and 1962 A4 in the same repository carry the
`Set Warnings` line of (a), and the A4 proof also the `Local Open Scope` line of (c).

## Files attached

- putnam_1962_b5.v                      – current upstream statement (verbatim apart from the marked compat lines, see section 4)
- putnam_1962_b5_statement_is_false.v   – derives False from it (compile with -R . "")
- putnam_1962_b5_corrected.v            – proposed fix for the bound (one line differs from putnam_1962_b5.v)
- putnam_1962_a6.v                      – current upstream statement (verbatim)
- putnam_1962_a6_statement_is_vacuous.v – one-line vacuous proof of it
- putnam_1962_a6_corrected.v            – proposed fix
- putnam_1962_a2.v                      – current upstream statement (verbatim apart from the marked compat lines, see section 4)
- putnam_1962_a2_statement_is_false.v   – derives False from it (compile with -R . "")
- putnam_1962_a2_corrected.v            – proposed fix: the Lean solution set, transcribed

## A broader note

These defects survived because, unlike the Lean statements, the Rocq statements have
not been attacked by any prover since the 2024 baselines, so nothing exercises them; the
A2 case also shows that a fix made to a Lean statement was not carried over to the Rocq
and Isabelle versions. Three defective statements among the first eight I looked at (the
1962 problems that have Rocq versions, plus 1963 A2) suggests a systematic audit of the
412 Rocq files would be worthwhile: a cheap first pass is to check that each statement's
hypotheses are satisfiable, that the statement holds at small concrete values of its
parameters, and, for "find all" problems, that the solution set agrees with the Lean one.
Section 4 suggests a second cheap pass: simply compiling all 412 files on the current
Rocq Platform, which would list every file affected by the `Variable` and import-order
issues.
