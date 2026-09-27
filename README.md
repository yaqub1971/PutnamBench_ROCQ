# Rocq proofs for PutnamBench: 1962 A2, A4, A5, A6, B2, B5 and 1963 A2 — plus three defective statements

[![verify](https://github.com/yaqub1971/PutnamBench_ROCQ/actions/workflows/verify.yml/badge.svg)](https://github.com/yaqub1971/PutnamBench_ROCQ/actions/workflows/verify.yml)

This repository contains machine-checked Rocq/MathComp proofs of seven
[PutnamBench](https://github.com/trishullab/PutnamBench) problems and a report on
three PutnamBench Rocq statements that turned out to be defective (three of the seven
proofs are of corrected versions of those statements).

The proofs were produced by an LLM (Claude Fable 5.1, Anthropic) working in Rocq/MathComp,
with me directing the work and running the checks. The purpose of the exercise is
to see how far current language models can get at *formalizing and proving in
Rocq specifically*, which is the least-exercised track of the benchmark.

## What is in this repository

| File | What it is |
|---|---|
| `putnam_1962_a5.v` | Proof of the upstream statement of 1962 A5, unchanged: for n ≥ 2, Σ<sub>k=1..n</sub> C(n,k)·k² = n(n+1)·2<sup>n−2</sup>. |
| `putnam_1963_a2.v` | Proof of the upstream statement of 1963 A2, unchanged: a positive, strictly increasing, multiplicative f : ℕ → ℕ with f(2) = 2 is the identity. (One import line, `zify`, is added for the proof's tactics.) |
| `putnam_1962_b2.v` | Proof of the upstream statement of 1962 B2, unchanged: there is a function f from ℝ to the subsets of ℕ with f(a) ⊊ f(b) whenever a < b. The witness sends a to the set of (MathComp-encoded) rationals below a. |
| `putnam_1962_a4.v` | Proof of the upstream statement of 1962 A4, unchanged: if \|f\| ≤ 1 and \|f''\| ≤ 1 on an interval of length at least 2, then \|f'\| ≤ 2 there. The proof derives a second-order Taylor bound from MathComp-Analysis's mean value theorem. (One line of extra imports is added for the proof's libraries and tactics.) |
| `putnam_1962_a6_corrected_proof.v` | Proof of 1962 A6 **against a corrected statement**: a set of rationals closed under addition and multiplication, containing exactly one of r, −r for every r ≠ 0, is the set of positive rationals. The upstream statement has contradictory hypotheses (see below); this file proves the statement with the two fixes of `putnam_1962_a6_corrected.v` applied, working directly on Coq's concrete fractions. Its only axiom is the standard library's `Extensionality_Ensembles`, which the conclusion (an equality of `Ensemble`s) requires. |
| `putnam_1962_a2_corrected_proof.v` | Proof of 1962 A2 **against a corrected statement**: every nonnegative f whose mean value over [0, x] equals √(f(0)·f(x)) for all x > 0 (or all 0 < x < e) agrees with a member of the four-family solution set at every x > 0 of its domain (and on [0, e) in the second case), and every member of that set satisfies the condition on (0, +∞) or on some (0, e). The upstream answer key is incomplete (see below); this file proves the statement with the solution set of `putnam_1962_a2_corrected.v`. The proof works with MathComp-Analysis' Lebesgue integral: the integral function F is shown to be nondecreasing, hence f = F²/(a x²) measurable, on the part of the domain where the integral is finite; the fundamental theorem of calculus, the mean value theorem and the intermediate value theorem then force the closed form a x/(1 − c x) for F, and a bound on f identifies where the integral is finite. Its `Definition` of the solution set and its `Theorem` block are byte-identical to `putnam_1962_a2_corrected.v`. |
| `putnam_1962_b5_corrected_proof.v` | Proof of 1962 B5 **against a corrected statement**. The upstream Rocq statement is false as written (see below), so it cannot be proved; this file proves the statement with the one-token fix applied. Apart from that fix and the two marked compatibility lines described below, the statement is the upstream text. Its proof follows the structure of a Lean proof of the same problem. |
| `ISSUE_REPORT_rocq.md` | Report on the three defective upstream statements (1962 B5, A6, A2), written for the PutnamBench issue tracker. |
| `ci/verify.sh`, `.github/workflows/verify.yml` | The verification script and the GitHub Actions workflow that runs it on every push (see "Continuous verification" below). |
| `COVERAGE.md` | Problem-by-problem comparison with the twelve Lean solutions Humanfia published as a public preview: which of them have Rocq statements at all, and what this repository did with each. |
| `putnam_1962_b5.v`, `putnam_1962_a6.v`, `putnam_1962_a2.v` | Copies of the upstream statements at the commit named in the report, kept as evidence. `putnam_1962_a6.v` is verbatim. The B5 and A2 copies are verbatim except for clearly marked `(* compat: ... *)` lines (see "Rocq 9.1 / MathComp 2.5 compatibility" below), without which the upstream files do not compile on current Rocq at all. |
| `putnam_1962_b5_statement_is_false.v` | Derives `False` from the upstream B5 statement at n = 2 (it asserts 5/3 < 5/4). |
| `putnam_1962_a6_statement_is_vacuous.v` | Closes the upstream A6 statement with a one-line proof that uses only the contradiction in its hypotheses, no mathematics. |
| `putnam_1962_a2_statement_is_false.v` | Derives `False` from the upstream A2 statement: the indicator of the point 0 satisfies the benchmark's condition (its average over every [0, x] is 0) but is not of the form `a/(1 - c x)^2`, which the theorem claims every solution is. |
| `putnam_1962_b5_corrected.v`, `putnam_1962_a6_corrected.v`, `putnam_1962_a2_corrected.v` | The proposed fixes to the three statements, each proved in the corresponding `_corrected_proof.v` file. The A2 fix transcribes the four-case solution set of the Lean statement. |

The seven proof files end in `Qed`, contain no `Admitted`, `admit` or added
`Axiom`, and each is self-contained (the only dependencies are the MathComp,
MathComp-Analysis and Algebra-Tactics libraries and, for A6, Coq's standard
library).

## The three defective statements

While working through the 1962 problems that have Rocq versions (plus 1963 A2),
three of the first eight statements examined could not be proved as written:

* **1962 B5** encodes the lower bound as (3n + 4)/(2n + 2) instead of
  (3n + 1)/(2n + 2). The Lean and Isabelle statements are correct; the Rocq one is
  false already at n = 2. Fix: replace `3 * (n%:R + 1) + 1` by `3 * n%:R + 1`.
* **1962 A6** has contradictory hypotheses (`~(A r \/ A (-r))` where
  `~(A r /\ A (-r))` was intended, and Leibniz equality on non-canonical `Q`
  fractions), so the theorem is vacuously true and provable in one line. The
  corrected statement is proved in `putnam_1962_a6_corrected_proof.v`.
* **1962 A2** ("find all f whose average over [0, x] equals √(f(0)·f(x))") gives
  the answer as the single family `a/(1 - c x)^2`, but the benchmark's own
  condition is also satisfied by, e.g., the function that is 1 at 0 and 0
  elsewhere (its integral over every [0, x] is 0, and √(1·0) = 0), which agrees
  with no member of that family; so the theorem is false. PutnamBench's Lean
  version was already repaired with a four-case answer; the Rocq and Isabelle
  versions were not. Fix: adopt the Lean solution set (`putnam_1962_a2_corrected.v`).
  The corrected statement is proved in `putnam_1962_a2_corrected_proof.v`, which
  confirms that the transcribed solution set is exactly right for the Rocq reading
  of the integral.
* **1962 B5 and A2, separately from the mathematical defects,** do not compile at all on the
  current Rocq Platform (Rocq 9.1.0, MathComp 2.5): `Variable R : realType.`
  outside a `Section` became an error in Rocq 9.0, and the import order
  `all_algebra all_ssreflect` (used throughout the corpus) lets MathComp 2.5's
  `all_ssreflect` override the ring notations `1` and `%:R`, so `i%:R / N%:R` in
  the statement no longer typechecks. Both points are likely to affect other
  files in `coq/src`. **1962 A4** has a third problem of this kind: since
  MathComp-Analysis 1.9.0 the derivative notations `f^`()` and `f^`(2)` it uses
  exist only in `classical_set_scope`, which the statement never opens, so the
  file does not even parse on a current installation.

Full details, evidence files and proposed fixes are in
`ISSUE_REPORT_rocq.md`. The report is being submitted to the
PutnamBench maintainers through the repository's issue tracker so the statements
can be fixed upstream.

## How the proofs were checked

Toolchain: Rocq 9.1.0 (Rocq Platform 2026.07, macOS) with the MathComp 2.5
packages it bundles (`ssreflect`, `algebra`, `zify`; the B5 and A4 files
additionally use `mathcomp.reals`, `lra` and `ring` from MathComp-Analysis /
Algebra-Tactics, A4 also the derivatives and mean value theorem of
MathComp-Analysis 1.16.0; the B2 files use `mathcomp.reals`; the A2 files use the
Lebesgue integral of MathComp-Analysis 1.16.0, and the A2 proof also its fundamental
theorem of calculus, mean value theorem and intermediate value theorem, plus `lra`,
`nra` and `field` from Algebra-Tactics).

### About the warnings

The PutnamBench Rocq statements were written for an earlier MathComp (2.1). Under
Rocq 9.1 / MathComp 2.5 the `From mathcomp Require Import all_algebra
all_ssreflect.` line at the top of each statement triggers about thirty warnings
emitted by MathComp itself (`all_ssreflect` is deprecated since 2.5, ambiguous
coercion paths, overridden notations), the extra import line of the A2 proof
draws a dozen more of the same kind from MathComp-Analysis, and the A6 files'
`Require Import Ensembles QArith` draws a "Loading Stdlib without prefix is
deprecated" notice from Rocq 9. These are library warnings, not warnings about
this repository's code: none of the files' own lines produce any (verified on
Rocq 9.1.0, see the status below).
The import lines are kept exactly as upstream wrote them so that every statement
stays identical to the benchmark's; each `.v` file repeats this note in its
header.

### Rocq 9.1 / MathComp 2.5 compatibility lines

The four B5 files (`putnam_1962_b5.v`, `putnam_1962_b5_corrected.v`,
`putnam_1962_b5_corrected_proof.v`, `putnam_1962_b5_statement_is_false.v`) and the
four A2 files (`putnam_1962_a2.v`, `putnam_1962_a2_corrected.v`,
`putnam_1962_a2_corrected_proof.v`, `putnam_1962_a2_statement_is_false.v`) each
contain a few lines marked
`(* compat: ... *)`; `putnam_1962_b2.v` contains only the second of them, and
`putnam_1962_a4.v` the second and the third:

* `From mathcomp Require Import ssralg.` right after the upstream imports. Since
  MathComp 2.5, `all_ssreflect` is a deprecated umbrella that re-declares the
  `ring_scope` notations `1` and `%:R`; imported *after* `all_algebra` (the
  upstream order) it overrides the `ssralg` versions and the statement's
  `i%:R / N%:R` fails to typecheck. Re-importing `ssralg` restores them. On
  MathComp 2.4 and earlier the line is a no-op. It is bracketed by two
  `Set Warnings` lines so that the re-import itself does not add a
  `notation-overridden` warning of its own.
* `Set Warnings "-declaration-outside-section,-local-declaration".` right before
  the upstream `Variable R : realType.`, which Rocq 9.0 and later otherwise reject.
* `Local Open Scope classical_set_scope.` (A4 only) right before the upstream
  `Local Open Scope ring_scope.`: since MathComp-Analysis 1.9.0 the derivative
  notations `f^`()` and `f^`(2)` exist only in that scope, so without the line the
  statement does not parse. It is opened *before* `ring_scope` so that the ring
  notations keep precedence.

They change nothing mathematically. Apart from the header comments,
`diff putnam_1962_b5.v putnam_1962_b5_corrected.v` shows exactly one differing
line (the bound), and the
`Theorem` block of `putnam_1962_b5_corrected_proof.v` is identical to that of
`putnam_1962_b5_corrected.v`.

Each proof went through four checks:

1. **Compilation.** `rocq compile <file>.v` exits with status 0 and produces a
   `.vo` file. Warnings are expected; errors are not.
2. **Assumptions.** A two-line file `Require <file>. Print Assumptions
   <file>.<theorem>.` compiled with `-R . ""` prints
   `Closed under the global context`, i.e. the proof depends on no axioms.
   (For the B5, B2, A4 and A2 proofs, whose statements are about real numbers,
   `Print Assumptions` additionally lists the `Variable R : realType` that the
   upstream statement itself declares, and the classical axioms that
   `mathcomp.reals` introduces — propositional and functional extensionality,
   indefinite description. Both come from the statement and the library, not
   from the proof. For the A6 proof it lists exactly one axiom, the standard
   library's `Extensionality_Ensembles`: the statement's conclusion is an
   equality of `Ensemble`s, i.e. of predicates, which cannot be proved without
   an extensionality principle.)
3. **Independent kernel check.** `rocqchk -R . "" <file>` re-verifies the
   compiled `.vo` with Rocq's standalone checker, which does not trust the
   compiler that produced it.
4. **Statement integrity.** The `Definition` / `Theorem` text of
   `putnam_1962_a5.v`, `putnam_1963_a2.v`, `putnam_1962_b2.v` and
   `putnam_1962_a4.v` is character-for-character the upstream PutnamBench text;
   the only differences are the proof scripts, helper lemmas and definitions,
   and (for 1963 A2 and 1962 A4) added library imports. For B5 the statement is
   the upstream text plus the one-token fix and the marked compatibility lines;
   for A6 it is the upstream text with the two fixes described above (the
   `Theorem` block is identical to that of `putnam_1962_a6_corrected.v`); for A2
   it is the upstream text with the solution set of `putnam_1962_a2_corrected.v`
   (the `Definition` of the solution set and the `Theorem` block are identical to
   that file's, and the only lines added before the statement are the proof's
   library imports). The statement-integrity step of `ci/verify.sh` re-checks
   all of this against the upstream files on every run.

## Verification status (27 September 2026)

All sixteen `.v` files compile on Rocq 9.1.0 / MathComp 2.5 / MathComp-Analysis
1.16.0 (Rocq Platform 2026.07, macOS) with zero errors and zero warnings from
their own lines (the only warnings are the ones MathComp, MathComp-Analysis and
the standard library emit at the import lines, identical for every user).
`Print Assumptions` reports `Closed under the global
context` for `putnam_1962_a5` and `putnam_1963_a2`, and only `R` plus the three
classical axioms of `mathcomp.reals` for `putnam_1962_b5`, `putnam_1962_b2`,
`putnam_1962_a4` and the corrected `putnam_1962_a2`, and only
`Extensionality_Ensembles` for the corrected `putnam_1962_a6`. `rocqchk` reports
`Modules were successfully checked` for all seven proofs. All nine bug-report
evidence files compile, with the A6 vacuity and the B5 and A2 falsity derivations
closing as described above (each `False` derivation lists, as
its only assumptions, the admitted upstream theorem, `R`, and the classical axioms
of `mathcomp.reals`).

## Continuous verification

The badge at the top of this page reports the latest run of
`.github/workflows/verify.yml`. On every push, GitHub Actions starts a fresh
container from the `mathcomp/mathcomp:2.5.0-rocq-prover-9.1` image (Rocq 9.1.0 and
MathComp 2.5, the same versions as the Rocq Platform 2026.07), installs
MathComp-Analysis 1.16.0, zify and Algebra-Tactics, and runs `ci/verify.sh`, which
performs the four checks described above on all sixteen files: it compiles them
in dependency order and fails on any warning from a file's own lines, checks that
no proof file declares a notation, tactic or axiom or contains `admit`, checks the
`Print Assumptions` output of every proof and refutation, runs `rocqchk` on the
seven proofs, and downloads the upstream PutnamBench files at the pinned commit to
confirm that every statement here is byte-identical to upstream apart from the
documented changes. The run's log is public. The same script can be run locally
with `bash ci/verify.sh` from a clone of the repository; when every check passes
it removes the build products it created, leaving the folder as it found it.

## Compiling the files

You need **Rocq 9.1 with MathComp 2.5**, which is what the Rocq Platform 2026.07
release installs and the toolchain everything here was verified on; the B5, A2,
A4 and B2 files additionally need MathComp-Analysis and Algebra-Tactics, also
part of the Platform. If `rocq` is not on your `PATH` (for example with the Rocq Platform app
on macOS), point the shell at it first:

```sh
export PATH="/Applications/Rocq-Platform-9.1-2026.07.app/Contents/Resources/bin:$PATH"
cd PutnamBench_ROCQ          # the folder containing the .v files
```

**Compile one file** (here the 1962 A5 proof; a `putnam_1962_a5.vo` appears next
to it, and no line starting with `Error` means it checked):

```sh
rocq compile -R . "" putnam_1962_a5.v
```

**Compile all files at once**, in dependency order
(`putnam_1962_b5_statement_is_false.v` and `putnam_1962_a2_statement_is_false.v`
load the compiled upstream statements, so the order below matters; the loop stops
at the first failure and prints `OK <name>` after each success):

```sh
for f in putnam_1962_a5 putnam_1963_a2 putnam_1962_b5_corrected_proof \
         putnam_1962_b2 putnam_1962_a4 putnam_1962_a6_corrected_proof \
         putnam_1962_a2_corrected_proof \
         putnam_1962_b5 putnam_1962_b5_statement_is_false putnam_1962_b5_corrected \
         putnam_1962_a6 putnam_1962_a6_corrected putnam_1962_a6_statement_is_vacuous \
         putnam_1962_a2 putnam_1962_a2_statement_is_false putnam_1962_a2_corrected; do
  rocq compile -R . "" $f.v && echo "OK $f" || { echo "FAILED $f"; break; }
done
```

Both commands print the library warnings described above; they are expected.

## Reproduce the checks yourself

With Rocq and MathComp installed, in a clone of this repository:

```sh
# 1. compile the seven proofs
rocq compile putnam_1962_a5.v
rocq compile putnam_1963_a2.v
rocq compile putnam_1962_b5_corrected_proof.v      # needs mathcomp-analysis / algebra-tactics
rocq compile putnam_1962_b2.v                      # needs mathcomp-analysis (mathcomp.reals)
rocq compile putnam_1962_a4.v                      # needs mathcomp-analysis / algebra-tactics
rocq compile putnam_1962_a6_corrected_proof.v      # standard library only
rocq compile putnam_1962_a2_corrected_proof.v      # needs mathcomp-analysis / algebra-tactics

# 2. print their assumptions
printf 'Require putnam_1962_a5.\nPrint Assumptions putnam_1962_a5.putnam_1962_a5.\n' > pa1.v
printf 'Require putnam_1963_a2.\nPrint Assumptions putnam_1963_a2.putnam_1963_a2.\n' > pa2.v
printf 'Require putnam_1962_b5_corrected_proof.\nPrint Assumptions putnam_1962_b5_corrected_proof.putnam_1962_b5.\n' > pa3.v
rocq compile -R . "" pa1.v      # expect: Closed under the global context
rocq compile -R . "" pa2.v      # expect: Closed under the global context
rocq compile -R . "" pa3.v      # expect: only R and the classical axioms of mathcomp.reals
printf 'Require putnam_1962_b2.\nPrint Assumptions putnam_1962_b2.putnam_1962_b2.\n' > pa4.v
printf 'Require putnam_1962_a4.\nPrint Assumptions putnam_1962_a4.putnam_1962_a4.\n' > pa5.v
rocq compile -R . "" pa4.v      # expect: only R and the classical axioms of mathcomp.reals
rocq compile -R . "" pa5.v      # expect: only R and the classical axioms of mathcomp.reals
printf 'Require putnam_1962_a6_corrected_proof.\nPrint Assumptions putnam_1962_a6_corrected_proof.putnam_1962_a6.\n' > pa6.v
rocq compile -R . "" pa6.v      # expect: exactly one axiom, Extensionality_Ensembles
printf 'Require putnam_1962_a2_corrected_proof.\nPrint Assumptions putnam_1962_a2_corrected_proof.putnam_1962_a2.\n' > pa7.v
rocq compile -R . "" pa7.v      # expect: only R and the classical axioms of mathcomp.reals

# 3. independent kernel check (slow: it re-checks MathComp too)
rocqchk -R . "" putnam_1962_a5
rocqchk -R . "" putnam_1963_a2
rocqchk -R . "" putnam_1962_b5_corrected_proof
rocqchk -R . "" putnam_1962_b2
rocqchk -R . "" putnam_1962_a4
rocqchk -R . "" putnam_1962_a6_corrected_proof
rocqchk -R . "" putnam_1962_a2_corrected_proof

# 4. the bug-report evidence
rocq compile putnam_1962_b5.v                               # upstream statement (ends in Admitted); just compiles
rocq compile -R . "" putnam_1962_b5_statement_is_false.v    # assumptions list the admitted putnam_1962_b5: False follows from it
rocq compile putnam_1962_a6_statement_is_vacuous.v          # expect: Closed under the global context
rocq compile putnam_1962_b5_corrected.v
rocq compile putnam_1962_a6.v
rocq compile putnam_1962_a6_corrected.v
rocq compile putnam_1962_a2.v                               # upstream statement (ends in Admitted); just compiles
rocq compile -R . "" putnam_1962_a2_statement_is_false.v    # assumptions list the admitted putnam_1962_a2: False follows from it
rocq compile putnam_1962_a2_corrected.v
```

Every compile prints a batch of warnings at the file's import lines (about thirty
per file on MathComp 2.5, a dozen more for the A2 proof, two for the A6 files); they
come from the libraries, not
from these files, and nothing needs to be done about them (see "About the
warnings" above). The `.vo`, `.vok`, `.vos`, `.glob`, `.*.aux` and `.lia.cache` /
`.nia.cache` / `.nra.cache` files these commands create are build products and are
not part of the repository.
