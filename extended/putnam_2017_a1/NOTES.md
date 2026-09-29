# putnam_2017_a1 -- notes

## 1. The problem

Putnam 2017 A1. Let `S` be the smallest set of positive integers such that (a) `2` is in
`S`, (b) `n` is in `S` whenever `n^2` is in `S`, and (c) `(n+5)^2` is in `S` whenever `n`
is in `S`. Which positive integers are not in `S`? Answer: `1` and the positive multiples
of `5`, i.e. the set `{x > 0 | x = 1 or 5 | x}` (upstream's `putnam_2017_a1_solution`,
the same as the Lean statement's commented solution).

## 2. Defect of the upstream statement

Upstream (`coq/src/putnam_2017_a1.v`, commit 4dbe26e) encodes "the smallest qualifying
set" as

    (hS : IsQualifying S /\ forall T : set int, T `<=` S -> ~ IsQualifying T)

The second conjunct says that NO subset of `S` qualifies. `T = S` is a subset of `S`
(`S `<=` S`), so it gives `~ IsQualifying S`, contradicting the first conjunct. The
hypotheses are contradictory and the theorem is **vacuous** (audit verdict: vacuous,
machine-checked): `putnam_2017_a1_statement_is_vacuous.v` closes upstream's theorem,
verbatim, with the one-liner

    by case: hS => hq /(_ S (fun _ h => h)) /(_ hq).

The rest of the statement was re-read against the trap list of the brief (section 7.5), with
`Set Printing All` on the elaborated theorem (scratch file `parse.v`), and found faithful:

* `IsQualifying_def` is a genuine hypothesis (`<->`), not a local `:=` definition; its four
  conjuncts are "every element is positive", (a) `2 \in S`, (b)
  `forall n, n > 0 /\ n ^ 2 \in S -> n \in S` (parsed as `(n > 0 /\ n^2 \in S) -> n \in S`),
  and (c) `forall n, n \in S -> (n + 5) ^ 2 \in S`.
* `n ^ 2` and `(n + 5) ^ 2` on `int` elaborate to `exprz n 2` / `exprz (n + 5) 2` with
  the exponent `2 = 1 *+ 2 = Posz 2 >= 0`, i.e. the ordinary square `n ^+ 2` (checked by
  proving `x ^ 2 = x * x` by conversion to `x ^+ 2`, `expr2`).
* `(5 %| x)%Z` elaborates to `dvdz 5 x` ("5 divides x", the right direction);
  `x = 1` is Leibniz equality on `int`, which is canonical, so that is fine.
* The conclusion `~` S `&` [set n : int | n > 0]` elaborates to
  `setI (setC S) [set n | 0 < n]`, the positive integers not in `S`; the solution set
  requires `x > 0` as well, so both sides live in the positive integers.
* No `nat` division, no real exponent, no index shift, no bound slip.

A side remark: the upstream file does not compile on Rocq 9.1 / MathComp 2.5 at all
(`x = 1` in the solution set: "The term 1 has type BaseUMagma.sort ?s while it is expected
to have type int", line 11), because importing `all_ssreflect` after `all_algebra`
overrides the ring notation `1`. It compiles on Coq 8.18 / MathComp 2.1 (the audit's
environment). The repository's marked compat lines (kind (1) of the brief: re-import of
`ssralg`) fix this in all three files without changing the statement.

## 3. The fix

One line of the statement changes (checked with `diff` on the files with their headers
removed; the rest, compat lines included, is identical to the upstream copy):

    before:  (hS : IsQualifying S /\ forall T : set int, T `<=` S -> ~ IsQualifying T)
    after:   (hS : IsQualifying S /\ forall T : set int, IsQualifying T -> S `<=` T)

`S` is now the LEAST qualifying set for inclusion: it qualifies and is contained in every
qualifying set. That is exactly "the smallest set" of the problem, and exactly the Lean
statement's `hS : IsLeast IsQualifying S` (Mathlib: `IsLeast s a := a ∈ s ∧ a ∈ lowerBounds s`,
with `≤` on `Set ℤ` being `⊆`), which was the model. Such an `S` exists and is unique (the
intersection of all qualifying sets qualifies, because every clause of `IsQualifying` is a
closure condition and the set of positive integers qualifies), so the hypotheses are
satisfiable; this was machine-checked (section 4).

Alternative considered: keep upstream's shape and make the subset strict,
`forall T : set int, T `<` S -> ~ IsQualifying T` ("S is minimal"). Here minimal and least
coincide (if `S` is minimal and `T` qualifies, then `S `&` T` qualifies and is contained in
`S`, so it equals `S`, hence `S `<=` T`), but "smallest" literally means least, and the
least-element form is what Lean uses, so the least-element form was chosen. It does not
weaken anything: the least set is the unique set that satisfies the corrected `hS`.

Everything else is upstream's text unchanged: imports, `Set`/`Unset` lines, scopes, theorem
name, `putnam_2017_a1_solution`, `IsQualifying_def`, the conclusion. Compat lines: the
three marked lines of kind (1) (re-import of `ssralg` after the upstream imports), identical
in the upstream copy, the corrected file and the evidence file. No `Variable` outside a
Section, no derivative notation, so no compat lines of kinds (2) or (3).

## 4. Sanity checks (all actually run)

* Compilation, Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (`rocq compile -R . ""`):
  `putnam_2017_a1.v`, `putnam_2017_a1_corrected.v`, `putnam_2017_a1_statement_is_vacuous.v`
  all compile (exit 0). The only warnings are the 30 library warnings attributed to the
  first import line `From mathcomp Require Import all_algebra all_ssreflect.`; none come
  from the files' own lines. Without the compat lines the upstream file fails on 9.1 (error
  quoted in section 2).
* Compilation, Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (`coqc -R . ""`, after
  deleting the 9.1 build products): the same three files compile (exit 0), no warning from
  their own lines.
* Vacuity proof: `Print Assumptions putnam_2017_a1.` in the evidence file prints, on both
  toolchains, only `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`,
  `boolp.constructive_indefinite_description` (they come from the statement: membership
  `n \in S` in a classical `set int` goes through boolp's `asbool`).
* Elaboration of the corrected statement: `Set Printing All. Check putnam_2017_a1. Print
  putnam_2017_a1_solution.` (scratch `parse.v`, Rocq 9.1) -- see the bullet list in
  section 2; the new conjunct elaborates to `forall T : set int, IsQualifying T -> @subset int S T`.
* Scratch file `sanity.v` (in the scratch directory, not in this folder), compiled against
  `putnam_2017_a1_corrected.vo` on BOTH toolchains (exit 0 on each), proves:
  - `pos_IQ`: the set of positive integers satisfies `IsQualifying`'s defining clauses;
  - `least_exists : exists S, IQ S /\ forall T, IQ T -> S `<=` T` with
    `S := [set n | forall T, IQ T -> n \in T]` (the intersection of all qualifying sets),
    where `IQ` is literally the right-hand side of `IsQualifying_def`: the hypotheses of the
    corrected theorem are satisfiable (non-vacuity). `Print Assumptions least_exists`: only
    the three boolp axioms.
  - `corrected_instance`: the corrected theorem can be instantiated with
    `IsQualifying := IQ`, `IsQualifying_def := fun _ => iff_refl _`, `S :=` the least set.
  - `half_sol_sub`: from the corrected hypotheses, `putnam_2017_a1_solution `<=` ~` S `&`
    [set n | n > 0]`, i.e. HALF of the corrected theorem (1 and the positive multiples of 5
    are not in `S`), by showing that `[set n | n > 0 /\ n <> 1 /\ ~ 5 %| n]` qualifies and
    using leastness. `Print Assumptions half_sol_sub`: only the three boolp axioms (it does
    not use the admitted theorem). This confirms the corrected minimality clause has the
    intended strength: it is what makes this half provable, and it would not be provable
    from qualifying alone.
  - small values of the solution set: `1` and `10` are in it; `0`, `2`, `3` are not
    (`sol_1`, `sol_10`, `sol_not_0`, `sol_not_2`, `sol_not_3`).
* Verifier (`extended/verify.sh putnam_2017_a1`), verdict lines:

  - under Rocq 9.1 (`source /opt/rocq91/bin/rocq-env.sh && bash verify.sh putnam_2017_a1`):

      toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
      OK   putnam_2017_a1.v (upstream copy) compiles
      OK   putnam_2017_a1_corrected.v compiles
      OK   putnam_2017_a1_corrected.v ends in Admitted (statement only)
      OK   putnam_2017_a1_statement_is_vacuous.v compiles
      OK   putnam_2017_a1_statement_is_vacuous.v: only library axioms / the statement's R: boolp.propositional_extensionality boolp.functional_extensionality_dep boolp.constructive_indefinite_description 
      OK   putnam_2017_a1.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
      ALL CHECKS PASSED

  - under Coq 8.18 (`bash verify.sh putnam_2017_a1`, plain PATH):

      toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
      OK   putnam_2017_a1.v (upstream copy) compiles
      OK   putnam_2017_a1_corrected.v compiles
      OK   putnam_2017_a1_corrected.v ends in Admitted (statement only)
      OK   putnam_2017_a1_statement_is_vacuous.v compiles
      OK   putnam_2017_a1_statement_is_vacuous.v: only library axioms / the statement's R: boolp.propositional_extensionality boolp.functional_extensionality_dep boolp.constructive_indefinite_description 
      OK   putnam_2017_a1.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
      ALL CHECKS PASSED

## 5. Difficulty and proof sketch

Difficulty: **2 / 5** (elementary number theory; the harder half is a short argument, the
easier half is already machine-checked in scratch in about 30 lines).

Proof sketch of the corrected statement. Write `P = [set n | n > 0]`. By set
extensionality (`eqEsubset` / `seteqP`, `in_setE`) it suffices to show both inclusions.

1. `solution `<=` ~` S `&` P` (done in scratch, `half_sol_sub`): the set
   `T = {n > 0 | n <> 1, ~ 5 | n}` qualifies: `2 ∈ T`; if `n > 0` and `n^2 ∈ T` then
   `n <> 1` (else `n^2 = 1`) and `5 ∤ n` (else `5 | n^2`); if `n ∈ T` then `(n+5)^2 > 1`
   and `5 ∤ (n+5)^2` (Euclid's lemma for the prime 5, then `5 | n+5 -> 5 | n`). By
   leastness `S ⊆ T`, so `1` and multiples of 5 are not in `S`.
2. `~` S `&` P `<=` solution`, i.e. every `m > 1` with `5 ∤ m` is in `S`:
   (i) `S` is closed under `n ↦ n + 5`: from `n ∈ S`, (c) gives `(n+5)^2 ∈ S`, and (b)
   (with `n + 5 > 0`) gives `n + 5 ∈ S`. Hence `n ∈ S` implies `n + 5k ∈ S` for all
   `k >= 0`.
   (ii) `2 ∈ S`, so `49 = (2+5)^2 ∈ S` (`49 ≡ 4 mod 5`), and `54^2 = 2916 = (49+5)^2 ∈ S`
   (`2916 ≡ 1 mod 5`). By (i), every `x ≡ 4 (mod 5)` with `x >= 49` and every
   `x ≡ 1 (mod 5)` with `x >= 2916` is in `S`.
   (iii) Let `m >= 2`, `5 ∤ m`. Then `m^4 ≡ 1 (mod 5)` (Fermat) and
   `m^(2^k) >= 2^16 = 65536 >= 2916` for `k = 4`; so `m^16 ∈ S` by (ii), and four
   applications of (b) (to `m^8`, `m^4`, `m^2`, `m`, all positive) give `m ∈ S`.
   (Equivalently: induction on `k` for `m^(2^k) ∈ S -> m ∈ S`.)
   So a positive integer not in `S` is `1` or a multiple of 5.

Library facts needed: `dvdzE`, `abszM`, `Euclid_dvdM` (prime 5), `dvdzz`, `rpredDr` on the
zmod-closed predicate `dvdz 5`, `exprz` on a nonnegative exponent is `^+` (`expr2`,
`exprS`, `exprM`), `modz`/`%%` arithmetic or a direct witness `m^16 = 49 + 5 k` /
`2916 + 5 k` (via `dvdzP` or `lia`/`nia` from mczify on `int`), `eqEsubset`, `in_setE`/`inE`,
and the classical set lemmas of `classical_sets`. The expected `Print Assumptions` outcome
is the three `boolp` axioms only.

## 6. Status of the files

| file | status |
|---|---|
| `putnam_2017_a1.v` | upstream statement verbatim plus the three marked compat lines; ends in `Admitted`; compiles on Rocq 9.1.1 and Coq 8.18.0 (on 9.1 only thanks to the compat lines). |
| `putnam_2017_a1_corrected.v` | corrected statement (one line changed); ends in `Admitted`; compiles on Rocq 9.1.1 and Coq 8.18.0 with no warning from its own lines. |
| `putnam_2017_a1_statement_is_vacuous.v` | upstream theorem verbatim (plus compat lines) closed by a one-line proof using only the contradiction in `hS`; compiles on both toolchains; `Print Assumptions`: the three boolp axioms. |
| `putnam_2017_a1_corrected_proof.v` | not written (proofs are out of scope for this phase). |
