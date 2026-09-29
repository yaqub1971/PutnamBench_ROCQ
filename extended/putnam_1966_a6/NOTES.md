# putnam_1966_a6 — notes

Audit verdict: **compile** (one-token fix `--> (3 : R)`; statement otherwise faithful).
This folder: the upstream statement kept as evidence, the corrected statement, and these
notes. No `_statement_is_false` / `_statement_is_vacuous` file: the statement is neither
false nor vacuous (see §2 and §4), so there is no `False` to derive.

## 1. The problem

Putnam 1966 A6: prove that

    sqrt(1 + 2 sqrt(1 + 3 sqrt(1 + 4 sqrt(1 + 5 sqrt(...))))) = 3

(Ramanujan's nested radical, the case x = 2 of x + 1 = sqrt(1 + x sqrt(1 + (x+1) sqrt(...)))).
Both PutnamBench statements (Lean and Rocq) make the infinite radical precise as the limit
of its finite truncations: for n >= 1 define a n n = n and, for 1 <= m < n,
a n m = m * sqrt(1 + a n (m+1)); then

    a n 1 = sqrt(1 + 2 sqrt(1 + 3 sqrt(1 + ... + (n-1) sqrt(1 + n))))

and the claim is a n 1 -> 3 as n -> oo. The informal file gives no solution. The
"limiting values" are L m = m (m + 2) (indeed 1 + (m+1)(m+3) = (m+2)^2, so
L m = m sqrt(1 + L(m+1)), and L 1 = 3); the truncation a n n = n sits below L n = n(n+2).

## 2. The defect in the upstream statement

The upstream file does not compile. Its conclusion line is

    : (fun n => a n 1%nat) @ \oo --> 3.

The bare numeral `3` elaborates, in `ring_scope`, to `3%:R` in an unknown additive monoid,
and the `-->` notation needs a point of a filtered type; unification fails:

    File "./putnam_1966_a6.v", line 18, characters 37-38:
    Error: [printout of the environment omitted]
    The term "3" has type "GRing.Nmodule.sort ?t"
    while it is expected to have type "Filtered.sort ?s".

(This is the error in the audit's build log, at upstream line 18; I reproduced it with Coq
8.18 on the copy in this folder, where it sits at line 48, see §4.) It is a
pure elaboration problem; the intended type is obviously `R`, the `realType` of the
statement. Mathematically the upstream text is a faithful transcription of the Lean
statement (same `a`, same recursion, same 1-based indexing, same limit).

Whether the file compiled on the benchmark authors' (unpinned) versions is unknown. On the
repository's CI toolchain (Rocq 9.1.1) it is rejected even earlier, at line 43 of the copy
(`Variable R : realType.` outside a `Section`, error `[declaration-outside-section]`, an
error since Rocq 9.0; Coq 8.x only warns), which the marked compat line of the corrected
file addresses; see §4.

## 3. The fix and why it is faithful

Exactly one line of the statement changes, by one token (diff of the two `.v` files with
the header comments and the marked compat lines removed):

    18c18
    <     : (fun n => a n 1%nat) @ \oo --> 3.
    ---
    >     : (fun n => a n 1%nat) @ \oo --> (3 : R).

`(3 : R)` is `3%:R : R`, the real number 3, so the conclusion is: the sequence
`n |-> a n 1` converges (in the norm topology of `R`, given by
`Import numFieldNormedType.Exports`) to 3. That is precisely the Lean statement
`Tendsto (fun n => a n 1) atTop (𝓝 3)` with `3 : ℝ`, and the informal claim under the
standard reading of an infinite nested radical as the limit of its truncations. Nothing
else is touched: no hypothesis added or removed, the recursion `a n n = n%:R`,
`a n m = m%:R * sqrt(1 + a n (S m))` for `ge m 1`, `lt m n`, `ge n 1` is the Lean one
(`a n n = n ∧ ∀ m ≥ 1, m < n → a n m = m * Real.sqrt (1 + a n (m + 1))`), and the value
whose limit is taken, `a n 1%nat`, is the Lean `a n 1`. I follow the Lean statement
completely; there is nothing to deviate from.

Re-reading against the trap list of the brief (§7.5), none applies:
- no `nat` division, no `pow`/`^` with a `nat` exponent, no `Rpower`/`ln`;
- `Num.sqrt` is applied to `1 + a n (S m)`, which for the constrained indices is >= 1
  (a n m >= 0 by downward induction from a n n = n), so the `sqrt x = 0 for x < 0`
  convention never matters;
- no series, integrals, `sum_n`, `\sum`, `Q`, `int`, `sup`, divisibility, absolute values;
- indexing is 1-based exactly as in Lean (`ge m 1`, `lt m n`, `a n 1%nat`, `a n n = n%:R`);
  `<`/`<=` match Lean (`m < n`, `n >= 1`, `m >= 1`);
- `-->` in MathComp-Analysis is convergence to the *point* `(3 : R)`; it does not admit
  `+oo` (that would be a different filter), so it is real convergence, not `ex_lim_seq`-style;
- no `(h : Prop := ...)` local definitions, no existential scoping over an `iff`.

Compat lines (marked `(* compat: ... *)`, copied byte-for-byte from the root files
`putnam_1962_a2_corrected.v` / `putnam_1962_b5_corrected.v`, checked with `grep`):
kind (2) before `Variable R : realType.` (needed on Rocq >= 9.0); kind (1), the bracketed
`From mathcomp Require Import ssralg.`, after the upstream import lines because the
statement uses the ring notations `n%:R`, `1 + ...`, `3` (the brief's criterion). Note that
this file's upstream import order is `all_ssreflect all_algebra` (the reverse of the
1962 files), so the re-import is redundant on MathComp 2.5: a scratch copy of the corrected
file with the three kind-(1) lines deleted also compiles on Rocq 9.1.1 (exit 0, all 27
warnings at the import line), see §4. It is a harmless re-import and is kept for
uniformity with the repository. Kind (3) (derivative notations) does not apply.

## 4. Sanity checks actually run (Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04))

1. Rocq 9.1.1 (`source /opt/rocq91/bin/rocq-env.sh`):
   `cd extended/putnam_1966_a6 && rocq compile -R . "" putnam_1966_a6_corrected.v` —
   exit 0, `.vo` produced; all 27 warnings of the log are reported at line 42 (the first
   `From mathcomp Require Import` line: library warnings); **no warning from any of the
   file's own lines**.
2. Rocq 9.1.1: `rocq compile -R . "" putnam_1966_a6.v` (the upstream copy) — exit 1,
   `File "./putnam_1966_a6.v", line 43, characters 0-22: Error: Use of "Variable" or
   "Hypothesis" outside sections behaves as "#[local] Parameter" or "#[local] Axiom".
   [declaration-outside-section,vernacular,default]`. Expected (kept verbatim as evidence).
3. Rocq 9.1.1, scratch copy of the corrected file without the three kind-(1) compat lines:
   exit 0, all 27 warnings at the import line (so kind (1) is redundant here, see §3).
4. Coq 8.18.0 (plain `coqc`, after deleting the 9.1 build products):
   `coqc -R . "" putnam_1966_a6_corrected.v` — exit 0, `.vo` produced; all 23 warnings
   (`notation-overridden`, `ambiguous-paths`) at line 42, the import line; **no warning
   from any of the file's own lines**.
5. Coq 8.18.0: `coqc -R . "" putnam_1966_a6.v` (the upstream copy) — exit 1, the error
   quoted in §2 at line 48 of the copy (= upstream line 18 + the 30-line header),
   characters 37-38. As expected: the file is kept verbatim precisely because it does not
   compile.
6. Byte-identity: with the header stripped, `putnam_1966_a6.v` is identical to the
   upstream `putnam_1966_a6.v` (`diff` empty). With header and the marked compat lines
   stripped (the `strip` filter of `ci/verify.sh`), `putnam_1966_a6_corrected.v` differs
   from upstream in exactly one line (2 diff lines), shown in §3.
7. Non-vacuity of the hypotheses (scratch file `check.v`, compiled with exit 0 on both
   Rocq 9.1.1 and Coq 8.18.0): the
   explicit truncation `a n m := go (n - m) n m` with `go 0 n m = n%:R`,
   `go k.+1 n m = m%:R * sqrt(1 + go k n m.+1)` satisfies the hypothesis `ha` of the
   statement verbatim (`Lemma a_witness`, proof: `subnn` for `m = n`, `subnSK` for
   `m < n`). So the statement is not vacuous, and `ha` pins down `a n m` for all
   1 <= m <= n (values outside that range are irrelevant to the conclusion).
8. Small instances (same scratch file, all proved): `a 1 1 = 1`, `a 2 1 = sqrt 3`,
   `a 3 1 = sqrt(1 + 2 sqrt(1 + 3)) = sqrt 5` (using `nat1r`, `natrX`, `sqrtr_sqr`,
   `ger0_norm`, `natrM`). The corrected conclusion also typechecks against this witness
   and inside a `Section` (shape checks in the same file).
9. Numerical check of the claim and of the bound used in the proof sketch (Python, double
   precision): a_n(1) = 1, 1.7320508, 2.2360680, 2.5598302, 2.7550533, ... ,
   2.98992 (n = 10), 2.9999879 (n = 20), 3.0000000 (n = 50, 100, 1000); and
   0 <= 3 - a_n(1) <= 6/(n+2) held for every n tested (1, 2, 3, 4, 5, 10, 20, 50, 100, 1000).
10. `grep -i` for model names in both `.v` files: none.
11. Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix):
    `bash verify.sh putnam_1966_a6` -> ALL CHECKS PASSED (corrected file compiles, no
    own-line warnings; the upstream copy fails first at line 43 with "Use of Variable or
    Hypothesis outside sections" [declaration-outside-section]; upstream byte-identity OK).
    Verdict lines:

        toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
        NOTE putnam_1966_a6.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)
        OK   putnam_1966_a6_corrected.v compiles
        OK   putnam_1966_a6_corrected.v ends in Admitted (statement only)
        OK   putnam_1966_a6.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
        ALL CHECKS PASSED

12. Coq 8.18.0 (plain PATH): `bash verify.sh putnam_1966_a6` -> ALL CHECKS PASSED
    (a first run could not download the upstream file for the byte-identity step,
    "curl: (23) Failure writing output to destination", a transient failure in the shared
    download folder; I compared by hand, `tail -n +31 putnam_1966_a6.v | diff - <upstream>`
    empty, and a second run passed that step too). Verdict lines of the second run:

        toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
        NOTE putnam_1966_a6.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)
        OK   putnam_1966_a6_corrected.v compiles
        OK   putnam_1966_a6_corrected.v ends in Admitted (statement only)
        OK   putnam_1966_a6.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
        ALL CHECKS PASSED

## 5. Difficulty estimate and proof sketch for `putnam_1966_a6_corrected_proof.v`

**Difficulty: 3 / 5.** The mathematics is a short downward induction with a clean
invariant plus a squeeze; the work is MathComp bookkeeping (Peano `ge`/`lt` in `ha`,
casts `%:R`, clearing denominators) and the MathComp-Analysis filter/`near` layer.

Sketch. Fix `a`, `ha`. Write L m := m%:R * (m%:R + 2) (so L 1 = 3).

1. *Identity.* `1 + L (m+1) = (m%:R + 2) ^+ 2`, hence `sqrt (1 + L (m+1)) = m%:R + 2`
   (`sqrtr_sqr`, `ger0_norm`) and `L m = m%:R * sqrt (1 + L (m+1))`.
2. *Invariant*, by induction on k with m := n - k, for n >= 1:
   for all k, for all m >= 1 with m + k = n,
   `0 <= a n m` and `0 <= L m - a n m <= m (m+1) (m+2) / (n+2)`.
   - k = 0: m = n, `a n n = n%:R` (first part of `ha`); L n - n = n(n+1) = n(n+1)(n+2)/(n+2).
   - k+1: then m < n and (m+1) + k = n; `ha` gives `a n m = m%:R * sqrt (1 + b)` with
     b := a n (m+1), and the IH gives 0 <= b and 0 <= L(m+1) - b <= (m+1)(m+2)(m+3)/(n+2).
     Then a n m >= 0 (`mulr_ge0`, `sqrtr_ge0`); L m - a n m = m (sqrt(1 + L(m+1)) - sqrt(1 + b))
     >= 0 by `ler_wsqrtr`; and, from (x - y)(x + y) = x^2 - y^2 with `sqr_sqrtr`,
     sqrt(1+L(m+1)) - sqrt(1+b) = (L(m+1) - b) / ((m+2) + sqrt(1+b)) <= (L(m+1) - b)/(m+3)
     because sqrt(1+b) >= sqrt 1 = 1 (`ler_wsqrtr`, `sqrtr1`). So
     L m - a n m <= m/(m+3) * (m+1)(m+2)(m+3)/(n+2) = m(m+1)(m+2)/(n+2).
     Denominators are cleared with `ler_pdivlMr`/`ler_pdivrMr` (all positive), the rest is
     `lra`/`ring` (algebra-tactics: `From mathcomp Require Import lra.` as an extra import).
   Index bookkeeping as in `check.v`: `ha` takes `ge n 1`, `lt m n` (Peano), convert with
   `leP`/`ltP`; `subnSK`, `subnn`.
3. *Specialize* m = 1, k = n - 1: for all n >= 1, `3 - 6 / (n%:R + 2) <= a n 1 <= 3`.
4. *Limit.* `squeeze_cvgr` (normedtype.v) with f n := 3 - 6/(n%:R + 2), g n := a n 1,
   h := cst 3; the `\near \oo` hypothesis from `nbhs_infty_ge 1` and step 3;
   `h @ \oo --> 3` by `cvg_cst`; `f @ \oo --> 3 - 0` by `cvgB` with `cvg_cst` and
   `6 / (n%:R + 2) = 6 * harmonic (n+1)` (`cvg_harmonic`, `cvg_shiftS`, `cvgMr`), or
   directly by `cvgrPdist_lt` + `near_infty_natSinv_lt`.
   Expected `Print Assumptions`: `R` and the three `boolp` classical axioms only.

## 6. Status of the files

| file | status |
|---|---|
| `putnam_1966_a6.v` | upstream statement verbatim + header; does **not** compile (Coq 8.18: the audited error at line 48; Rocq 9.1.1: `declaration-outside-section` at line 43; kept as evidence, as the brief prescribes for `compile` verdicts) |
| `putnam_1966_a6_corrected.v` | corrected statement (one token: `--> (3 : R)`) + compat lines; **compiles on Rocq 9.1.1 and on Coq 8.18.0**, no own-line warnings on either; ends in `Proof. Admitted.` |
| `putnam_1966_a6_statement_is_false.v` / `_vacuous.v` | not written: the statement is neither false nor vacuous (the defect is a compile error), so there is no evidence to derive |
| `putnam_1966_a6_corrected_proof.v` | not part of this phase (proof sketch in §5) |
| `NOTES.md` | this file |

Scratch files (not deliverables), in `.../scratchpad/work/putnam_1966_a6/`: `check.v`
(+ `check.log`, `check91.log`, `check818.log`), `corrected91.log`, `corrected818.log`,
`upstream91.log`, `upstream818.log`, `nocompat1/` (corrected file minus the kind-(1)
compat lines), `verify91.log`, `verify818.log`.
