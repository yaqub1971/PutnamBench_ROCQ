# putnam_1969_b3 — notes

Audit verdict: **compile** (one-token fix `--> (1 : R)`; statement otherwise faithful).
This folder: the upstream statement kept as evidence, the corrected statement, and these
notes. No `_statement_is_false` / `_statement_is_vacuous` file: the statement is neither
false nor vacuous (see §2 and §4), so there is no `False` to derive.

## 1. The problem

Putnam 1969 B3: a real sequence T satisfies T_n T_(n+1) = n for every n >= 1, and
T_n / T_(n+1) -> 1 as n -> oo. Show that pi T_1^2 = 2. (The informal file gives no
solution.) The first condition fixes the whole sequence from T_1 (T_(n+1) = n / T_n, and
T_1 != 0 is forced); the ratio T_n / T_(n+1) = T_n^2 / n tends to pi T_1^2 / 2 along odd
n and to 2 / (pi T_1^2) along even n (Wallis' product), so the second condition holds
exactly when pi T_1^2 = 2.

## 2. The defect in the upstream statement

The upstream file does not compile. Its hypothesis `hT2` is

    (hT2 : (fun n => (T n)/(T n.+1)) @ \oo --> 1)

The bare numeral `1` elaborates, in `ring_scope`, to `1` of an unknown semiring, and the
`-->` notation needs a point of a filtered type; unification fails. Reproduced here
(`coqc` on the verbatim upstream text, Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0):

    File "./putnam_1969_b3.v", line 17, characters 47-48:
    Error:
    In environment
    T : nat -> R
    hT1 : forall n : nat, (n >= 1)%coq_nat -> T n * T n.+1 = n%:R
    The term "1" has type "GRing.SemiRing.sort ?s0"
    while it is expected to have type "Filtered.sort ?s".

(identical to the audit's build log). On Rocq 9.1.1 / MathComp 2.5.0 /
MathComp-Analysis 1.16.0 the verbatim file stops earlier, at `Variable R : realType.`
outside a `Section` (`declaration-outside-section`, an error since Rocq 9.0); with the
repository's marked compat lines added (scratch copy) it stops at the same `--> 1` token
(`The term "1" has type "GRing.PzSemiRing.sort ?s0" while it is expected to have type
"Filtered.sort ?s"`). It is a pure elaboration problem: the intended type is obviously
`R`, the `realType` of the statement. Mathematically the upstream text is a faithful
transcription of the Lean statement.

## 3. The fix and why it is faithful

Exactly one line of the statement changes, by one token (diff of the two `.v` files with
the header comments and the marked compat lines removed, using the `strip` filter of
`extended/verify.sh`):

    17c17
    <     (hT2 : (fun n => (T n)/(T n.+1)) @ \oo --> 1)
    ---
    >     (hT2 : (fun n => (T n)/(T n.+1)) @ \oo --> (1 : R))

`(1 : R)` is the real number 1, so `hT2` says: the sequence `n |-> T n / T n.+1`
converges (in the norm topology of `R`, via `Import numFieldNormedType.Exports`) to 1 —
checked in the scratch file: `hT2` is equivalent, by `cvgrPdist_lt`, to
`forall e > 0, \forall n \near \oo, |1 - T n / T n.+1| < e`. That is the Lean hypothesis
`Tendsto (fun n => T n / T (n + 1)) atTop (𝓝 1)` and the informal
lim T_n / T_(n+1) = 1. Everything else is untouched and matches Lean line by line:
- `hT1 : forall n : nat, ge n 1 -> (T n) * (T (n.+1)) = n%:R` = Lean
  `∀ n : ℕ, n ≥ 1 → (T n) * (T (n + 1)) = n` (1-based: `T 0` is unconstrained in both,
  as the informal sequence starts at T_1);
- conclusion `pi * (T 1%nat) ^+ 2 = 2` = Lean `Real.pi * (T 1)^2 = 2`; `pi` is
  `mathcomp.analysis.trigo.pi` (checked with `Locate pi` / `About pi` in the scratch file;
  defined as twice the zero of `cos` in [0, 2], i.e. the real pi), `^+ 2` is the square,
  `2 : R`.
I follow the Lean statement completely; there is nothing to deviate from.

Re-reading against the trap list of the brief (§7.5), none applies:
- no `nat` division, no `Rpower`/`ln`/`expR`; `^+ 2` is a genuine natural exponent;
- division by zero: MathComp's `x / 0 = 0`, but for n >= 1 `hT1` forces `T n.+1 != 0`
  (and `T n != 0`), proved in the scratch file (`T_neq0`), so `T n / T n.+1` is the real
  ratio for every n >= 1; the n = 0 term (possibly `T 0 / T 1` with arbitrary `T 0`) does
  not affect the limit;
- `-->` to the point `(1 : R)` is convergence to a finite limit (not `ex_lim_seq`-style,
  no `+oo`);
- indexing is 1-based as in the problem (`ge n 1`, `T 1%nat`); `>=` (not `>`) as in Lean;
- no series, integrals, sums, `sup`, `Q`, `int`, divisibility, absolute values, local
  `(h : Prop := ...)` definitions, or existentials.

Compat lines (marked `(* compat: ... *)`, byte-identical to the lines of the root file
`putnam_1962_b5_corrected.v`, checked with `grep -xF`):
- kind (2) before `Variable R : realType.` (needed on Rocq >= 9.0);
- kind (1), the bracketed re-import `From mathcomp Require Import ssralg.`, inserted after
  the second upstream import line (the placement used by the other folders of `extended/`).
  It is needed: upstream imports `all_algebra all_ssreflect` in that order, and without the
  re-import Rocq 9.1 / MathComp 2.5 rejects `n%:R` in `hT1` (checked on a scratch copy:
  `line 17, characters 58-62: The term "1" has type "BaseUMagma.sort ?s" while it is
  expected to have type "Algebra.BaseAddUMagma.sort ?V"`).
- kind (3) (derivative notations) does not apply.
On Coq 8.18 / MathComp 2.1 the compat lines are no-ops.

## 4. Sanity checks actually run

1. `putnam_1969_b3_corrected.v`, Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0
   (`source /opt/rocq91/bin/rocq-env.sh && rocq compile -R . "" putnam_1969_b3_corrected.v`):
   exit 0, `.vo` produced; 30 warnings, all at line 41 (the first
   `From mathcomp Require Import` line: library warnings); none from the file's own lines.
2. Same file, Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (`coqc -R . ""`, after
   deleting the `.vo` files): exit 0, `.vo` produced; 23 warnings, all at line 41.
3. `putnam_1969_b3.v` (upstream copy): Coq 8.18 — exit 1 at line 50 (= upstream line 17),
   characters 47-48, the error of §2; Rocq 9.1 — exit 1 at line 46
   (`Variable R : realType.`, `declaration-outside-section`). Expected: the file is kept
   verbatim precisely because it does not compile.
4. Byte-identity: `tail -n +34 putnam_1969_b3.v` is byte-identical (`cmp`) to the upstream
   `coq/putnam_1969_b3.v`. With header and marked compat lines stripped,
   `putnam_1969_b3_corrected.v` differs from upstream in exactly one line (shown in §3).
5. Scratch file `.../scratchpad/work/putnam_1969_b3/check/check.v` (the corrected file plus
   checks; compiled with exit 0 on BOTH toolchains, no warning from its own lines):
   - `Locate pi` / `About pi`: `pi` is `mathcomp.analysis.trigo.pi : forall {R : realType}, R`.
   - `hT2_meaning`: `hT2`'s proposition `<->` the epsilon-N definition with `|1 - T n / T n.+1|`
     (proof `exact: cvgrPdist_lt`).
   - Consequences of `hT1` (in a `Section` with `hT1` as hypothesis): `T_neq0`
     (`T n != 0` for n >= 1), `T_rec` (`T n.+1 = n%:R / T n`), `T_ratio`
     (`T n / T n.+1 = T n ^+ 2 / n%:R`), and `T_small`: `T 2 = (T 1)^-1`,
     `T 3 = 2 * T 1`, `T 4 = 3 / (2 * T 1)`, `T 5 = 8 / 3 * T 1` — all proved.
   - Satisfiability of `hT1` (partial non-vacuity, machine-checked): for every `c != 0` the
     recursively defined `Tw c` (`Tw c 1 = c`, `Tw c (m+2) = (m+1) / Tw c (m+1)`) satisfies
     `hT1` verbatim (`Tw_ok`, proved).
   - The statement is not trivially true: `hT2_needed` proves
     `~ (forall T, hT1 T -> pi * T 1 ^+ 2 = 2)` (with `T := Tw 2` it would give `4 pi = 2`,
     contradicting `pi_ge2`), so the conclusion genuinely depends on `hT2`.
   - `Print Assumptions putnam_1969_b3` (of the admitted statement): only the theorem itself.
6. Non-vacuity of `hT1 /\ hT2` together is not machine-checked (it is equivalent to Wallis'
   formula, i.e. to the problem itself). Numerical check instead (Python, double precision,
   `numeric.py` in the scratch folder), iterating `T_(n+1) = n / T_n`:
   - T_1 = sqrt(2/pi): T_n/T_(n+1) = 0.9995001 (n = 1000), 0.999995 (n = 10^5),
     0.9999995 (n = 10^6 and 10^6 + 1) -> 1: the hypotheses are satisfiable, with
     pi T_1^2 = 2.
   - T_1 = 1: ratios 0.6366195 (n = 10^6) and 1.5707955 (n = 10^6 + 1), i.e. 2/pi and pi/2;
     T_1 = 0.8: 0.9947179 / 1.0053091 = 2/(pi T_1^2) and pi T_1^2/2. So `hT2` fails whenever
     pi T_1^2 != 2, consistent with the claim.
7. `grep -il` for model names in the folder: none.
8. Verifier, verdict lines (both runs end with "ALL CHECKS PASSED"):

   Rocq 9.1.1 (`source /opt/rocq91/bin/rocq-env.sh && cd extended && bash verify.sh putnam_1969_b3`):

       toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
       NOTE putnam_1969_b3.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)
       OK   putnam_1969_b3_corrected.v compiles
       OK   putnam_1969_b3_corrected.v ends in Admitted (statement only)
       OK   putnam_1969_b3.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
       checked 1 problem folder(s), 0 with a proof file
       ALL CHECKS PASSED

   Coq 8.18.0 (`cd extended && bash verify.sh putnam_1969_b3`):

       toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
       NOTE putnam_1969_b3.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)
       OK   putnam_1969_b3_corrected.v compiles
       OK   putnam_1969_b3_corrected.v ends in Admitted (statement only)
       OK   putnam_1969_b3.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
       checked 1 problem folder(s), 0 with a proof file
       ALL CHECKS PASSED

## 5. Difficulty estimate and proof sketch for `putnam_1969_b3_corrected_proof.v`

**Difficulty: 4 / 5.** The algebra and the limit bookkeeping are routine, but the proof
needs Wallis' product, which is in neither MathComp-Analysis (1.0.0 or 1.16.0) nor
Coquelicot (grep for "wallis": no hit) and must be built from integrals of powers of `sin`
over [0, pi/2] with MathComp-Analysis' Lebesgue integral. The needed FTC / integration by
parts lemmas live in `ftc.v`, which exists in MathComp-Analysis 1.16.0 but not in 1.0.0,
so the proof file will realistically compile only on Rocq 9.1 (to be stated in its header).

Sketch. Fix `T`, `hT1`, `hT2`.
1. *Algebra* (as in the scratch file): `T n != 0` for n >= 1, `T n.+1 = n%:R / T n`,
   `T n / T n.+1 = T n ^+ 2 / n%:R`. By induction on k:
   `T (2k+1) = T 1 * P k` with `P k = \prod_(1 <= j < k.+1) (2j)%:R / (2j - 1)%:R`.
   Hence along odd indices `T (2k+1) / T (2k+2) = T 1 ^+ 2 * (P k ^+ 2 / (2k+1)%:R)`.
2. *Subsequence*: from `hT2` and `k |-> 2k+1` tending to `\oo` (e.g. `cvg_comp` with a
   `nbhs_infty`/`leq`-monotonicity argument), `T 1 ^+ 2 * (P k ^+ 2 / (2k+1)) --> 1`.
3. *Wallis*: `P k ^+ 2 / (2k+1)%:R --> pi / 2`. With I m = \int_0^{pi/2} sin^m:
   I 0 = pi/2, I 1 = 1 (`continuous_FTC2` with F = -cos, `cos_pihalf`, `cos0`);
   I (m+2) = (m+1)/(m+2) * I m (`Rintegration_by_parts` with F = -cos, G = sin^(m+1),
   `sin2cos2`); 0 < I (m+1) <= I m (0 <= sin <= 1 on [0, pi/2], `le_Rintegral`-type
   monotonicity). Then I (2k) = (pi/2) / P k and I (2k+1) = P k / (2k+1), and the squeeze
   (2k+1)/(2k+2) = I(2k+2)/I(2k) <= I(2k+1)/I(2k) <= 1 gives
   I(2k+1)/I(2k) = P k ^+ 2 / ((2k+1) * pi/2) --> 1 (`squeeze_cvgr`).
4. *Conclusion*: by `cvgM` and uniqueness of limits (`cvg_unique` / `cvg_lim` in the
   Hausdorff space R), `T 1 ^+ 2 * (pi/2) = 1`, i.e. `pi * T 1 ^+ 2 = 2` (`lra`/field
   manipulation, `pi_gt0`).
Expected `Print Assumptions`: the Variable `R` and the three `boolp` classical axioms only.

## 6. Status of the files

| file | status |
|---|---|
| `putnam_1969_b3.v` | upstream statement verbatim (byte-identical after the header) + header; does **not** compile on either toolchain (the audited error on Coq 8.18; the `Variable` error first on Rocq 9.1); kept as evidence, as the brief prescribes for `compile` verdicts |
| `putnam_1969_b3_corrected.v` | corrected statement (one token: `--> (1 : R)`) + marked compat lines; **compiles** on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0, no own-line warnings; ends in `Proof. Admitted.` |
| `putnam_1969_b3_statement_is_false.v` / `_vacuous.v` | not written: the statement is neither false nor vacuous (the defect is a compile error), so there is no evidence to derive |
| `putnam_1969_b3_corrected_proof.v` | not part of this phase (proof sketch in §5) |
| `NOTES.md` | this file |

Scratch files (not deliverables), under
`.../scratchpad/work/putnam_1969_b3/` (the session scratch directory):
`check/check.v` (+ `log91`, `log818`), `numeric.py` / `numeric.out`, `upc91/` (upstream plus
compat lines on Rocq 9.1), `nocompat1/` (corrected without the ssralg re-import on Rocq 9.1),
`corr91.log`, `corr818.log`, `upcopy91.log`, `upcopy818.log`, `verify91.out`, `verify818.out`.
