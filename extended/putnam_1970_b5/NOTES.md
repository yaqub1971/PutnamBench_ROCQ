# putnam_1970_b5 -- notes

Audit verdict: **naming** (the theorem has the wrong name; the mathematics is faithful).
Upstream commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 of PutnamBench, file
`coq/src/putnam_1970_b5.v`.

## 1. The problem

Putnam 1970 B5. Let u_n be the "ramp" (clamp) function u_n(x) = -n if x <= -n, x if
-n < x <= n, and n otherwise. Let F be a function from the reals to the reals. Show that
F is continuous if and only if u_n o F is continuous for every natural number n.
PutnamBench's informal file gives no solution text ("None."); nothing is to be
determined, it is a pure "show that".

## 2. Defect(s) in the upstream statement

The upstream file (kept verbatim, after a header comment and one marked compat line, in
`putnam_1970_b5.v`) is

```coq
Variable R : realType.
Theorem putnam_1970_b5_solution
    (ramp : int -> (R -> R) := fun (n : int) => (fun (x : R) => if x <= -n%:~R then -n%:~R else (if -n%:~R <= x <= n%:~R then x else n%:~R)))
    (F : R -> R)
    : continuous F <-> (forall n : nat, continuous (ramp (n%:Z) \o F)).
Proof. Admitted.
```

**Defect (the audited one): naming.** The theorem is declared `putnam_1970_b5_solution`.
The problem is a "show that" with no answer to determine; in PutnamBench the suffix
`_solution` names the answer `Definition` of "find/determine" problems, and this file has
no such definition. The theorem itself should be `putnam_1970_b5`, the name of
PutnamBench's informal and Lean statements. A harness or a proof file that looks for the
theorem `putnam_1970_b5` does not find it (checked: `Fail Check putnam_1970_b5_solution`
succeeds against the corrected module, and the upstream module has no `putnam_1970_b5`).

**Re-reading the whole statement against the trap list of the brief (section 7.5): no
further defect.** Item by item (backed by the `Set Printing All` output and the lemmas of
section 4):

* `(ramp : ... := ...)` is a local definition (let-binding) in the theorem's binders. The
  "local definition meant as a hypothesis" trap does not apply: ramp *is* meant as a
  definition of u_n, and the Lean statement expresses the same thing with a variable plus
  the equation `ramp_def`.
* The middle test is `-n <= x <= n` where the problem (and Lean) has `-n < x <= n`. The
  two differ only at x = -n, and there the first branch `x <= -n` has already fired, so
  ramp n is exactly u_n. Machine-checked for every integer n and every x
  (`ramp_is_u`, section 4, check 4).
* `-n%:~R` elaborates to `GRing.opp (intmul 1 n)` (opposite of the image of n in R),
  checked under `Set Printing All`; `n%:~R` is the image of an `int` in R (no `nat` or
  `int` division, no exponent anywhere).
* `ramp (n%:Z)` with `n : nat`: the quantifier ranges over the natural numbers, as in the
  problem. n = 0 is included; u_0 is the constant 0 (checked, `u0`), which is continuous,
  so including it is harmless whichever convention for "natural numbers" is meant.
* `continuous g` for `g : R -> R` is MathComp-Analysis' `forall x, continuous_at x g`
  (`g @ x --> g x`), i.e. continuity at every real point, as in the problem (checked in
  the printed type). `\o` is `ssrfun.comp`, so `ramp n \o F = fun x => ramp n (F x)`.
* `<=` is the order of R; the comparisons are real, not `nat`/`int`.
* No `Series`, limits of sequences, integrals, `sup`, `ln`/`Rpower`, `Q`, indexing,
  divisibility, sums/products, absolute values or existentials occur. The only
  hypothesis-like binder is the arbitrary `F`, so the statement cannot be vacuous.

**Rocq 9.1 compatibility (not a mathematical defect):** the raw upstream file does not
compile on Rocq 9.1.1 (checked): `Variable R : realType.` outside a `Section` is an error
(`Use of "Variable" or "Hypothesis" outside sections behaves as "#[local] Parameter" or
"#[local] Axiom".`, upstream line 13). On Coq 8.18.0 the raw file compiles, with a
`local-declaration` warning at that line. With only the Variable compat line (kind (2) of
the brief), it compiles on Rocq 9.1.1 / MathComp 2.5.0, and the elaborated theorem type
is byte-identical under `Set Printing All` with and without the ssralg re-import (kind
(1)). The statement uses no `1` and no `%:R` (only `-` and `%:~R`), so kind (1) is not
needed and was not added; kind (3) does not apply (no derivative notation, and
`classical_set_scope` is already opened by upstream).

## 3. The fix

`putnam_1970_b5_corrected.v` differs from the upstream copy `putnam_1970_b5.v` in exactly
one line (besides the header comment); both carry the same marked compat line:

```diff
 Local Open Scope ring_scope.
 Local Open Scope classical_set_scope.

+Set Warnings "-declaration-outside-section,-local-declaration". (* compat: ... *)   (in both files)
 Variable R : realType.
-Theorem putnam_1970_b5_solution
+Theorem putnam_1970_b5
     (ramp : int -> (R -> R) := fun (n : int) => (fun (x : R) => if x <= -n%:~R then -n%:~R else (if -n%:~R <= x <= n%:~R then x else n%:~R)))
     (F : R -> R)
     : continuous F <-> (forall n : nat, continuous (ramp (n%:Z) \o F)).
 Proof. Admitted.
```

Why the corrected statement is faithful: renaming changes nothing mathematical (the two
elaborated theorem types print identically under `Set Printing All`, up to the module and
theorem names and the indentation that the longer name induces; checked on both
toolchains). The statement is exactly the problem's equivalence: the let-bound ramp is
u_n (check 4), and the theorem implies, and by the same rewriting is implied by,
`forall F, continuous F <-> (forall n : nat, continuous (u n \o F))` with u written
literally as in the problem (`informal_form`, check 4). Nothing is weakened; there are no
hypotheses to add or drop; there is no `_solution` definition.

Comparison with the Lean statement (`putnam_1970_b5.lean`):

```lean
theorem putnam_1970_b5
(ramp : ℤ → (ℝ → ℝ))
(ramp_def : ramp = fun (n : ℤ) => (fun (x : ℝ) => if x ≤ -n then (-n : ℝ) else (if -n < x ∧ x ≤ n then x else (n : ℝ))))
(F : ℝ → ℝ)
: Continuous F ↔ (∀ n : ℕ, Continuous ((ramp n) ∘ F)) :=
```

The Rocq statement follows it: same name after the fix, same ramp (let-binding instead of
variable + defining equation; `-n <= x` instead of `-n < x` in the middle test, which is
equivalent as shown above), same equivalence, same quantification over ℕ. The informal
statement is followed exactly.

## 4. Sanity checks actually run

All on this machine, under both toolchains unless stated: Rocq 9.1.1 / MathComp 2.5.0 /
MathComp-Analysis 1.16.0 (Nix, `source /opt/rocq91/bin/rocq-env.sh`, `rocq compile`) and
Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (Ubuntu 24.04, `coqc`). Scratch
files are in the scratch directory `work/putnam_1970_b5/` (`raw91/`, `raw818/`,
`novar91/`, `withssr91/`, `b91/`, `b818/`, `reading.v`).

1. **Both deliverable files compile, with no warning from their own lines.**
   `rocq compile -R . "" putnam_1970_b5.v` and `... putnam_1970_b5_corrected.v`: exit 0;
   the 30 warnings of each log all point at the first upstream import line
   (`From mathcomp Require Import all_algebra all_ssreflect.`, line 45 resp. 43). After
   deleting the `.vo` files, `coqc -R . "" ...` on both: exit 0; 23 warnings each, all at
   that same import line. No `Error`, no warning at the compat line, the `Variable` or the
   `Theorem`.
2. **Raw upstream file** (no compat lines): Rocq 9.1.1 exit 1 with the Variable error at
   line 13 (quoted in section 2); Coq 8.18.0 exit 0 with 23 import-line warnings plus the
   `local-declaration` warning at line 13. Upstream + Variable compat line only: Rocq 9.1.1
   exit 0 (30 import-line warnings). Upstream + Variable compat line + ssralg re-import
   block: exit 0, and `Check putnam_1970_b5_solution` under `Set Printing All` prints
   byte-identical output with and without the re-import (so it is not needed). On Coq
   8.18.0 the raw upstream module and the upstream copy with the compat line give
   identical `Set Printing All` output for the theorem.
3. **Byte identity and minimal diff.** Both files were assembled by a script from the
   upstream bytes (not retyped). Stripping the header box and the `(* compat: ... *)`
   line of `putnam_1970_b5.v` (the verifier's `strip` function) and diffing with the
   upstream file: identical (also re-downloaded from GitHub at the pinned commit: same
   bytes as the local copy). `diff` of the two deliverables below their headers: exactly
   one changed line, `Theorem putnam_1970_b5_solution` -> `Theorem putnam_1970_b5`. On both
   toolchains, `Check` of `putnam_1970_b5.putnam_1970_b5_solution` and of
   `putnam_1970_b5_corrected.putnam_1970_b5` under `Set Printing All` give identical output
   after replacing module/theorem names and squeezing whitespace (the only raw
   difference is the indentation of continuation lines).
4. **Reading of the statement** (`reading.v`, which `Require`s the corrected module; exit
   0 on both toolchains):
   * `Check (putnam_1970_b5 : forall F : R -> R, continuous F <-> (forall n : nat,
     continuous (fun x => ramp_up (n%:Z) (F x))))` succeeds, where `ramp_up` is the
     upstream ramp body as a top-level definition (so the let-binding is exactly that
     function and `\o` is plain composition).
   * `ramp_is_u : forall (n : int) (x : R), ramp_up n x = u n x`, proved, where `u` is the
     problem's u_n written with `(-n < x) && (x <= n)` in the middle test. `Print
     Assumptions`: only the three `boolp` axioms and the module's `R`.
   * `informal_form : forall F : R -> R, continuous F <-> (forall n : nat, continuous
     (u (n%:Z) \o F))`, proved from `putnam_1970_b5` by rewriting with `ramp_is_u`
     (`funext`); `Print Assumptions` lists `putnam_1970_b5` (admitted), the three `boolp`
     axioms and `R`.
   * `opp_embed : - (n%:~R) = (- n)%:~R` (so the parse of `-n%:~R` does not matter).
   * small values, proved: `ramp_up 0 x = 0` for all x; `ramp_up 1 (1/2) = 1/2`;
     `ramp_up 1 3 = 1`; `ramp_up 1 (-3) = -1`.
   * non-vacuity/instantiation: `continuous (@id R)` proved (`cvg_id`), and
     `proj1 (putnam_1970_b5 id) id_cont` typechecks (the forward direction applies to a
     concrete continuous F).
   * `Fail Check putnam_1970_b5_solution` succeeds (the old name is gone).
5. **No model names** in the files (grep over the folder: no hit).
6. `Print Assumptions` of the theorem: not applicable in this phase (both files end in
   `Admitted`).
7. **Verifier**, under both toolchains (verdict lines quoted verbatim; a first run of each
   printed `NOTE putnam_1970_b5.v: could not download upstream for comparison` after a
   `curl: (23) Failure writing output to destination`, which comes from concurrent runs
   of the verifier sharing and deleting its `ci_upstream/` download directory; rerun
   without that interference, both runs show the full identity check):

   `(source /opt/rocq91/bin/rocq-env.sh && cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1970_b5)`
   ```
   toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
   OK   putnam_1970_b5.v (upstream copy) compiles
   OK   putnam_1970_b5_corrected.v compiles
   OK   putnam_1970_b5_corrected.v ends in Admitted (statement only)
   OK   putnam_1970_b5.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
   checked 1 problem folder(s), 0 with a proof file
   ALL CHECKS PASSED
   ```
   `(cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1970_b5)`
   ```
   toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
   OK   putnam_1970_b5.v (upstream copy) compiles
   OK   putnam_1970_b5_corrected.v compiles
   OK   putnam_1970_b5_corrected.v ends in Admitted (statement only)
   OK   putnam_1970_b5.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
   checked 1 problem folder(s), 0 with a proof file
   ALL CHECKS PASSED
   ```

## 5. Difficulty estimate and proof sketch

**Difficulty: 2 / 5** (elementary real analysis; the work is filter/`near` bookkeeping in
MathComp-Analysis). A proof should be possible on both toolchains (no `ftc`-style
library facts are needed), though lemma names differ between MathComp-Analysis 1.0.0 and
1.16.0.

Mathematical proof.
(=>) Each u_n is continuous (it is max(-n, min(x, n)), or: 1-Lipschitz), and a
composition of continuous functions is continuous.
(<=) Fix x0 and pick n : nat with |F x0| < n - 1 (Archimedes). Then u_n(F x0) = F x0.
By continuity of g = u_n o F at x0, near x0 we have |g x - F x0| < 1, hence |g x| < n,
hence -n < g x < n. But u_n(y) lies strictly inside (-n, n) only when u_n(y) = y (if
y <= -n then u_n y = -n; if y > n then u_n y = n). So F x = g x near x0, i.e. F and g
agree on a neighbourhood of x0, and F is continuous at x0 because g is
(`near_eq_cvg`-style transfer).

Rocq plan (names checked in the MathComp-Analysis 1.16.0 sources under `src91/analysis`):

1. First rewrite the let-bound ramp into a closed form:
   `ramp n x = Num.max (- n%:~R) (Num.min x n%:~R)` for `0 <= n` (case analysis on the
   comparisons, `ltNge`, `lt_total`/`real` ordering of a `realType`), or keep the `if`
   form and prove continuity pointwise.
2. (=>) `continuous_comp` (`topology_structure.v:263`) with continuity of the clamp:
   `continuous_min` / `continuous_max` (`normedtype_theory/normed_module.v:986, 996`)
   together with `cvg_id` and `cst_continuous` (`topology_structure.v:360`); or a direct
   epsilon-delta argument via `cvgr_dist_lt`, using `|u_n a - u_n b| <= |a - b|`.
3. (<=) For `x0`, take `n` = the integer part of `|F x0|` plus 2 (MathComp's
   archimedean truncation of a nonnegative real; the exact lemma names differ between
   MathComp 2.1 and 2.5 and were not looked up in this phase). From `H n x0` get `\forall x \near x0, `|ramp n (F x) - F x0| < 1`
   (`cvgr_dist_lt`, `pseudometric_normed_Zmodule.v:253`, after `ramp n (F x0) = F x0`),
   deduce `\forall x \near x0, ramp n (F x) = F x` by the case analysis of the
   mathematical proof, and conclude with `near_eq_cvg` (`classical/filter.v:914`) or
   `cvg_trans` plus the eventual equality.
4. Expected `Print Assumptions`: only the statement's `R` and the three `boolp` axioms.

## 6. Status of each file

| file | status |
|---|---|
| `putnam_1970_b5.v` | upstream text verbatim after a header comment, plus the one marked compat line (Variable outside a Section); compiles on Rocq 9.1.1 and on Coq 8.18.0 (checks 1, 7); verified identical to upstream apart from header and compat line (checks 3, 7). |
| `putnam_1970_b5_corrected.v` | corrected statement (theorem renamed `putnam_1970_b5`, nothing else changed), ends in `Proof. Admitted.`; compiles on Rocq 9.1.1 and on Coq 8.18.0 with no warning from its own lines (checks 1, 7). |
| `putnam_1970_b5_statement_is_false.v` / `_vacuous.v` | not written: the verdict is `naming`; the statement is a true theorem (proof sketch in section 5) and its only binder is an arbitrary F, so there is nothing to refute and no contradiction to exhibit. |
| `putnam_1970_b5_corrected_proof.v` | not written in this phase (proofs are out of scope). Sketch in section 5. |
| `NOTES.md` | this file. |
