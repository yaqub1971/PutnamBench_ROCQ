# putnam_1966_a1 -- notes

## 1. The problem

Putnam 1966 A1. Let `a_n = n/2` for `n` even and `a_n = (n-1)/2` for `n` odd, i.e.
`a_n = floor(n/2)`: `a_0, a_1, a_2, ... = 0, 0, 1, 1, 2, 2, 3, 3, ...` (the problem lists the
sequence from `a_1` on as `0, 1, 1, 2, 2, 3, ...`). Let `f(n)` be the sum of its first `n`
terms, `f(n) = a_1 + ... + a_n`, which equals `a_0 + ... + a_n` because `a_0 = 0`; in closed
form `f(n) = floor(n^2/4) = floor(n/2) * ceil(n/2)`. Show that `x y = f(x+y) - f(x-y)` for
all positive integers `x > y`. (Proof: `x+y` and `x-y` have the same parity, so
`(x+y)^2` and `(x-y)^2` leave the same remainder modulo 4 and
`floor((x+y)^2/4) - floor((x-y)^2/4) = ((x+y)^2 - (x-y)^2)/4 = x y`.)

## 2. Defect of the upstream statement

Upstream (`coq/src/putnam_1966_a1.v`, commit 4dbe26e) defines the summand, in `ring_scope`,
as

    (f : nat -> int := fun n => \sum_(0 <= m < n + 1) (if (~~odd m) then (m%:Z)/2 else (m%:Z-1)/2))

`x / y` in `ring_scope` is `x * y^-1`, and the inverse of MathComp's `int` (a `unitRingType`
whose only units are `1` and `-1`) is the identity function: `Definition invz n : int := n.`
in `mathcomp/algebra/ssrint.v`. Hence `(m%:Z)/2 = m%:Z * 2` and `(m%:Z-1)/2 = (m%:Z-1) * 2`:
the encoded sequence is `0, 0, 4, 4, 8, 8, 12, 12, ...`, four times the intended
`0, 0, 1, 1, 2, 2, 3, 3, ...`, the encoded `f` is four times the intended `f`
(`f 0..6 = 0, 0, 4, 8, 16, 24, 36` instead of `0, 0, 1, 2, 4, 6, 9`), and the theorem claims
`x y = 4 x y`. At `x = 2, y = 1` it asserts `(2 * 1)%:Z = f 3 - f 1 = 8 - 0`, i.e. `2 = 8`.
So the upstream statement is **false**, as the audit verdict says (false, machine-checked);
`putnam_1966_a1_statement_is_false.v` derives `False` from it.

The rest of the statement was re-read against the trap list of the brief (section 7.5) and
found faithful:

* Sum range `0 <= m < n + 1`, i.e. `m = 0, ..., n` inclusive (the Lean statement's
  `Finset.Icc 0 n`): this is `a_1 + ... + a_n` since `a_0 = 0`, the "sum of the first n
  terms" of the problem's sequence `0, 1, 1, 2, 2, 3, ...` (whose first term is `a_1 = 0`).
  The other conceivable reading, `a_0 + ... + a_(n-1)`, would make the identity false already
  at `x = 2, y = 1` (`f 3 - f 1 = 1 <> 2`), so the inclusive range is the right one.
* The bound `n + 1` elaborates to `addn n 1` (checked with `Set Printing All`), not to a
  ring operation; `(x * y)%:Z` elaborates to `Posz (muln x y)`.
* `gt x 0`, `gt y 0`, `gt x y` are Peano's `>` on `nat`: "positive integers x > y".
* `Nat.add x y` and `Nat.sub x y` are exact because `x > y`.
* `~~odd m` selects the even branch, as in the problem; `f` is a genuine local definition
  (`:=`), not a hypothesis in disguise.
* Side effect of the upstream `Set Implicit Arguments`: `x` and `y` are implicit arguments of
  the theorem (they occur in `gt x 0`), so it must be instantiated as `@putnam_1966_a1 2 1 ...`.
  This changes nothing in the statement.

## 3. The fix

One line of the statement changes, in two subterms:

    before:  (f : nat -> int := fun n => \sum_(0 <= m < n + 1) (if (~~odd m) then (m%:Z)/2 else (m%:Z-1)/2))
    after:   (f : nat -> int := fun n => \sum_(0 <= m < n + 1) (if (~~odd m) then (m %/ 2)%:Z else ((m - 1) %/ 2)%:Z))

`%/` is MathComp's Euclidean division of natural numbers (`divn`, from `div.v` in
`all_ssreflect`), applied to the natural number `m` before the cast `%:Z` to `int`; in the
odd branch `m - 1` is exact since `m` is odd, hence `>= 1`. `Set Printing All` shows the two
new terms as `Posz (divn m 2)` and `Posz (divn (subn m 1) 2)`. The encoded terms are now
`0, 0, 1, 1, 2, 2, 3, 3, ...`, exactly `n/2` for even `n` and `(n-1)/2` for odd `n`.

Comparison with the Lean statement (`putnam_1966_a1.lean`): Lean has `f : ℤ → ℤ`,
`f n = ∑ m ∈ Finset.Icc 0 n, (if Even m then m / 2 else (m - 1)/2)` with `Int` division
(floor division, exact here since all arguments are nonnegative), and `x y : ℤ` with
`x > 0 ∧ y > 0 ∧ x > y`. The Rocq statement keeps upstream's choice of `nat` for `x`, `y`
and the summation index; on `m >= 0` the integer division of the Lean statement and the
natural-number division used here are the same function, so the corrected `f` agrees with
the Lean `f` at every argument at which it is evaluated (`x + y`, `x - y >= 1`). The only
deviation from the Lean shape is that the division is done on `nat` before the cast rather
than on `int` after it; the `int` variant `(m%:Z %/ 2)%Z` would need the extra import
`intdiv` (not among upstream's imports) and an `int_scope` delimiter, i.e. a larger diff for
the same function. The alternative `(m./2)%:Z` (MathComp's `half`) is also the same function
but drops the problem's explicit even/odd case distinction, so the `if` is kept.

Nothing else changed: same imports, same `Set`/`Unset` lines, same scope, same theorem name,
same hypotheses, same conclusion. No compat lines are needed in any of the files: no
`Variable` outside a `Section`, `ssralg` is already imported after `all_ssreflect`, no
derivative notation.

## 4. Sanity checks

Toolchains: Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix,
the primary one) and Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1
(Ubuntu 24.04). Items 1 and 3-7 were run on both toolchains. Item 2 is a plain `diff`, which
does not depend on the toolchain.

1. Compilation, from inside this folder, in dependency order, once per toolchain (build
   products deleted in between):
   * Rocq 9.1.1: `rocq compile -R . "" putnam_1966_a1.v`, then `..._corrected.v`, then
     `..._statement_is_false.v`. All three exit 0. In each file, the only warnings (27) point
     at the `From mathcomp Require Import` line: MathComp library warnings (overridden
     notations, ambiguous coercion paths, `all_ssreflect` deprecation). No warning comes from
     the files' own lines.
   * Coq 8.18.0: the same with `coqc -R . "" ...`. All three exit 0, and the only warnings
     (23 per file) are again at the import line.
   * Both runs count warnings with the same `File "...", line N` filter as `extended/verify.sh`.
2. Statement integrity: `putnam_1966_a1.v` with its header box removed (the `strip` filter of
   `extended/verify.sh`) is byte-identical to the upstream file (`diff` empty, no compat
   lines); `diff` of the header-stripped upstream copy against the header-stripped corrected
   file shows exactly the one line quoted in section 3. The only other difference is a newline:
   upstream has no final newline and the corrected file has one. This was re-checked after
   the latest header edits.
3. Evidence: `putnam_1966_a1_statement_is_false.v` compiles on both toolchains. On each one
   its `Print Assumptions` prints exactly one axiom, the admitted upstream theorem
   `putnam_1966_a1 : let f := ... in forall x y : nat, ...` -- nothing else (no classical
   axiom is involved; the derivation is `have h := @putnam_1966_a1 2 1 (@le_S 1 1 (le_n 1))
   (le_n 1) (le_n 2). rewrite unlock in h; vm_compute in h. discriminate.`; `rewrite unlock`
   is needed because MathComp's `bigop` is an `HB.lock`ed constant that `vm_compute` cannot
   unfold).
4. Small-value checks in a scratch file (`probe.v`, same imports and scope as the statement),
   proved by `rewrite unlock; vm_compute`. It compiles with exit 0 on both toolchains, and the
   only warnings are at its import line:
   * terms `m = 0..7` of the upstream summand: `[:: 0; 0; 4; 4; 8; 8; 12; 12]`; of the
     corrected summand: `[:: 0; 0; 1; 1; 2; 2; 3; 3]`;
   * upstream `f 0..6 = (0, 0, 4, 8, 16, 24, 36)`; corrected `f 0..6 = (0, 0, 1, 2, 4, 6, 9)`
     (= `floor(n^2/4)`);
   * the corrected theorem's conclusion, in its exact shape
     `(x * y)%:Z = f (Nat.add x y) - f (Nat.sub x y)`, holds at
     `(x, y) = (2, 1), (3, 1), (3, 2), (4, 1), (5, 3), (7, 4)` (six lemmas, all closed by
     computation);
   * the upstream conclusion at `(2, 1)` reduces to `2 = 8` and implies `False` (lemma
     `inst_up`).
5. Non-vacuity: the hypotheses are satisfiable, e.g. `gt 2 0 /\ gt 1 0 /\ gt 2 1` (lemma
   `hyps_ok` in `probe.v`, proved by `le_S`/`le_n`). The corrected statement is not trivially
   true: with the upstream `f` the same conclusion is false, so its truth depends on `f`.
6. Proof sketch check: the sketch of section 5 was compiled as a scratch file on both
   toolchains. Section 5 gives the outcome.
7. Verifier, run after all edits, with the verdict lines quoted verbatim:
   * `(source /opt/rocq91/bin/rocq-env.sh && cd extended && bash verify.sh putnam_1966_a1)`,
     toolchain `The Rocq Prover, version 9.1.1  (rocq compile)`:

         OK   putnam_1966_a1.v (upstream copy) compiles
         OK   putnam_1966_a1_corrected.v compiles
         OK   putnam_1966_a1_corrected.v ends in Admitted (statement only)
         OK   putnam_1966_a1_statement_is_false.v compiles
         OK   putnam_1966_a1_statement_is_false.v: assumes the admitted upstream theorem putnam_1966_a1 (False follows from it)
         OK   putnam_1966_a1.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
         ALL CHECKS PASSED

   * `(cd extended && bash verify.sh putnam_1966_a1)`, toolchain
     `The Coq Proof Assistant, version 8.18.0  (coqc)`:

         OK   putnam_1966_a1.v (upstream copy) compiles
         OK   putnam_1966_a1_corrected.v compiles
         OK   putnam_1966_a1_corrected.v ends in Admitted (statement only)
         OK   putnam_1966_a1_statement_is_false.v compiles
         OK   putnam_1966_a1_statement_is_false.v: assumes the admitted upstream theorem putnam_1966_a1 (False follows from it)
         curl: (23) Failure writing output to destination
         NOTE putnam_1966_a1.v: could not download upstream for comparison
         ALL CHECKS PASSED

     In that run the upstream comparison was skipped because the download failed
     (curl error 23), which is not a statement defect. The same comparison passed in the
     Rocq 9.1 run just before it, and the manual `diff` of item 2 against the local upstream
     copy is empty.

## 5. Difficulty and proof sketch for `putnam_1966_a1_corrected_proof.v`

Difficulty: **2/5** (routine: one induction with `big_nat_recr`, parity bookkeeping with
`half`/`uphalf`, and a polynomial identity; the only fiddly parts are the let-bound `f`, the
`Nat.add`/`Nat.sub`/`gt` from the standard library, and pushing `Posz` through the sum).

Sketch (MathComp only; `From mathcomp Require Import zify` for `lia` on `nat`/`int` with
`divn`, `half`, `uphalf`, `odd`, which zify translates to `Z.div`/`Z.modulo` by 2):

1. `termE m : (if ~~ odd m then (m %/ 2)%:Z else ((m - 1) %/ 2)%:Z) = (m./2)%:Z`
   (`case: ifP => hm; congr Posz; lia`): both branches are `floor(m/2)`.
2. `sum_half n : \sum_(0 <= m < n.+1) m./2 = n./2 * uphalf n` by induction on `n`:
   `big_nat1` for `n = 0`; `big_nat_recr //=` for the step, after which `n.+1./2` is already
   `uphalf n` and `uphalf n.+1` is `(n./2).+1` (`half`/`uphalf` are a mutual fixpoint, so
   `/=` unfolds them). The remaining goal
   `n./2 * uphalf n + uphalf n = uphalf n * (n./2).+1` is closed by `lia`. A plain `mulnSr`/`mulnC` rewrite does not match the goal that `big_nat_recr //=`
   leaves.
3. `fE n : f n = (n./2 * uphalf n)%:Z`: `rewrite /f addn1 (eq_bigr _ (fun m _ => termE m))`,
   push `Posz` out of the sum with `big_morph Posz PoszD (erefl _)`, then `sum_half`.
   `natr_sum` + `natz` is an alternative that was not tried. (The theorem's `f` is a let-binder: introduce it
   with `move=> f` or unfold with `cbv zeta`.)
4. Main goal: `move=> x y _ _ /ltP hxy`. Replace `Nat.add x y`, `Nat.sub x y` by
   `(x + y)%N`, `(x - y)%N` (`by []`: they are convertible to `addn`/`subn`). Then write
   `x = (d + y)%N` (`exists (x - y)%N; rewrite subnK // ltnW`), so `x + y = d + y + y` and
   `x - y = d` (`addnK`), and rewrite with `fE`. Every one of these auxiliary `nat` equations
   must carry the `%N` delimiter, because the file opens `ring_scope`: without it `+`/`-`
   are parsed as ring operations and the equation does not typecheck (seen on Rocq 9.1).
   The three facts `(d + y + y)%N./2 = (d./2 + y)%N`,
   `uphalf (d + y + y)%N = (uphalf d + y)%N` and `(d./2 + uphalf d)%N = d` are each `lia`
   (`halfD`, `uphalf_half`, `odd_double_half` should also work by hand, but that was not
   tried). After
   `rewrite h1 h2 -{1}h3` what remains is the polynomial identity
   `((a + b + y) * y)%:Z = ((a + y) * (b + y))%:Z - (a * b)%:Z` in `a = d./2`, `b = uphalf d`,
   which `lia` closes. `PoszM`/`PoszD` + `ring` is an alternative that was not tried.

`Print Assumptions`: `Closed under the global context` (no `Variable`, no classical axiom;
`zify`/`lia` add none). This was observed on the scratch run below.

Scratch check of this sketch: `sketch.v` in the scratch directory (not a deliverable). It
holds the corrected statement verbatim under the name `putnam_1966_a1_sketch`, with the same
imports plus `zify`.

* **First run failed.** It stopped at step 2 with `Error: The LHS of mulnSr (_ * _.+1)%N
  does not match any subterm of the goal`: a plain `mulnSr` rewrite does not match the goal
  that `big_nat_recr //=` leaves.
* **Fixes.** Step 2 is now closed by `lia`. In step 4 the auxiliary equations now carry
  `%N`. Without it, `Nat.add x y = x + y` and `exists d, x = d + y` fail to typecheck in
  `ring_scope`.
* **Final run passed on both toolchains.** Exit 0 on Rocq 9.1.1 / MathComp 2.5.0 and on
  Coq 8.18.0 / MathComp 2.1.0. The only warnings are at the import line, and
  `Print Assumptions putnam_1966_a1_sketch` prints `Closed under the global context` on both.

The text of steps 1-4 above matches that final `sketch.v`, so the sketch has been checked.
In the proof phase it can be copied almost unchanged into `putnam_1966_a1_corrected_proof.v`.
The difficulty estimate stays at 2/5 (routine).

## 6. Status of the files

| file | status |
|---|---|
| `putnam_1966_a1.v` | upstream statement + header comment, no compat lines; compiles on Rocq 9.1.1 and Coq 8.18.0; header-stripped text byte-identical to upstream |
| `putnam_1966_a1_corrected.v` | corrected statement, one line differs from upstream (two subterms); compiles on Rocq 9.1.1 and Coq 8.18.0; ends in `Proof. Admitted.` |
| `putnam_1966_a1_statement_is_false.v` | derives `False` from the admitted upstream theorem at `x = 2, y = 1`; compiles on Rocq 9.1.1 and Coq 8.18.0; `Print Assumptions` lists only `putnam_1966_a1` on both |
| `putnam_1966_a1_corrected_proof.v` | not written in this phase (proof phase) |
| `NOTES.md` | this file |

Build products (`*.vo *.vos *.vok *.glob .*.aux`) were removed from the folder after the checks.
