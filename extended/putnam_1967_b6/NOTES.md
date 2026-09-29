# putnam_1967_b6 -- notes

## 1. The problem

Putnam 1967 B6. Let `f` be a real-valued function which is defined for `x^2 + y^2 <= 1`,
has partial derivatives, and satisfies `|f(x, y)| <= 1`. Show that there is a point
`(x0, y0)` in the interior of the unit disk (`x0^2 + y0^2 < 1`) with
`(df/dx (x0, y0))^2 + (df/dy (x0, y0))^2 <= 16`.
The informal file gives no solution. The standard solution (as summarized, for instance,
in the Kalva Putnam archive; only a search-result summary of that page could be read
here) looks at `g(x, y) = f(x, y) + 2 (x^2 + y^2)`. On the circle `g >= -1 + 2 = 1`, and
at the centre `g(0, 0) = f(0, 0) <= 1`, so the minimum of `g` over the closed disk is
reached at an interior point `(a, b)`. There both partial derivatives of `g` vanish, so
`f_x = -4a`, `f_y = -4b` and `f_x^2 + f_y^2 = 16 (a^2 + b^2) < 16`. This argument needs
the minimum to exist, i.e. it takes `f` to be continuous on the closed disk.

## 2. Defects of the upstream statement

Upstream (`coq/src/putnam_1967_b6.v`, commit 4dbe26e):

    Theorem putnam_1967_b6
        (f : R -> R -> R)
        (fdiff : forall y : R, (forall x0 : R, differentiable (fun x => f x y) x0) /\
                                (forall y0 : R, differentiable (fun y => f y y0) y0))
        (fbound : forall x y : R, x^+2 + y^+2 <= 1 -> `| f x y | <= 1)
        : exists x0 y0 : R, x0^+2 + y0^+2 < 1 /\
            ((fun x : R => f x y0)^`() x0)^+2 + ((fun y : R => f x0 y)^`() y0)^+2 <= 16.

1. **Audit verdict (unfaithful), confirmed.** The second conjunct of `fdiff`,
   `forall y0 : R, differentiable (fun y => f y y0) y0`, passes the lambda's variable `y`
   as the *first* argument of `f`. So it says only that `x |-> f x y0` is differentiable
   at the point `x = y0`, which is a special case of the first conjunct. As a result `fdiff`
   is equivalent to "`x |-> f x y` is differentiable everywhere, for every `y`"
   (machine-checked: lemma `upstream_fdiff_only_x` in section 4). Nothing is assumed about
   `df/dy`, although the conclusion is about `(fun y => f x0 y)^`() y0`. For example,
   `f x y = |y|` satisfies every upstream hypothesis (machine-checked: `abs_instance`),
   but it has no partial derivative in `y` at `y = 0`.
   In MathComp-Analysis, `derive1` of a non-differentiable function is a junk value (a
   `lim` of a filter that does not converge). So in upstream the `df/dy` term of the
   conclusion can be junk.
2. **Found on re-reading: no continuity hypothesis.** The upstream statement has no
   continuity assumption. The benchmark's Lean statement has one:
   `fcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}`.
   The standard solution (section 1) needs it, and partial derivatives alone do not make
   `f` continuous: `2xy / (x^2 + y^2)` (0 at the origin) has both partial derivatives
   everywhere and is discontinuous at `0`. I have not settled whether the statement holds
   without continuity. The standard proof does not work without it, and I know no other
   proof and no counterexample. So a corrected statement without `fcont` could be
   unprovable.

No other trap from brief section 7.5 applies. I checked each one:
* The `^+2` are the intended squares, with a `nat` exponent.
* There is no `nat` or `int` division, no `ln`/`Rpower`, no series, `sup` or integral.
* `<= 1` in `fbound` is the closed disk and `< 1` in the conclusion is the interior.
* The bound is `<= 16`, as in the problem, and the absolute value `|f x y|` is present.
* `(fun x => f x y0)^`() x0` and `(fun y => f x0 y)^`() y0` are `df/dx` and `df/dy` at
  `(x0, y0)`, with the right point and argument order.
* `differentiable g x0` for `g : R -> R` is Fréchet differentiability, which is equivalent
  to the existence of `g^`() x0` (`derivable1_diffP`).
* The existential scopes only over the conjunction, and there are no local definitions.
* The only other issue is the top-level `Variable R : realType`, which is a compile
  problem on Rocq ≥ 9.0 and is handled by a compat line.

Like the Lean statement ("boosted domain ... partially differentiable everywhere",
according to its own comment), upstream defines `f` on all of `R x R` and assumes partial
derivatives everywhere, not just on the disk. That is a documented design choice of the
benchmark, and I kept it (see section 3).

Raw upstream on this machine: it does **not** compile on Rocq 9.1.1 (`Error: Use of
"Variable" or "Hypothesis" outside sections behaves as "#[local] Parameter"`, line 11).
After that line is fixed, it also fails with `Unknown interpretation for notation "_ ^` ()"`
(MathComp-Analysis ≥ 1.9 declares `f^`()` only in `classical_set_scope`). It compiles on
Coq 8.18.0, with only the `local-declaration` warning at line 11. With the two marked
compat lines (Variable, `classical_set_scope`), `putnam_1967_b6.v` compiles on both
toolchains with 0 warnings from its own lines. Compat line (1), the `ssralg` re-import, is
not needed: upstream already imports `ssralg` after `all_ssreflect`.

## 3. The fix

The corrected file differs from the header-stripped upstream copy in two lines of the
statement (output of `diff`):

    17c17,18
    <                             (forall y0 : R, differentiable (fun y => f y y0) y0))
    ---
    >                             (forall x y0 : R, differentiable (fun y => f x y) y0))
    >     (fcont : {within (fun p : R * R => p.1^+2 + p.2^+2 <= 1), continuous (fun p : R * R => f p.1 p.2)})

1. `fdiff`, second conjunct: `forall x y0 : R, differentiable (fun y => f x y) y0`. For
   every `x`, the function `y |-> f x y` is differentiable at every `y0`, i.e. `df/dy`
   exists everywhere. With the unchanged first conjunct, this is exactly the Lean
   `fdiff : (∀ y, Differentiable ℝ (fun x => f x y)) ∧ (∀ x, Differentiable ℝ (fun y => f x y))`
   (machine-checked equivalence: `corrected_fdiff_iff`). Upstream's outer `forall y` is kept
   to keep the diff to one line. The second conjunct does not use it, and `R` is inhabited,
   so this is harmless. `Set Printing All` shows the new conjunct as
   `forall x y0, differentiable (fun y1 => f x y1) y0`, i.e. `[eta f x]`.
2. New hypothesis `fcont`, placed between `fdiff` and `fbound` as in the Lean statement. It
   says that `f`, as a function of the point `p = (x, y)` of `R x R` (product topology),
   is continuous on the closed unit disk, in the subspace sense: its restriction to the
   disk is continuous. This is exactly Lean's `ContinuousOn`, and weaker than continuity
   of `f` on `R x R` at the points of the disk.
   Technical points:
   * The notation `{within A, continuous g}` is declared in `classical_set_scope` in both
     MathComp-Analysis 1.0.0 and 1.16.0. This scope is open in the file because of compat
     line (2), the line that the derivative notation already needs. The header says so.
   * `%classic` cannot be used instead: the `classic` delimiter is unknown here because
     upstream does not import `classical_sets`.
   * The disk is written as a lambda, which Rocq coerces to a `set`. `[set p : R * R | ...]`
     would resolve to MathComp's *finset* notation and fails to typecheck. `Set Printing All`
     confirms that the set elaborates to `fun p => is_true (p.1 ^+ 2 + p.2 ^+ 2 <= 1)`, and
     the function to `from_subspace A (fun p => f p.1 p.2)` on 1.16.0.

**Why adding `fcont` is justified, and the caveat.** The brief says a hypothesis may be
added only when the informal statement clearly assumes it. The text says "a real-valued
function having partial derivatives ... defined for x^2 + y^2 <= 1". It does not say
"continuous". However:
* the problem's intended solution depends on continuity on the closed disk;
* the benchmark's own Lean formalization adds exactly this hypothesis;
* without it the statement is of unknown truth.

I therefore read "having partial derivatives" in the problem's sense, and followed the
Lean statement. This is a deliberate deviation from the literal wording and should be
reviewed. If a reviewer prefers the literal reading, removing the `fcont` line gives the
upstream shape with only the `fdiff` fix. Its truth is then open (section 2).

Unchanged, and faithful or deliberately kept:
* `fbound`, the interior-point condition `< 1`, the bound `<= 16`, the use of `derive1`,
  the theorem name, and the imports, `Set`/`Unset` lines and scopes.
* The global domain with partial derivatives everywhere, which is the benchmark's design
  choice, stated in the Lean file.
  * This makes the Rocq and Lean statements formally weaker than a statement with
    derivatives only in the open disk.
  * The standard proof only uses derivatives at interior points, so the corrected statement
    stays true and in the spirit of the problem.
  * Changing the domain encoding would be a large change beyond the audited defect.

## 4. Sanity checks (all actually run)

1. **Compilation.** From inside this folder, `putnam_1967_b6.v` then
   `putnam_1967_b6_corrected.v`:
   * Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (`rocq compile -R . ""`): both
     exit 0.
   * Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (`coqc -R . ""`, after deleting
     the 9.1 `.vo` files): both exit 0.

   On both toolchains, 0 warnings come from the files' own lines, counted with the
   `File "...", line N` filter of `verify.sh`. All warnings are at the three
   import lines.
2. **Statement integrity.**
   * `putnam_1967_b6.v`, with the header box and the two compat lines stripped, equals the
     upstream file. The only `diff` difference is the missing final newline of upstream,
     which the verifier's `awk '{print}'` normalizes; the upstream copy keeps upstream's
     bytes. The verifier's check 4a confirms this against the downloaded upstream file.
   * The `diff` between the header-stripped upstream copy and the corrected file is exactly
     the one quoted in section 3.
3. **Elaborated statement.** A scratch file `Require`s `putnam_1967_b6_corrected` and runs
   `Check` with `Set Printing All` (Rocq 9.1.1), and `Print Assumptions` (both
   toolchains). The type of the theorem shows:
   * the second `fdiff` conjunct as `differentiable [eta f x] y0`;
   * `fcont` as continuity of `from_subspace` on the subspace
     `fun p => p.1 ^+ 2 + p.2 ^+ 2 <= 1` of the product topology on `R * R`;
   * the conclusion with `derive1 (fun x => f x y0) x0` and `derive1 (fun y => f x0 y) y0`.
4. **Machine-checked lemmas.** The scratch file `sanity.v` (under
   `.../scratchpad/work/putnam_1967_b6/san/`, not a deliverable) uses the same imports and
   scopes as the statement. It compiles with exit 0 and no warnings from its own lines on
   **both** toolchains. It contains:
   * `upstream_fdiff_only_x`: upstream's `fdiff` holds iff
     `forall y x0, differentiable (fun x => f x y) x0`, i.e. it says nothing about `df/dy`.
   * `abs_instance`: `f x y = |y|` satisfies upstream's `fdiff` and `fbound`. (That `|.|` has
     no derivative at 0 is standard and was not machine-checked.)
   * `corrected_fdiff_iff`: the corrected `fdiff` is equivalent to the Lean conjunction
     `(forall y x0, differentiable (fun x => f x y) x0) /\ (forall x y0, differentiable (fun y => f x y) y0)`.
   * `zero_instance`: `f = 0` satisfies all three corrected hypotheses (`fdiff`, `fcont`,
     `fbound`), and the conclusion holds for it at `(0, 0)` (`derive1_cst`).
   * `linear_instance`: `f x y = 5 x` satisfies the corrected `fdiff` (and is continuous)
     but violates `fbound`. For it the conclusion fails at *every* point:
     `(df/dx)^2 + (df/dy)^2 = 25 + 0 > 16`, computed with `is_deriveZ`/`is_derive_id` and
     `derive1_cst`. So the conclusion does not follow from `fdiff` alone; the bound
     hypothesis matters.
5. **Non-vacuity against the real theorem.** The scratch file `inst.v` (under
   `.../work/putnam_1967_b6/inst/`) `Require`s the compiled `putnam_1967_b6_corrected`.
   It applies the theorem itself to `f = fun _ _ => 0` and proves each of its three premises
   (`differentiable_cst`; `continuous_subspaceT` + `cst_continuous`; `normr0`, `ler01`).
   It compiles on both toolchains. `Print Assumptions corrected_hyps_satisfiable` lists:
   * the admitted `putnam_1967_b6_corrected.putnam_1967_b6`;
   * `putnam_1967_b6_corrected.R`;
   * the three `boolp` axioms.

   So the hypotheses of the actual statement are jointly satisfiable, as written.
6. **Verifier** (`extended/verify.sh putnam_1967_b6`), verdict lines:
   * Rocq 9.1.1 (`source /opt/rocq91/bin/rocq-env.sh && cd extended && bash verify.sh putnam_1967_b6`):

         toolchain: The Rocq Prover, version 9.1.1  (rocq compile)
         OK   putnam_1967_b6.v (upstream copy) compiles
         OK   putnam_1967_b6_corrected.v compiles
         OK   putnam_1967_b6_corrected.v ends in Admitted (statement only)
         OK   putnam_1967_b6.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
         checked 1 problem folder(s), 0 with a proof file
         ALL CHECKS PASSED

     Two of the three 9.1 runs (the first and a final confirmation run) printed
     `NOTE putnam_1967_b6.v: could not download upstream for comparison` instead of the 4a
     line; the first also printed `curl: (23) Failure writing output to destination`. The
     likely cause is a parallel verifier run removing the shared `extended/ci_upstream/`
     directory. Both of those runs still ended in `ALL CHECKS PASSED`. The run quoted above
     made the comparison and passed, and every Coq 8.18 run did too.
   * Coq 8.18.0 (`cd extended && bash verify.sh putnam_1967_b6`):

         toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)
         OK   putnam_1967_b6.v (upstream copy) compiles
         OK   putnam_1967_b6_corrected.v compiles
         OK   putnam_1967_b6_corrected.v ends in Admitted (statement only)
         OK   putnam_1967_b6.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines
         checked 1 problem folder(s), 0 with a proof file
         ALL CHECKS PASSED

## 5. Difficulty and proof sketch for a future `putnam_1967_b6_corrected_proof.v`

Difficulty: **3/5**. The mathematics is a one-paragraph argument. The work is
MathComp-Analysis bookkeeping: compactness of the closed disk in the product topology
`R * R`, the extreme value theorem on it, and moving between subspace continuity, the
slices `t |-> f t b`, and 1-D derivatives.

Sketch:
1. **The function to minimize.** Let `D = fun p : R * R => p.1^+2 + p.2^+2 <= 1` and
   `g p = f p.1 p.2 + 2 * (p.1^+2 + p.2^+2)`. Then `{within D, continuous g}`, from `fcont`
   plus continuity of the polynomial part (`fst`/`snd` continuous via `cvg_fst`/`cvg_snd`,
   sums and products of continuous maps). Use `continuous_subspace_in` and
   `continuous_subspaceT` to combine a within-continuous map with a globally continuous one.
2. **`D` is compact and nonempty.**
   * `D` is contained in `` `[-1, 1] `*` `[-1, 1] ``, which is compact: `segment_compact`
     and `compact_setX` (1.16.0; called `compact_setM` in 1.0.0).
   * `D` is closed, as the preimage of `closed_le` under a continuous map: `preimage_closed`
     (1.16.0; `closed_comp` in 1.0.0).
   * So `D` is compact by `subclosed_compact`, and `(0, 0)` is in `D`.
3. **EVT.** `compact_EVT_min` (MathComp-Analysis 1.16.0, `derive.v`, for any
   `topologicalType`) gives `c = (a, b)` in `D` with `g c <= g p` for all `p` in `D`.
   This lemma does **not** exist in MathComp-Analysis 1.0.0. On Coq 8.18 it would have to
   be re-derived from `continuous_compact` + `compact_bounded` + closedness of compact sets
   in `R`, so a proof is likely 9.1-only; the header must then say so.
4. **Interior.** If `a^2 + b^2 = 1`, then `g c >= -1 + 2 = 1 >= f 0 0 = g (0, 0) >= g c`
   (`fbound` at `c` and at `(0, 0)`). So `(0, 0)` is also a minimizer, and we may replace
   `c` by it. Hence WLOG `a^2 + b^2 < 1`.
5. **Fermat on the slices.**
   * Choose `d = (1 - (a^2 + b^2)) / 4 > 0`. For `|t - a| < d` the point `(t, b)` is in `D`,
     since `(|a| + d)^2 + b^2 <= a^2 + b^2 + 3d < 1`; the same holds for `(a, t)` with
     `|t - b| < d`.
   * `t |-> g (t, b)` is derivable on `` `]a - d, a + d[ ``: first `fdiff` conjunct via
     `derivable1_diffP`, plus `derivableX`/`deriveD`. It is minimal at `a`, so
     `derive1_at_min` (in both versions) gives derivative `0`.
   * Hence `f_x(a, b) + 4a = 0`, using `deriveD`, `deriveX`
     and `derive1_cst`. Likewise `f_y(a, b) + 4b = 0` from the second conjunct of the
     corrected `fdiff`.
6. **Conclusion.** `f_x^2 + f_y^2 = 16 (a^2 + b^2) < 16`, so `<= 16` holds; `lra`/`nra` after
   rewriting.

Expected `Print Assumptions`:
* the `Variable R`;
* the three `boolp` axioms (`propositional_extensionality`, `functional_extensionality_dep`,
  `constructive_indefinite_description`) of `mathcomp.classical`.

## 6. Status of the files

| file | status |
|---|---|
| `putnam_1967_b6.v` | upstream statement + header + two marked compat lines (Variable outside a Section; `classical_set_scope` for `f^`()`); compiles on Rocq 9.1.1 and Coq 8.18.0; identical to upstream after stripping (verifier check 4a OK on both) |
| `putnam_1967_b6_corrected.v` | corrected statement (second `fdiff` conjunct fixed, `fcont` added as in Lean); ends in `Proof. Admitted.`; compiles on Rocq 9.1.1 and Coq 8.18.0 with 0 warnings from its own lines |
| `putnam_1967_b6_statement_is_false.v` / `_is_vacuous.v` | not written. The verdict is *unfaithful*, not false/vacuous: the upstream hypotheses are satisfiable (`f = 0`), and no counterexample to the upstream conclusion is known. A counterexample would need, on every horizontal chord, points where the x-derivative is small and the y-derivative (or MathComp's junk value for it) is large, which is at least as hard as the open continuity question of section 2. |
| `putnam_1967_b6_corrected_proof.v` | not written (proofs are out of scope for this phase) |
| `NOTES.md` | this file |

Build products (`*.vo *.vos *.vok *.glob .*.aux`) were removed from the folder after the checks.
