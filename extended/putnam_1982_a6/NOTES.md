# putnam_1982_a6 -- notes

Audit verdict: **vacuous (machine-checked)**; re-reading the statement found four further
defects (section 2). Upstream commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 of PutnamBench,
file `coq/src/putnam_1982_a6.v`. Files in this folder: `putnam_1982_a6.v` (upstream copy,
evidence), `putnam_1982_a6_corrected.v` (proposed fix, ends in `Proof. Admitted.`),
`putnam_1982_a6_statement_is_vacuous.v` (machine-checked vacuity proof), this file.

## 1. The problem

Putnam 1982 A6. Let `b` be a bijection of the positive integers and `x_1, x_2, ...` real
numbers such that (i) `|x_n|` is strictly decreasing, (ii) `|b(n) - n| * |x_n| -> 0`,
(iii) `sum_(k=1)^n x_k -> 1`. Prove or disprove: then `sum_(k=1)^n x_(b(k)) -> 1`.
Answer (informal solution): disprove, the limit need not be 1. So the Rocq encoding is
"(for all b, x satisfying (i)-(iii), the rearranged partial sums tend to 1) <-> False",
with `putnam_1982_a6_solution := False` (kept).

## 2. Defect(s) in the upstream statement

Upstream text (verbatim after the header in `putnam_1982_a6.v`):

```coq
Require Import Nat Reals Coquelicot.Coquelicot.
Open Scope R.
Definition putnam_1982_a6_solution := False.
Theorem putnam_1982_a6
    (a: nat -> R) 
    : ((Series a = 1 /\ forall (i j: nat), le i j -> Rabs (a i) > Rabs (a j)) /\
    forall (f: nat -> nat), Lim_seq (fun i => Rabs (INR (f i - i)) * Rabs (a i)) = 0 -> exists f', forall x, f' (f x) = x /\ f (f' x) = x -> 
    Series (fun i => a (f i)) = 1) <-> putnam_1982_a6_solution.    
Proof. Admitted.
```

**Defect 1 (vacuous, the audit verdict).** `forall (i j: nat), le i j -> Rabs (a i) > Rabs (a j)`
at `i = j` demands `|a i| > |a i|`. So the left side of the biconditional is False for every
`a`, and `False <-> putnam_1982_a6_solution` (= `False <-> False`) holds with no mathematics.
Machine-checked: `putnam_1982_a6_statement_is_vacuous.v` closes the verbatim upstream theorem
with `split; [intros [[_ h] _]; exact (Rlt_irrefl _ (h 0%nat 0%nat (le_n 0))) | intros []].`
Problem's condition: strictly decreasing, i.e. `i < j -> |a i| > |a j|`.

Re-reading the whole statement against the trap list of the brief (section 7.5):

**Defect 2 (quantifier scope).** `a` is a parameter of the theorem, outside the biconditional.
Even with `lt` the theorem would read "for every `a`: (hypotheses on `a` and for all `f` ...) <->
False", i.e. "for EVERY `a` satisfying the hypotheses the claim fails for some `f`", which is
not the problem ("NOT for all `a`, `b` does the claim hold") and is false (take an absolutely
convergent `a`, e.g. `a n = (1/2)^(n+1)`: every rearrangement sums to 1). The problem's
universal quantifier over the sequence must be inside the left side, as in the Lean statement.

**Defect 3 (bijection garbled).** `exists f', forall x, f' (f x) = x /\ f (f' x) = x -> Series ... = 1`
parses as `exists f', forall x, ((f' (f x) = x /\ f (f' x) = x) -> Series ... = 1)`: the
inverse property is a premise of the conclusion inside an existential, not a hypothesis that
`f` is a bijection. (For injective `f` the existential is met by `f' (f x) := x + 1`, whatever
the series do.)

**Defect 4 (nat subtraction).** `INR (f i - i)` is truncated `nat` subtraction: it is `0`
whenever `f i <= i`, so `Rabs (INR (f i - i))` is `max(f(i) - i, 0)`, not `|f(i) - i|`
(machine-checked instance: `Rabs (INR (0 - 3)) = 0` while `Rabs (INR 0 - INR 3) = 3`,
section 4). This weakens hypothesis (ii).

**Defect 5 (Series is not convergence).** `Series u = Rbar.real (Lim_seq (sum_n u))` and
Coquelicot's `Lim_seq u` is by definition `(LimSup_seq u + LimInf_seq u) / 2`
(`Lim_seq.v`, line 1212 of Coquelicot 3.4.1), so `Series a = 1` does not say that the partial
sums converge (partial sums oscillating between `3/2` and `1/2` have `Series = 1`; this
example is by the definition, not machine-checked). As a hypothesis (iii) this is weaker than
the problem's; as the conclusion `Series (fun i => a (f i)) = 1` it is weaker than "the
rearranged partial sums tend to 1", so its negation would be stronger than the problem's
answer. The problem needs `is_series` (convergence of the partial sums to 1) in both places,
as the Lean statement's `Tendsto ... (𝓝 1)`.

Not a defect: `Lim_seq (fun i => ...) = 0` for hypothesis (ii). The sequence is nonnegative,
and for nonnegative `u`, `Lim_seq u = 0 <-> is_lim_seq u 0` (machine-checked, section 4). It
is nevertheless replaced by `is_lim_seq ... 0` for clarity and uniformity with `is_series`.
Other traps checked and absent: no `Rpower`/`ln`, no `pow` with a misplaced exponent, no
`sum_n` inclusive-bound issue (the partial sums are inside `is_series`), the absolute values
`Rabs (a i)` and (after the fix) `Rabs (INR (f i) - INR i)` are present, no local
definitions standing for hypotheses.

Indexing: the problem indexes from 1, the Rocq statement from 0. This is an exact
correspondence, not a shift error: for a bijection `b` of the positive integers put
`f(n) = b(n + 1) - 1` (a bijection of `nat`) and `a(n) = x_(n+1)`; then
`|f(n) - n| = |b(n+1) - (n+1)|`, `|a n|` strictly decreasing iff `|x_n|` is,
`sum_(k=0)^n a k = sum_(k=1)^(n+1) x_k` and `sum_(k=0)^n a (f k) = sum_(k=1)^(n+1) x_(b(k))`,
and conversely.

## 3. The fix

```diff
 Require Import Nat Reals Coquelicot.Coquelicot.
 Open Scope R.
 Definition putnam_1982_a6_solution := False.
 Theorem putnam_1982_a6
-    (a: nat -> R) 
-    : ((Series a = 1 /\ forall (i j: nat), le i j -> Rabs (a i) > Rabs (a j)) /\
-    forall (f: nat -> nat), Lim_seq (fun i => Rabs (INR (f i - i)) * Rabs (a i)) = 0 -> exists f', forall x, f' (f x) = x /\ f (f' x) = x -> 
-    Series (fun i => a (f i)) = 1) <-> putnam_1982_a6_solution.    
+    : (forall (a: nat -> R),
+    (is_series a 1 /\ forall (i j: nat), lt i j -> Rabs (a i) > Rabs (a j)) ->
+    forall (f: nat -> nat), is_lim_seq (fun i => Rabs (INR (f i) - INR i) * Rabs (a i)) 0 -> (exists f', forall x, f' (f x) = x /\ f (f' x) = x) ->
+    is_series (fun i => a (f i)) 1) <-> putnam_1982_a6_solution.
 Proof. Admitted.
```

Line by line: `(a: nat -> R)` moves inside the left side as `forall (a: nat -> R),` (defect 2);
`Series a = 1` -> `is_series a 1` (defect 5) and `le` -> `lt` (defect 1), and the `/\` joining
this block to the rest becomes `->` (the block is now a hypothesis of the claim, not a conjunct
of the left side); `INR (f i - i)` -> `INR (f i) - INR i` (defect 4), `Lim_seq (...) = 0` ->
`is_lim_seq (...) 0` (clarity, equivalent), and the bijection condition becomes the
parenthesised hypothesis `(exists f', forall x, f' (f x) = x /\ f (f' x) = x) ->` (defect 3);
`Series (fun i => a (f i)) = 1` -> `is_series (fun i => a (f i)) 1` (defect 5). The trailing
blanks of two upstream lines are dropped. Library (Coquelicot), names, the order of the
hypotheses and `putnam_1982_a6_solution := False` are kept.

Why it is faithful: the left side now says "for every real sequence `a` whose partial sums
tend to 1 and whose absolute values strictly decrease, and every bijection `f` of `nat` with
`|f(n) - n| |a_n| -> 0`, the partial sums of `a (f n)` tend to 1", which is the problem's claim
(0-indexed, section 2), and the theorem says this claim is equivalent to False, i.e. is
disproved, which is the problem's answer.

Comparison with the Lean statement:

```lean
theorem putnam_1982_a6 :
  (∀ b : ℕ → ℕ, ∀ x : ℕ → ℝ,
      BijOn b (Ici 1) (Ici 1) →
      StrictAntiOn (fun n : ℕ => |x n|) (Ici 1) →
      Tendsto (fun n : ℕ => |b n - (n : ℤ)| * |x n|) atTop (𝓝 0) →
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, x k) atTop (𝓝 1) →
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, x (b k)) atTop (𝓝 1))
  ↔ putnam_1982_a6_solution   -- := False
```

The corrected Rocq statement agrees hypothesis by hypothesis: `BijOn b (Ici 1) (Ici 1)` <->
`f` has a two-sided inverse on `nat`; `StrictAntiOn |x|` <-> `lt i j -> Rabs (a i) > Rabs (a j)`;
the integer difference `|b n - (n : ℤ)|` <-> the real difference `Rabs (INR (f i) - INR i)`;
`Tendsto` of the partial sums <-> `is_series`. Deviations: 0-based instead of 1-based indices
(exact correspondence, section 2), and the order of the hypotheses follows upstream (`a`'s
conditions first, then `f`'s), which is logically irrelevant.

## 4. Sanity checks run (scratch files under the work directory, not in this folder)

All compiled with exit 0 on BOTH toolchains (Rocq 9.1.1 / Coquelicot 3.4.4 via
`rocq compile`, and Coq 8.18.0 / Coquelicot 3.4.1 via `coqc`, `.vo` files deleted in between).

1. The deliverables: `putnam_1982_a6.v`, `putnam_1982_a6_corrected.v`,
   `putnam_1982_a6_statement_is_vacuous.v` each compile on both toolchains; the only warnings
   are at the `Require` line (Rocq 9.1.1: "Loading Stdlib without prefix is deprecated"; both:
   Coquelicot's "New coercion path [real; Finite] : Rbar >-> Rbar ..."). None from the files'
   own lines. The first 8 lines of the vacuity file's statement are identical (`diff`) to the
   upstream file; `putnam_1982_a6.v` minus its header is identical to the upstream file
   (verifier, section 6).
2. Vacuity proof: `Print Assumptions putnam_1982_a6` in `putnam_1982_a6_statement_is_vacuous.v`
   prints `ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec`,
   `FunctionalExtensionality.functional_extensionality_dep` (the axioms of the standard reals)
   and nothing else, on both toolchains.
3. `sanity.v` (definition `corr_lhs` = the corrected left side copied verbatim):
   * `a0 n := (/2)^n * /2`; `a0_series : is_series a0 1` (via `is_series_geom`,
     `is_series_scal_r`), `a0_strict : lt i j -> Rabs (a0 i) > Rabs (a0 j)`;
   * `hyps_satisfiable`: with `a = a0` and `f = id`, all three hypotheses of the corrected
     claim hold (series to 1 with strictly decreasing `|a|`; `|f i - i| |a i| -> 0`;
     `f` has an inverse). So the corrected statement is not vacuous in the upstream way;
   * `inst_holds`: its conclusion also holds for that instance (`is_series (a0 o id) 1`);
   * `nat_sub_trap : Rabs (INR (0 - 3)) = 0 /\ Rabs (INR 0 - INR 3) = 3` (defect 4).
   `Print Assumptions` of `hyps_satisfiable` and `inst_holds`:
   `ClassicalDedekindReals.sig_forall_dec`, `FunctionalExtensionality.functional_extensionality_dep`.
4. `link2.v` (`Require putnam_1982_a6_corrected sanity.`, with the deliverable
   `putnam_1982_a6_corrected.v` copied byte-for-byte into the scratch directory):
   `Lemma link : sanity.corr_lhs <-> putnam_1982_a6_corrected.putnam_1982_a6_solution.
   Proof. exact putnam_1982_a6_corrected.putnam_1982_a6. Qed.` type-checks, i.e. the
   definitions in `sanity.v` are, by conversion, exactly the corrected theorem's left side.
   `Print Assumptions link`: only the admitted `putnam_1982_a6_corrected.putnam_1982_a6`.
5. `limeq.v`: `Lemma Lim_seq_0_iff (u : nat -> R) : (forall n, 0 <= u n) -> (Lim_seq u = 0 <-> is_lim_seq u 0).`
   proved (via `LimInf_le`, `LimSup_LimInf_seq_le`, `ex_lim_LimSup_LimInf_seq`,
   `Lim_seq_correct`, `is_lim_seq_unique`); assumptions: the three standard-reals axioms.
   So replacing upstream's `Lim_seq ... = 0` by `is_lim_seq ... 0` does not change meaning.

Not checked by machine: that the corrected statement is TRUE (i.e. that a counterexample
exists). That is the content of the problem; a sketch is in section 5.

## 5. Difficulty and proof sketch

Difficulty for a full Rocq proof: **4** (an explicit counterexample with a piecewise-defined
sequence and a piecewise-defined bijection; no deep theory, but heavy bookkeeping with
limits, partial sums and a bijection of `nat` in Coquelicot).

Direction `False -> ...` is trivial. For `... -> False` one must build `a`, `f` satisfying the
hypotheses whose rearranged partial sums do not tend to 1. Key observation: the penalty
`|f(p) - p| |a_p|` is measured with `|a_p|` at the POSITION `p`, so a term of large index-size
may be moved far to the right, to a position where `|a|` is tiny.

Construction (one route, checked on paper). Let `d` be a strictly decreasing positive
sequence tending to 0, and `a_n = (-1)^n d_n / L` with `L = sum (-1)^n d_n > 0` (alternating
series test; Stdlib `AltSeries.alternated_series`, then `is_lim_seq_Reals`/`sum_n_Reals`
to get `is_series a 1`). Choose rounds `j = 1, 2, ...` with intervals `[A_j, B_j]`,
`B_j ~ A_j e^j`, on which `d_p ~ 1/p` (harmonic profile), followed by a gap
`(B_j, A_(j+1))`, `A_(j+1) ~ 2 j B_j`, on which `d_p` lies in `[1/(2 j B_j), 1/(j B_j)]` (a
sharp drop), strictly decreasing throughout.
In round `j`, remove the set `R_j` of even (positive) indices in `[A_j, B_j]` with density
`1/j` (about `(B_j - A_j)/j` indices). The bijection `f`: positions `<= B_j` take, in
increasing order, the indices `<= B_j` not in `R_j` followed by the `|R_j|` indices just above
`B_j`; positions `B_j + 1 .. B_j + |R_j|` take the indices of `R_j`; `f` is the identity
elsewhere up to the next round.
* Penalty inside `[A_j, B_j]`: the shift at position `p` is at most `#(R_j ∩ [A_j, p]) <= p/j`,
  times `d_p ~ 1/p`: `O(1/j) -> 0`. Positions `B_j + 1 .. B_j + |R_j|`: shift `<= B_j`, times
  `d_p <= 1/(j B_j)`: `<= 1/j -> 0`.
* Partial sum at `n = B_j`: `S'_n = S_n - sum_(R_j) a + (|R_j| terms of size <= 1/(j B_j))`,
  and `sum_(R_j) a ~ (1/L) * (1/j) * sum_(p=A_j)^(B_j) 1/p ~ (1/L)(1/j) * j = 1/L`, while
  `S_n -> 1`. So `S'_(B_j) -> 1 - 1/L` along `j`, not 1 (constants to be tuned; any fixed
  nonzero offset suffices).
Library facts needed: `AltSeries.alternated_series` (or a direct Cauchy argument),
`is_lim_seq` algebra (`is_lim_seq_le_le`, `is_lim_seq_ext_loc`), harmonic-sum bounds via
`ln` (`sum_f_R0` of `1/k` between `ln` values), and a hand-made bijection of `nat` with its
inverse (defined by blocks; `lia`-heavy). No `ftc`, so the proof should work on both toolchains.

## 6. Status of each file

| file | status |
|---|---|
| `putnam_1982_a6.v` | upstream statement verbatim (header prepended, no compat lines needed). Compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04). |
| `putnam_1982_a6_corrected.v` | corrected statement (`Proof. Admitted.`). Compiles on both toolchains, no warning from its own lines. |
| `putnam_1982_a6_statement_is_vacuous.v` | upstream statement verbatim closed by a one-line proof using only the `le i i` contradiction. Compiles on both toolchains; `Print Assumptions`: the three standard-reals axioms only. |
| `putnam_1982_a6_corrected_proof.v` | not written (out of scope for this phase). |

Verifier output, Rocq 9.1.1 (`source /opt/rocq91/bin/rocq-env.sh && cd extended && bash verify.sh putnam_1982_a6`):

```
toolchain: The Rocq Prover, version 9.1.1  (rocq compile)

### putnam_1982_a6
OK   putnam_1982_a6.v (upstream copy) compiles
OK   putnam_1982_a6_corrected.v compiles
OK   putnam_1982_a6_corrected.v ends in Admitted (statement only)
OK   putnam_1982_a6_statement_is_vacuous.v compiles
OK   putnam_1982_a6_statement_is_vacuous.v: only library axioms / the statement's R: ClassicalDedekindReals.sig_not_dec ClassicalDedekindReals.sig_forall_dec FunctionalExtensionality.functional_extensionality_dep 
OK   putnam_1982_a6.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines

checked 1 problem folder(s), 0 with a proof file
ALL CHECKS PASSED
(build products and logs removed)
```

Coq 8.18.0 (plain PATH, `cd extended && bash verify.sh putnam_1982_a6`):

```
toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)

### putnam_1982_a6
OK   putnam_1982_a6.v (upstream copy) compiles
OK   putnam_1982_a6_corrected.v compiles
OK   putnam_1982_a6_corrected.v ends in Admitted (statement only)
OK   putnam_1982_a6_statement_is_vacuous.v compiles
OK   putnam_1982_a6_statement_is_vacuous.v: only library axioms / the statement's R: ClassicalDedekindReals.sig_not_dec ClassicalDedekindReals.sig_forall_dec FunctionalExtensionality.functional_extensionality_dep 
OK   putnam_1982_a6.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines

checked 1 problem folder(s), 0 with a proof file
ALL CHECKS PASSED
(build products and logs removed)
```
