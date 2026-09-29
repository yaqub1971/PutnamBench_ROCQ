# putnam_1974_a1 -- notes

Audit verdict: **unfaithful (incomplete)**. Upstream commit
4dbe26ef21563af851eedaeb82d936fe1f94fc52 of PutnamBench, file `coq/src/putnam_1974_a1.v`.
Files in this folder: `putnam_1974_a1.v` (upstream copy, evidence), `putnam_1974_a1_corrected.v`
(proposed fix, ends in `Proof. Admitted.`), this file. No `_statement_is_false` /
`_statement_is_vacuous` file: the upstream statement is neither false nor vacuous (it is the
true upper-bound half of the problem; see section 2).

## 1. The problem

Putnam 1974 A1. Call a set of positive integers *conspiratorial* if no three of them are
pairwise relatively prime. What is the largest number of elements in any conspiratorial
subset of the integers 1 through 16? Answer: **11** (e.g. the multiples of 2 or 3,
{2, 3, 4, 6, 8, 9, 10, 12, 14, 15, 16}: among any three of them two are even or two are
multiples of 3; and no 12-element subset works).

## 2. Defect(s) in the upstream statement

The upstream text (kept verbatim, after a header comment and three marked compat lines, in
`putnam_1974_a1.v`) is

```coq
Definition putnam_1974_a1_solution : nat := 11%nat.
Theorem putnam_1974_a1
    (conspiratorial : set int -> Prop := fun A => forall a b c : int, (a \in A) -> (b \in A) -> (c \in A) -> (a > 0) -> (b > 0) -> (c > 0) -> (a <> b) -> (b <> c) -> (c <> a) -> (~ coprimez a b \/ ~ coprimez b c \/ ~ coprimez c a))
    : forall A : set int, A `<=` [set x : int | 1 <= x <= 16] -> conspiratorial A -> A #<= [set : 'I_(putnam_1974_a1_solution)].
Proof. Admitted.
```

**Defect (the audited one): only half of "the largest number" is stated.** The conclusion says
that every conspiratorial `A` included in [1, 16] has at most `putnam_1974_a1_solution = 11`
elements (`A #<= [set : 'I_11]`: an injection of `A` into an 11-element type exists). It never
says that some conspiratorial subset has 11 elements. An upper bound stays true when it is
increased, so the conclusion with 12 (or 13, ...) in place of 11 follows from it (machine-checked
as `upstream_monotone` in section 4): the theorem would be just as provable with the wrong answer
`putnam_1974_a1_solution := 12`, i.e. it does not determine the answer the problem asks for.
The statement itself is true (it is the hard half of the problem), so it is not false; its
let-bound `conspiratorial` is a definition, not a hypothesis, so it is not vacuous.

**Re-reading the whole statement against the trap list of the brief (section 7.5):** no further
defect.

* `conspiratorial`: for all `a b c` in `A`, positive and pairwise distinct (`a <> b`, `b <> c`,
  `c <> a`), not all three pairs are coprime (`~ coprimez a b \/ ~ coprimez b c \/ ~ coprimez c a`).
  That is exactly "no three of them are pairwise relatively prime" ("three of them" = three
  distinct elements). `coprimez a b` is `gcdz a b == 1`. The positivity guards restrict the
  condition to positive elements; the problem only defines the notion for sets of positive
  integers, and every `A` the theorem quantifies over is included in [1, 16], so the guards are
  always satisfied and change nothing. The let-binding `(conspiratorial : ... := ...)` is the
  intended use (it names a definition of the problem), not the "hypothesis written as a local
  definition" trap.
* `a \in A` on `A : set int` is MathComp-Analysis membership (`in_setE : (x \in A) = A x`),
  checked in use by the proofs of section 4.
* `[set x : int | 1 <= x <= 16]` is the inclusive range "1 through 16" (ring-scope `<=` on
  `int`); no `nat` subtraction/division, no `^`, no logarithms, no series, no `sup`.
* `A #<= [set : 'I_11]` is "`A` has at most 11 elements" (`'I_11` has exactly 11 elements;
  the 0-indexing of ordinals is irrelevant for a cardinality). `#<=` is a `bool` coerced to `Prop`.
* The answer 11 is correct (exhaustive search, section 4, item 4). Theorem and `_solution` names are
  the problem's (no naming issue).

**Rocq 9.1 / MathComp 2.5 compatibility (not a mathematical defect):** the upstream file does
not compile on the CI toolchain: MathComp 2.5's `all_ssreflect`, imported after `all_algebra`
(upstream's order), overrides the ring notation `1`, and Rocq 9.1.1 stops at upstream line 15:

```
File "./putnam_1974_a1.v", line 15, characters 48-49:
Error: ...
The term "1" has type "BaseUMagma.sort ?s0" while it is expected to have type
 "Order.Preorder.sort ?s".
```

(the `1` of `1 <= x <= 16`). The upstream file verbatim does compile on Coq 8.18.0 / MathComp
2.1.0. There is no top-level `Variable` and no derivative notation, so only compat kind (1) of
the brief applies; both files carry those three marked lines (after the two upstream import
lines), in the upstream copy because it needs them to compile on Rocq 9.1.

## 3. The fix

`putnam_1974_a1_corrected.v` differs from the upstream text only in the conclusion (plus the
header comment and the three marked compat lines, identical in both files):

```diff
 From mathcomp Require Import classical_sets cardinality.
+Set Warnings "-notation-overridden". (* compat: ... *)
+From mathcomp Require Import ssralg. (* compat: ... *)
+Set Warnings "notation-overridden". (* compat: restore the default. *)
 ...
-    : forall A : set int, A `<=` [set x : int | 1 <= x <= 16] -> conspiratorial A -> A #<= [set : 'I_(putnam_1974_a1_solution)].
+    : (exists A : set int, A `<=` [set x : int | 1 <= x <= 16] /\ conspiratorial A /\ A #= [set : 'I_(putnam_1974_a1_solution)]) /\
+      forall A : set int, A `<=` [set x : int | 1 <= x <= 16] -> conspiratorial A -> A #<= [set : 'I_(putnam_1974_a1_solution)].
```

(`diff` of the upstream file against the corrected file with its header and `(* compat: *)`
lines removed shows exactly this one changed line, `15c15,16`.)

* The new first conjunct: some subset of [1, 16] is conspiratorial and has exactly
  `putnam_1974_a1_solution` elements. `A #= B` is MathComp-Analysis' equality of cardinals
  (a bijection between `A` and `B` exists); PutnamBench's own Rocq statement of 2015 B5 uses the
  same `[set : 'I_n] #= ...` idiom. It uses the same range, the same `conspiratorial` and the
  same `[set : 'I_(putnam_1974_a1_solution)]` as the upper bound.
* The second conjunct is the upstream conclusion, character for character (only its leading
  `    : ` became six spaces). `P /\ forall A, ...` parses as `P /\ (forall A, ...)`; `Check`
  prints exactly that (section 4, item 3).
* Together they say that 11 is the **largest** size, which is what the problem asks; with a
  wrong value of the solution the statement is now false (with 12 or more the first conjunct fails:
  no 12-element conspiratorial set exists, section 4, item 4; with 10 or less the second fails:
  the 11-element witness of `exists_half`, section 4, item 3). Abstractly, the new shape can hold
  for at most one value of the solution (`determined`, section 4, item 3).

Comparison with the Lean statement (`putnam_1974_a1.lean`):

```lean
theorem putnam_1974_a1
    (conspiratorial : Set ℤ → Prop)
    (hconspiratorial : ∀ S, conspiratorial S ↔ ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, (a > 0 ∧ b > 0 ∧ c > 0) ∧ ((a ≠ b ∧ b ≠ c ∧ a ≠ c) → (Int.gcd a b > 1 ∨ Int.gcd b c > 1 ∨ Int.gcd a c > 1))) :
    IsGreatest {k | ∃ S, S ⊆ Icc 1 16 ∧ conspiratorial S ∧ S.encard = k} putnam_1974_a1_solution
```

`IsGreatest X k` is `k ∈ X ∧ k ∈ upperBounds X`: membership = the new first conjunct (`S.encard = k`
<-> `A #= [set : 'I_k]`), upper bound = the upstream conjunct (`encard S <= k` <-> `A #<= [set : 'I_k]`).
The corrected Rocq statement follows the Lean one in this respect. It deviates from Lean only where
the upstream Rocq text already did, harmlessly: Lean makes positivity part of the definition
(every element of a conspiratorial set is positive) while the Rocq definition only restricts the
condition to positive elements; for subsets of [1, 16] the two definitions coincide. The upstream
Rocq definition and upstream `_solution` value were kept.

## 4. Sanity checks actually run

All Rocq checks were run on **both** toolchains: Rocq 9.1.1 / MathComp 2.5.0 /
MathComp-Analysis 1.16.0 (`source /opt/rocq91/bin/rocq-env.sh`, `rocq compile`) and Coq 8.18.0 /
MathComp 2.1.0 / MathComp-Analysis 1.0.0 (`coqc`), deleting build products in between.

1. **Compilation of the deliverables** (in this folder, `rocq compile -R . "" <file>` resp.
   `coqc -R . "" <file>`):
   * `putnam_1974_a1.v`: exit 0 on both. All warnings (30 on Rocq 9.1.1, 23 on Coq 8.18.0) point
     at line 36, the upstream `From mathcomp Require Import all_algebra all_ssreflect.` line
     (all_ssreflect deprecated since 2.5, ambiguous coercion paths, overridden notations).
   * `putnam_1974_a1_corrected.v`: exit 0 on both. All warnings (30 resp. 23) point at line 45,
     the same upstream import line; none at the compat lines, the `Definition` or the `Theorem`.
   * The upstream file verbatim (no compat lines, scratch copy): Rocq 9.1.1 exit 1 with the error
     quoted in section 2; Coq 8.18.0 exit 0 (23 warnings, all at line 1).
2. **Byte identity / diff.** The two files were assembled by a script from the upstream bytes.
   `tail` of `putnam_1974_a1.v` after its header, with the `(* compat: *)` lines removed, is
   `cmp`-identical to the upstream file (747 bytes, ending in a newline). The corrected body
   against upstream: the one-line diff shown in section 3.
3. **Scratch file `checks.v`** (in the scratch directory `work/putnam_1974_a1/final/`; it
   `Require`s the final `putnam_1974_a1_corrected.v`), exit 0 on both toolchains:
   * `Check putnam_1974_a1.` prints
     `let conspiratorial := fun A : set int => forall a b c : int, a \in A -> ... -> ~ coprimez a b \/ ~ coprimez b c \/ ~ coprimez c a in (exists A : set int, A `<=` [set x | 1 <= x <= 16] /\ conspiratorial A /\ A #= [set: 'I_putnam_1974_a1_solution]) /\ (forall A : set int, A `<=` [set x | 1 <= x <= 16] -> conspiratorial A -> A #<= [set: 'I_putnam_1974_a1_solution])`
     -- the intended parse. `Print putnam_1974_a1_solution.` gives `11%N`.
   * **The new conjunct is provable** (`Lemma exists_half`, its statement copied verbatim from
     the corrected theorem's binder and first conjunct, `Qed`): witness
     `f @` [set: 'I_11]` with `f i = nth 0 [:: 2; 3; 4; 6; 8; 9; 10; 12; 14; 15; 16] i`; range by
     `all` + `by []`, conspiratoriality by a boolean triple check over the list closed by
     `vm_compute`, and `#=` by `inj_card_eq` with `nth_uniq`. So the existence half is true for 11,
     and `#=` / `\in` have the intended meaning. `Print Assumptions exists_half`: only
     `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`,
     `boolp.constructive_indefinite_description`.
   * **`conspiratorial` is not trivial**: `all16_not_consp : ~ conspiratorial [set x : int | 1 <= x <= 16]`
     (1, 2, 3 pairwise coprime) and `plus5_not_consp : ~ conspiratorial (5 |` witness)`
     (2, 3, 5 pairwise coprime), both `Qed`. So the upper-bound conjunct is a real constraint.
   * **The upstream conclusion does not pin the answer**: `upstream_monotone (A : set int) :
     A #<= [set : 'I_11] -> A #<= [set : 'I_12]` (`card_le_trans`, `card_II`, `card_le_II`), `Qed`.
   * **The corrected shape does pin it**: `determined (n m : nat) (P : set int -> Prop) :
     (exists A, P A /\ A #= [set : 'I_n]) -> (forall A, P A -> A #<= [set : 'I_m]) -> (n <= m)%N`,
     `Qed`. Hence the corrected statement can hold for at most one value of the solution.
   * `Print Assumptions` of every lemma above: only the three `boolp` axioms.
4. **Exhaustive search** (`brute.py` in the scratch directory, all 2^16 subsets of {1..16}):
   `max size of a conspiratorial subset of 1..16: 11`; exactly one maximum set,
   `[2, 3, 4, 6, 8, 9, 10, 12, 14, 15, 16]`; number of conspiratorial subsets by size
   `{0: 1, 1: 16, 2: 120, 3: 377, 4: 718, 5: 919, 6: 828, 7: 528, 8: 233, 9: 68, 10: 12, 11: 1}`.
   So the corrected statement is true with 11 and false with 12 (no 12-element set exists).
5. **Verifier** (`extended/verify.sh putnam_1974_a1`), run under both toolchains; verdict lines
   quoted below.
6. No AI model names in the files (grep, no hit).

Verifier output, `(source /opt/rocq91/bin/rocq-env.sh && cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1974_a1)`, exit 0:

```
toolchain: The Rocq Prover, version 9.1.1  (rocq compile)

### putnam_1974_a1
OK   putnam_1974_a1.v (upstream copy) compiles
OK   putnam_1974_a1_corrected.v compiles
OK   putnam_1974_a1_corrected.v ends in Admitted (statement only)
OK   putnam_1974_a1.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines

checked 1 problem folder(s), 0 with a proof file
ALL CHECKS PASSED
(build products and logs removed)
```

Verifier output, `(cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1974_a1)` (Coq 8.18.0), exit 0:

```
toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)

### putnam_1974_a1
OK   putnam_1974_a1.v (upstream copy) compiles
OK   putnam_1974_a1_corrected.v compiles
OK   putnam_1974_a1_corrected.v ends in Admitted (statement only)
OK   putnam_1974_a1.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines

checked 1 problem folder(s), 0 with a proof file
ALL CHECKS PASSED
(build products and logs removed)
```

## 5. Difficulty estimate and proof sketch

**Difficulty: 2 / 5** (a finite combinatorial fact; the only friction is moving between
MathComp-Analysis cardinals of `set int` and concrete lists).

Mathematical proof. *Existence*: Q = {2, 3, 4, 6, 8, 9, 10, 12, 14, 15, 16}, the 11 multiples
of 2 or 3 in [1, 16]; among any three of them two are divisible by 2 or two by 3 (pigeonhole),
so Q is conspiratorial. *Upper bound*: [1, 16] is the disjoint union of Q and
P = {1, 5, 7, 11, 13}. Let `A` be a conspiratorial subset of [1, 16].
(a) The elements of P are pairwise coprime, so `A` contains at most two of them.
(b) If `A` contains some p in P, then {2, 3, p} and {4, 9, p} are pairwise coprime triples
(p is odd and not a multiple of 3), so `A` misses at least one of 2, 3 and at least one of 4, 9:
|A ∩ Q| <= 9 and |A| <= 2 + 9 = 11.
(c) Otherwise A is included in Q and |A| <= 11.
(The exhaustive search of section 4, item 4, confirms the bound and shows Q is the only 11-element
conspiratorial set.)

Rocq plan (the existence half is already done in the scratch `checks.v`, ~15 lines):

* Existence: as in `exists_half` (witness `f @` [set: 'I_11]`, `vm_compute` on a boolean
  triple check, `inj_card_eq` + `nth_uniq`).
* Upper bound, by reflection to lists: let `L := [seq x <- [seq (Posz k) | k <- iota 1 16] | `[< A x >]]`
  (classical decidability `asboolP`); from `A `<=` [set x | 1 <= x <= 16]` get
  `forall x, A x <-> x \in L`, `uniq L` (`filter_uniq`, `map_inj_uniq`), and that `L` is a
  subsequence of the list 1..16 (`filter_subseq`) satisfying the boolean triple condition
  (from `conspiratorial A`). A decidable lemma "every subsequence of 1..16 satisfying the triple
  condition has size <= 11" is proved by computation: enumerate subsequences with pruning (only
  3821 subsets of 1..16 are conspiratorial, so a search that extends only conspiratorial prefixes
  should be fast under `vm_compute`), or by the case analysis (a)-(c) above. Finally build the injection
  `x |-> index x L` into `'I_11` (`index_uniq`/`nth_index` for injectivity on `A`) and conclude
  with `card_leP`/`pcard_injP` or via `card_le_trans` with `subset_card_le` and `inj_card_eq`.
* Library facts (all names checked to exist in both MathComp 2.5.0 / MathComp-Analysis 1.16.0
  and MathComp 2.1.0 / MathComp-Analysis 1.0.0 sources): `cardinality.v` (`inj_card_eq`, `card_le_trans`, `card_II`, `card_le_II`,
  `card_le_eql`, `card_le_eqr`, `pcard_injP` or `card_leP`, `subset_card_le`), `seq.v`
  (`nth_uniq`, `index_uniq`, `nth_index`, `filter_subseq`, `mem_filter`), `classical_sets.v`
  (`in_setE`), `boolp.v` (`asboolP`), `intdiv.v` (`coprimez`, computable).
* Expected `Print Assumptions`: the three classical axioms of `mathcomp.classical` only (no
  `Variable` in this statement).

## 6. Status of each file

| file | status |
|---|---|
| `putnam_1974_a1.v` | upstream text verbatim after a header comment, plus the three marked compat lines (needed on Rocq 9.1). **Compiles** on Rocq 9.1.1 and Coq 8.18.0 (section 4, item 1). |
| `putnam_1974_a1_corrected.v` | corrected statement, ends in `Proof. Admitted.`; **compiles** on Rocq 9.1.1 and Coq 8.18.0 with no warning from its own lines (section 4, item 1); differs from upstream only in the conclusion (existence conjunct added) and the marked compat lines. |
| `putnam_1974_a1_statement_is_false.v` / `_vacuous.v` | not applicable: verdict `unfaithful (incomplete)`; the upstream statement is true (the upper-bound half of the problem) and its only let-binding is a definition, so there is nothing false or contradictory to exhibit. The incompleteness itself is shown by `upstream_monotone` / `determined` in the scratch checks. |
| `putnam_1974_a1_corrected_proof.v` | not written (proofs are out of scope in this phase). Sketch in section 5. |
| `NOTES.md` | this file. |
