# putnam_1974_a3 -- notes

Audit verdict: **vacuous (machine-checked)**. Upstream commit
4dbe26ef21563af851eedaeb82d936fe1f94fc52 of PutnamBench, file `coq/src/putnam_1974_a3.v`.
Files in this folder: `putnam_1974_a3.v` (upstream copy, evidence), `putnam_1974_a3_corrected.v`
(proposed fix, ends in `Proof. Admitted.`), `putnam_1974_a3_statement_is_vacuous.v` (machine-checked
proof that the upstream hypotheses are contradictory), this file.

## 1. The problem

Putnam 1974 A3. A well-known theorem asserts that a prime p > 2 can be written as the sum of two
perfect squares if and only if p = 1 (mod 4). Find which primes p > 2 can be written in each of
the following forms, using (not necessarily positive) integers x and y: (a) x^2 + 16y^2,
(b) 4x^2 + 4xy + 5y^2. Answer: (a) exactly the primes p = 1 (mod 8); (b) exactly the primes
p = 5 (mod 8). The benchmark encodes the quoted theorem as a hypothesis and the answer as the pair
of sets `putnam_1974_a3_solution`.

## 2. Defect(s) in the upstream statement

The upstream text (kept verbatim after a header comment in `putnam_1974_a3.v`; it needs no compat
line) is

```coq
Definition putnam_1974_a3_solution : (set nat) * (set nat) := ([set p : nat | prime p /\ p = 1 %[mod 8]], [set p : nat | prime p /\ p = 5 %[mod 8]]).
Theorem putnam_1974_a3
    (assmption : forall p : nat, ((prime p /\ gt p 2) -> ((exists m n : int, p%:Z = m ^+ 2 + n ^+ 2))) <-> p = 1 %[mod 4])
    : forall p : nat, 
        ((prime p /\ gt p 2 /\ (exists x y : int, p%:Z = x ^+ 2 + 16 * y ^+ 2)) <-> p \in fst putnam_1974_a3_solution) /\
        ((prime p /\ gt p 2 /\ (exists x y : int, p%:Z = 4 * x ^+ 2 + 4 * x * y + 5 * y ^+ 2)) <-> p \in snd putnam_1974_a3_solution).
Proof. Admitted.
```

**Defect (the audited one): the hypothesis is contradictory, so the theorem is vacuous.** Because
of the parentheses, `assmption` says: for EVERY natural number p,
`((prime p /\ p > 2) -> p is a sum of two integer squares) <-> p = 1 %[mod 4]`. Its left side is an
implication, which is vacuously true whenever p is not a prime > 2. At p = 4 the left side holds
(4 is not prime) and the right side is `4 %% 4 = 1 %% 4`, i.e. `0 = 1`. Hence `assmption` is
unsatisfiable and the theorem holds for any answer sets whatsoever (it would be just as provable
with the two sets swapped). The same failure occurs at p = 0, 2, 6, 8, 10, ... (every even p; the
brute-force script of section 4 lists `[0, 2, 4, 6, 8, 10]` below 12). Machine-checked in
`putnam_1974_a3_statement_is_vacuous.v`: upstream's Definition and Theorem verbatim, closed by

```coq
case: (assmption 4%N) => h _.
suff: 4%N = 1 %[mod 4] by [].
by apply: h => -[].
```

(`prime 4` evaluates to `false`, which discharges the premise; `4 = 1 %[mod 4]` evaluates to
`0 = 1`).

**Re-reading the whole statement against the trap list of the brief (section 7.5):** no further
defect.

* Parse of the conclusion: `Set Printing All` (section 4, item 3) shows each conjunct is
  `iff (and (prime p) (and (gt p 2) (ex ...))) (in_mem p (mem (fst/snd solution)))`, as intended;
  `forall p : nat, A /\ B` scopes over both conjuncts.
* `p = 1 %[mod 8]` is `modn p 8 = modn 1 8` on `nat` (printed with `Set Printing All`), not a ring
  numeral trap; `gt p 2` is `Peano.gt`, i.e. `2 < p` on `nat`; `p%:Z` is `Posz p`.
* The forms: `x ^+ 2 + 16 * y ^+ 2` and `4 * x ^+ 2 + 4 * x * y + 5 * y ^+ 2` over `int`
  (`^+` with a `nat` exponent 2 is the intended square; the numerals 16, 4, 5 are `16%:R` etc. in
  `int`, printed as `natmul 1 16`). x, y range over all integers ("not necessarily positive").
* The answer sets `{p | prime p /\ p = 1 mod 8}` and `{p | prime p /\ p = 5 mod 8}` are the
  informal answer (the primes p = 1 or 5 (mod 8) are automatically > 2); membership `p \in A` on
  a classical `set nat` is `asbool (A p)` (`in_setE`, used in section 4).
* `<=`/`<`, divisibility, `\sum`/`\prod`, `Rpower`, series, `sup`, `'I_n` indexing, local `:=`
  definitions: none occur. Theorem and `_solution` names are the problem's.
* The hypothesis name `assmption` (sic) is upstream's and is kept.

## 3. The fix

`putnam_1974_a3_corrected.v` differs from the upstream text in exactly one line (plus the header
comment and the three marked compat lines). `diff` of the upstream file against the corrected
file with header and `(* compat: *)` lines removed (the verifier's `strip`):

```diff
13c13
<     (assmption : forall p : nat, ((prime p /\ gt p 2) -> ((exists m n : int, p%:Z = m ^+ 2 + n ^+ 2))) <-> p = 1 %[mod 4])
---
>     (assmption : forall p : nat, (prime p /\ gt p 2) -> ((exists m n : int, p%:Z = m ^+ 2 + n ^+ 2) <-> p = 1 %[mod 4]))
```

Only parentheses moved; every token is upstream's. The new hypothesis reads "for every prime
p > 2: p is a sum of two integer squares iff p = 1 (mod 4)", which is exactly the well-known
theorem the problem quotes (Fermat's two-squares theorem). It is a true statement, so the
hypothesis is satisfiable and the corrected theorem is not vacuous; being true, it also adds
nothing the problem does not grant. The printed type (section 4, item 3) is
`(forall p, prime p /\ (p > 2)%coq_nat -> (exists m n : int, p = m ^+ 2 + n ^+ 2) <-> p = 1 %[mod 4]) -> ...`,
with `->` scoping over the `<->` (`Set Printing All`: `forall (p : nat) (_ : and ...), iff ...`).

Comparison with the Lean statement (`putnam_1974_a3.lean`):

```lean
(assmption : ∀ p : ℕ, p.Prime ∧ p > 2 → ((∃ m n : ℤ, p = m^2 + n^2) ↔ p ≡ 1 [MOD 4]))
: ∀ p : ℕ, ((p.Prime ∧ p > 2 ∧ (∃ x y : ℤ, p = x^2 + 16*y^2)) ↔ p ∈ putnam_1974_a3_solution.1) ∧ ((p.Prime ∧ p > 2 ∧ (∃ x y : ℤ, p = 4*x^2 + 4*x*y + 5*y^2)) ↔ p ∈ putnam_1974_a3_solution.2)
```

with the answer `({p | p.Prime ∧ p ≡ 1 [MOD 8]}, {p | p.Prime ∧ p ≡ 5 [MOD 8]})`. The corrected
Rocq hypothesis is the Lean hypothesis transcribed (the Lean parenthesization puts the `↔` inside
the implication); the conclusion and the answer sets were already the same in both, and are kept
verbatim from upstream. No deviation from the Lean statement.

Compat lines: the corrected file carries the repository's compat kind (1) (the bracketed
`From mathcomp Require Import ssralg.` after the upstream import lines), as the brief prescribes for
MathComp statements with ring-scope numerals (`16 * y ^+ 2`, ... on `int`). For this file they are
a no-op: the upstream text compiles on Rocq 9.1 without them, and with and without them the theorem
and the Definition print identically under `Set Printing All` on Rocq 9.1.1 (section 4, item 2).
The upstream copy `putnam_1974_a3.v` needs none (brief: compat lines there only if needed to
compile), so it has none. Kinds (2) (no `Variable`) and (3) (no derivatives) do not apply.

## 4. Sanity checks actually run

Toolchains: Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (`source /opt/rocq91/bin/rocq-env.sh`,
`rocq compile`) and Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (`coqc`), deleting build
products in between. Scratch files are in
the scratch directory (`.../scratchpad/work/putnam_1974_a3/`, not part of the repository).

1. **Compilation of the deliverables** (in this folder, `rocq compile -R . "" <file>` resp.
   `coqc -R . "" <file>`), all exit 0 on both toolchains:
   * `putnam_1974_a3.v`: 30 warnings on Rocq 9.1.1, 23 on Coq 8.18.0, all at line 31 (the upstream
     `From mathcomp Require Import all_algebra all_ssreflect.` line).
   * `putnam_1974_a3_corrected.v`: 30 resp. 23 warnings, all at line 45 (the same import line);
     none at the compat lines, the Definition or the Theorem.
   * `putnam_1974_a3_statement_is_vacuous.v`: 30 resp. 23 warnings, all at line 30 (the same import
     line). Its `Print Assumptions putnam_1974_a3` prints exactly
     `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`,
     `boolp.constructive_indefinite_description` on both toolchains.
   * The upstream file verbatim (scratch copies `up91/`, `up818/`): exit 0 on both (30 resp. 23
     warnings, all at line 1). Hence no compat line in the upstream copy.
2. **Byte identity / compat no-op.** `putnam_1974_a3.v` minus its 30-line header (the comment box and one blank line) is `cmp`-identical
   to the upstream file (which has no trailing newline; kept so). The corrected body differs from
   upstream only in the line shown in section 3 (`diff` output above). In `cmp/`, the corrected
   statement was compiled with and without the compat lines on Rocq 9.1.1 and printed with
   `Set Printing All` (`Check ...putnam_1974_a3. Print ...putnam_1974_a3_solution.`): `diff` of the
   two outputs is empty (`SAME91`).
3. **Scratch file `final/checks.v`** (`Require`s the final `putnam_1974_a3_corrected.v`), exit 0 on
   both toolchains, all lemmas closed by `Qed`:
   * `Check putnam_1974_a3.` prints the intended statement (quoted in section 3);
     `Print putnam_1974_a3_solution.` prints
     `([set p | prime p /\ p = 1 %[mod 8]], [set p | prime p /\ p = 5 %[mod 8]])`.
   * `upstream_hyp_false : ~ (forall p : nat, <upstream hypothesis>)` (refuted at p = 4);
     `Print Assumptions`: "Closed under the global context".
   * `hyp_at_4`: the corrected hypothesis at p = 4 holds (premise false) -- the contradiction is
     gone. `hyp_at_5`, `hyp_at_13`: instances of the corrected hypothesis with both sides true
     (5 = 1^2 + 2^2, 13 = 2^2 + 3^2).
   * Instances of the conclusion, both sides of each biconditional true: `a_17` (17 = 1^2 + 16*1^2,
     17 in the (a) set), `a_41` (41 = 5^2 + 16*1^2), `b_5` (x = 0, y = 1), `b_13` (x = y = 1),
     `b_29` (x = 2, y = 1), each with membership in the matching answer set via `in_setE`.
   * `sets_small`: 2, 3, 7 are in neither answer set, 17 is not in the (b) set, 13 not in the (a)
     set; `sets_disjoint`: no p is in both sets.
   * `Print Assumptions` of `a_17`, `b_29`, `sets_small`: the three `boolp` axioms; of
     `mem_refl (A : set nat) p : p \in A -> p \in A` (proof `by []`) also exactly these three,
     which shows they come from membership in a classical set (the statement itself), not from the
     proofs; `putnam_1974_a3_solution`: closed.
4. **Brute force** (`brute.py`, Python, all p < 5000, |x|, |y| <= sqrt(p) + 1, which suffices for
   the three positive-definite forms): output `checked p < 5000 ; mismatches: []`, i.e. the
   corrected hypothesis (Fermat) holds for every prime 2 < p < 5000, and both biconditionals of the
   corrected conclusion hold for every p < 5000. Primes < 120 of form (a): `[17, 41, 73, 89, 97, 113]`;
   of form (b): `[5, 13, 29, 37, 53, 61, 101, 109]`. The upstream hypothesis fails at
   `[0, 2, 4, 6, 8, 10]` (p < 12).
5. **Verifier** (`extended/verify.sh putnam_1974_a3`), run under both toolchains, exit 0; verdict
   lines quoted below.
6. No AI model names in the files (grep, no hit).

Verifier output, `(source /opt/rocq91/bin/rocq-env.sh && cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1974_a3)`:

```
toolchain: The Rocq Prover, version 9.1.1  (rocq compile)

### putnam_1974_a3
OK   putnam_1974_a3.v (upstream copy) compiles
OK   putnam_1974_a3_corrected.v compiles
OK   putnam_1974_a3_corrected.v ends in Admitted (statement only)
OK   putnam_1974_a3_statement_is_vacuous.v compiles
OK   putnam_1974_a3_statement_is_vacuous.v: only library axioms / the statement's R: boolp.propositional_extensionality boolp.functional_extensionality_dep boolp.constructive_indefinite_description 
OK   putnam_1974_a3.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines

checked 1 problem folder(s), 0 with a proof file
ALL CHECKS PASSED
(build products and logs removed)
```

Verifier output, `(cd /home/user/PutnamBench_ROCQ/extended && bash verify.sh putnam_1974_a3)` (Coq 8.18.0):

```
toolchain: The Coq Proof Assistant, version 8.18.0  (coqc)

### putnam_1974_a3
OK   putnam_1974_a3.v (upstream copy) compiles
OK   putnam_1974_a3_corrected.v compiles
OK   putnam_1974_a3_corrected.v ends in Admitted (statement only)
OK   putnam_1974_a3_statement_is_vacuous.v compiles
OK   putnam_1974_a3_statement_is_vacuous.v: only library axioms / the statement's R: boolp.propositional_extensionality boolp.functional_extensionality_dep boolp.constructive_indefinite_description 
OK   putnam_1974_a3.v: identical to upstream PutnamBench 4dbe26e apart from header and compat lines

checked 1 problem folder(s), 0 with a proof file
ALL CHECKS PASSED
(build products and logs removed)
```

## 5. Difficulty estimate and proof sketch

**Difficulty: 2 / 5.** Given the hypothesis (Fermat's theorem is granted, not to be proved), the
problem is elementary arithmetic mod 8; the friction is `int` squares and parity in MathComp.

Mathematical proof. Squares of odd integers are 1 (mod 8); squares of even integers are 0 or 4
(mod 8), and 0 (mod 16) iff the root is divisible by 4.

* (a), left to right: p = x^2 + 16y^2 is an odd prime, so x is odd and p = x^2 = 1 (mod 8).
  Right to left: p prime, p = 1 (mod 8) gives p > 2 and p = 1 (mod 4), so by `assmption`
  p = m^2 + n^2; p odd, so exactly one of m, n is even, say n = 2k and m odd. Then
  p = m^2 + 4k^2 with m^2 = 1 (mod 8), so 4k^2 = 0 (mod 8), k = 2j is even and p = m^2 + 16j^2.
* (b): 4x^2 + 4xy + 5y^2 = (2x + y)^2 + (2y)^2. Left to right: p odd forces y odd, so
  (2x + y)^2 = 1 and 4y^2 = 4 (mod 8): p = 5 (mod 8). Right to left: p = 5 (mod 8) gives
  p = m^2 + (2k)^2 with m odd as above, and m^2 + 4k^2 = 5 (mod 8) forces k odd; put y = k,
  x = (m - k)/2 (an integer, m and k odd), so 2x + y = m and p = 4x^2 + 4xy + 5y^2.

Rocq plan.

* Reduce `int` equations to `nat`: from `p%:Z = m ^+ 2 + n ^+ 2` get
  `p = `|m| ^ 2 + `|n| ^ 2` (`abszX`, `gez0_abs`/`abszE`, `PoszD`, `Posz` injectivity via
  `[eqP]`/`eqz_nat`); for (b) first rewrite with the ring identity
  `4 * x ^+ 2 + 4 * x * y + 5 * y ^+ 2 = (2 * x + y) ^+ 2 + (2 * y) ^+ 2` (`ring` from
  algebra-tactics, or `sqrrD`/`exprMn` by hand).
* Parity / mod-8 arithmetic in `nat`: `modnDm`, `modnMm`, `modnXm`, `odd_mod`, `oddX`,
  `odd_double`, and the case split `a %% 8 < 8` (e.g. `case: (a %% 8) (ltn_pmod a (isT : 0 < 8))`
  with `do 8 case`) to show `(a ^ 2) %% 8 \in [:: 0; 1; 4]`; `prime_gt1`, `even_prime` / `prime`
  odd for p > 2.
* Constructing witnesses on the reverse directions: from `n = 2k` (`odd` false, `half`/`uphalf`,
  `odd_double_half`) and `k = 2j`, or for (b) `m = 2a + 1`, `k = 2b + 1` and `x := a%:Z - b%:Z`,
  then close the `int` equation with `ring` (algebra-tactics) or `lia` via zify where linear.
* Library: `ssrint.v`, `intdiv.v` (`absz`, `abszX`, `modz` if staying in `int`), `div.v`, `prime.v`,
  `classical_sets.v` (`in_setE`), algebra-tactics `ring`.
* Expected `Print Assumptions`: the three `boolp` axioms (they are in the statement's type).

## 6. Status of each file

| file | status |
|---|---|
| `putnam_1974_a3.v` | upstream text verbatim (byte-identical, no compat lines) after a header comment; **compiles** on Rocq 9.1.1 and Coq 8.18.0 (section 4, item 1). |
| `putnam_1974_a3_corrected.v` | corrected statement (one line: parentheses of `assmption` moved, as in the Lean statement) + the three compat lines of kind (1); ends in `Proof. Admitted.`; **compiles** on Rocq 9.1.1 and Coq 8.18.0 with no warning from its own lines. |
| `putnam_1974_a3_statement_is_vacuous.v` | upstream Definition and Theorem verbatim, proved from the contradiction at p = 4 (three tactic lines, `Qed`); **compiles** on Rocq 9.1.1 and Coq 8.18.0; `Print Assumptions`: only the three `boolp` axioms of the statement's classical-set membership. |
| `putnam_1974_a3_corrected_proof.v` | not written (proofs are out of scope in this phase). Sketch in section 5. |
| `NOTES.md` | this file. |
