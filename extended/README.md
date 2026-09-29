# Corrected Rocq statements for 25 of the 89 remaining defective PutnamBench statements

A hand audit of the 412 Rocq statements of [PutnamBench](https://github.com/trishullab/PutnamBench)
(commit `4dbe26ef21563af851eedaeb82d936fe1f94fc52`) found 92 whose verdict is not OK: **false**
(a counterexample exists), **vacuous** (contradictory hypotheses), **unfaithful** (encodes a
different or weaker problem), **naming** (theorem not named after the problem) or **compile**
(fails to compile for a one-token reason). Three of them (1962 A2, A6, B5) are handled in the
repository root; this folder handles 25 of the other 89 (the rest are listed at the end): for each, the corrected statement was
written and independently reviewed for faithfulness to the informal problem. **No proofs are
attempted here**: every `_corrected.v` ends in `Admitted`, and `NOTES.md` records a difficulty
estimate and a proof sketch for future work.

## Layout

One folder per problem, `extended/<problem>/`, mirroring the root convention:

| file | content |
|---|---|
| `<p>.v` | the upstream statement, kept as evidence: byte-identical to PutnamBench apart from the header comment and, where needed, the marked `(* compat: ... *)` lines |
| `<p>_corrected.v` | the proposed fix; ends in `Proof. Admitted.` (a statement, not a proof); compiles on Rocq 9.1 |
| `<p>_statement_is_false.v` / `<p>_statement_is_vacuous.v` | where present, a derivation of `False` from the admitted upstream theorem (its `Print Assumptions` lists that theorem), or a proof of the upstream theorem that only uses the contradiction in its hypotheses |
| `NOTES.md` | the defect, the fix and why it is faithful, the sanity checks run, the difficulty estimate and proof sketch |

## Verification

`bash extended/verify.sh [problem ...]` compiles every folder in dependency order, checks the
upstream copies against PutnamBench, checks the evidence files' assumptions, and (when a proof
file exists) checks hygiene, `Print Assumptions`, and statement identity (see the script header).
`.github/workflows/verify.yml` runs it on every push under Rocq 9.1 / MathComp 2.5 /
MathComp-Analysis 1.16 / Coquelicot 3.4.4 (job `verify-extended`). Locally the files were checked
under that toolchain (Rocq 9.1.1, Nix) and under Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis
1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04); the "verified" column below gives the verifier's verdict
under each (Rocq 9.1 / Coq 8.18). A `FAIL` under Coq 8.18 alone means the upstream file uses a
library feature that the older MathComp-Analysis lacks; see the folder's NOTES.md.

Summary: 25 of the 89 remaining problems done in this round; verifier passes under Rocq 9.1 for 25, under Coq 8.18 for 25;
11 evidence files (False derivations / vacuity proofs); 25 statements approved by the
independent review.

## Problems

| problem | audit verdict | fix (before -> after) | evidence | proof difficulty (1-5) | verified (Rocq 9.1 / Coq 8.18) | review approved |
|---|---|---|---|---|---|---|
| [putnam_1964_a2](putnam_1964_a2/) | false | One line added to the Theorem statement, directly after the positivity/continuity conjunct: before: `        /\ {within [set x \| 0 <= x <= 1], continuous f}) ` followed by `        /\ \int[mu]_(x in [set x \| 0 <= x ... | `putnam_1964_a2_statement_is_false.v` | 3 | PASS / PASS | yes |
| [putnam_1964_a6](putnam_1964_a6/) | false | This revision changed only comments and NOTES.md. The statement is the same as in the previous round:   -From mathcomp Require Import classical_sets. -> +From mathcomp Require Import classical_sets cardinality.   +   ... | `putnam_1964_a6_statement_is_false.v` | 4 | PASS / PASS | yes |
| [putnam_1965_b4](putnam_1965_b4/) | false | hu: "\sum_(0 <= i < n%/2 .+1) ('C(n, 2 * i)%:R * x^i)" -> "\sum_(0 <= i < (n%/2).+1) ('C(n, 2 * i)%:R * x^i)" hv: "\sum_(0 <= i < (n.-1)%/2 .+1) ('C(n, 2 * (i.+1))%:R * x^i)" -> "\sum_(0 <= i < ((n.-1)%/2).+1) ('C(n, ... | `putnam_1965_b4_statement_is_false.v` | 3 | PASS / PASS | yes |
| [putnam_1966_a1](putnam_1966_a1/) | false | Statement (unchanged from the previous round, which the reviewer judged faithful): (f : nat -> int := fun n => \sum_(0 <= m < n + 1) (if (~~odd m) then (m%:Z)/2 else (m%:Z-1)/2)) -> (f : nat -> int := fun n => \sum_(0... | `putnam_1966_a1_statement_is_false.v` | 2 | PASS / PASS | yes |
| [putnam_1966_a3](putnam_1966_a3/) | compile | Statement (unchanged from the previous round): `: (fun n : nat => n%:R * x n) @ \oo --> 1.` -> `: (fun n : nat => n%:R * x n) @ \oo --> (1 : R).` The marked compat lines are also present: the ssralg re-import block af... | - | 3 | PASS / PASS | yes |
| [putnam_1966_a5](putnam_1966_a5/) | unfaithful | Statement (unchanged from the previous round): localT "forall r s : R, r <= s -> ..." -> "forall r s : R, r < s -> ...". This round: putnam_1966_a5.v and putnam_1966_a5_corrected.v: Verified line "compiles on Coq 8.18... | - | 2 | PASS / PASS | yes |
| [putnam_1966_a6](putnam_1966_a6/) | compile | Statement (unchanged from the previous version): "    : (fun n => a n 1%nat) @ \oo --> 3." -> "    : (fun n => a n 1%nat) @ \oo --> (3 : R)." plus the marked compat lines of kinds (1) and (2). Text-only fixes for this... | - | 3 | PASS / PASS | yes |
| [putnam_1967_a4](putnam_1967_a4/) | unfaithful | Theorem conclusion (the only changed statement line): "    : ~exists u : R -> R, forall x : R, 0 <= x <= 1 -> u x = 1 + lambda * \int[mu]_(y in [set y \| 0 <= y <= 1]) (u y * u (y - x))." -> "    : ~exists u : R -> R,... | - | 4 | PASS / PASS | yes |
| [putnam_1967_b3](putnam_1967_b3/) | compile | Conclusion line: `    : (fun n : nat => \int[mu]_(x in [set y \| 0 < y < 1]) (f x * g (n%:~R * x))) --> ` -> `    : (fun n : nat => \int[mu]_(x in [set y \| 0 < y < 1]) (f x * g (n%:~R * x))) @ \oo --> ` (upstream's t... | - | 4 | PASS / PASS | yes |
| [putnam_1967_b6](putnam_1967_b6/) | unfaithful | Upstream copy (putnam_1967_b6.v): added only two marked compat lines, "Set Warnings \"-declaration-outside-section,-local-declaration\". (* compat: ... *)" before "Variable R : realType." and "Local Open Scope classic... | - | 3 | PASS / PASS | yes |
| [putnam_1968_a1](putnam_1968_a1/) | naming | Theorem putnam_1968_b1 -> Theorem putnam_1968_a1 (the only statement change). Both files also carry the repository's marked compat lines: the ssralg re-import block after the second import line, and the Set Warnings l... | - | 2 | PASS / PASS | yes |
| [putnam_1969_b3](putnam_1969_b3/) | compile | (hT2 : (fun n => (T n)/(T n.+1)) @ \oo --> 1)  ->  (hT2 : (fun n => (T n)/(T n.+1)) @ \oo --> (1 : R)) Also added the repository's marked compat lines. Kind (1), the ssralg re-import block, goes after the second impor... | - | 4 | PASS / PASS | yes |
| [putnam_1970_b5](putnam_1970_b5/) | naming | Theorem putnam_1970_b5_solution -> Theorem putnam_1970_b5 (both files, not a statement change: added compat line `Set Warnings "-declaration-outside-section,-local-declaration". (* compat: ... *)` before `Variable R :... | - | 2 | PASS / PASS | yes |
| [putnam_1974_a1](putnam_1974_a1/) | unfaithful | Conclusion line (upstream line 15): "    : forall A : set int, A `<=` [set x : int \| 1 <= x <= 16] -> conspiratorial A -> A #<= [set : 'I_(putnam_1974_a1_solution)]." -> two lines: "    : (exists A : set int, A `<=` ... | - | 2 | PASS / PASS | yes |
| [putnam_1974_a3](putnam_1974_a3/) | vacuous | (assmption : forall p : nat, ((prime p /\ gt p 2) -> ((exists m n : int, p%:Z = m ^+ 2 + n ^+ 2))) <-> p = 1 %[mod 4])  ->  (assmption : forall p : nat, (prime p /\ gt p 2) -> ((exists m n : int, p%:Z = m ^+ 2 + n ^+ ... | `putnam_1974_a3_statement_is_vacuous.v` | 2 | PASS / PASS | yes |
| [putnam_1977_b5](putnam_1977_b5/) | false | (hA : A + \sum_(i <- a) (i ^+ 2) <= 1/((size a)%:R - 1) * (\sum_(i <- a) i) ^+ 2) -> (hA : A + \sum_(i <- a) (i ^+ 2) < 1/((size a)%:R - 1) * (\sum_(i <- a) i) ^+ 2) (plus, in both the upstream copy and the corrected ... | `putnam_1977_b5_statement_is_false.v` | 2 | PASS / PASS | yes |
| [putnam_1978_b2](putnam_1978_b2/) | compile | : (f @ \oo --> ratr putnam_1978_b2_solution).  ->      : (f @ \oo --> (ratr putnam_1978_b2_solution : R)). (plus the marked compat lines: the ssralg re-import block after "From mathcomp Require Import reals topology s... | - | 3 | PASS / PASS | yes |
| [putnam_1979_a6](putnam_1979_a6/) | naming | Theorem putnam_1979_b6 -> Theorem putnam_1979_a6 ... 8*(size p)%:R*(\sum_(0 <= i < (size p).+1) (1%R)/(2*(i%:R) + 1)). -> ... 8*(size p)%:R*(\sum_(0 <= i < (size p)) (1%R)/(2*(i%:R) + 1)). (Both files also carry the 4... | - | 4 | PASS / PASS | yes |
| [putnam_1982_a6](putnam_1982_a6/) | vacuous | (a: nat -> R)  ->  : (forall (a: nat -> R),   [a moved inside the left side of the iff; theorem has no parameters] : ((Series a = 1 /\ forall (i j: nat), le i j -> Rabs (a i) > Rabs (a j)) /\  ->  (is_series a 1 /\ fo... | `putnam_1982_a6_statement_is_vacuous.v` | 4 | PASS / PASS | yes |
| [putnam_1994_b3](putnam_1994_b3/) | naming, compile | Definition putnam_1993_b3_solution : set R := [set k \| k < 1].  ->  Definition putnam_1994_b3_solution : set R := [set k \| k < 1]. Theorem putnam_1993_b3  ->  Theorem putnam_1994_b3     : [set k \| forall f (hf : fo... | - | 2 | PASS / PASS | yes |
| [putnam_2010_b2](putnam_2010_b2/) | vacuous | line 8 (body of noncollinear): "        ~exists (s t : R), (s * (c - a) + t * (e - a), s * (d - b) + t * (f - b)) = (0, 0))" -> "        ~exists (s t : R), (s <> 0 \/ t <> 0) /\ (s * (c - a) + t * (e - a), s * (d - b)... | `putnam_2010_b2_statement_is_vacuous.v` | 3 | PASS / PASS | yes |
| [putnam_2013_b2](putnam_2013_b2/) | vacuous | line 4 (first line of the definition of E): "(E: Ensemble (R -> R) := fun f => forall (x : R), exists (a : nat -> R) (N : nat), f x = 1 + sum_n_m (...) 1 N /\ f x >= 0 /\ " -> "(E: Ensemble (R -> R) := fun f => exists... | `putnam_2013_b2_statement_is_vacuous.v` | 2 | PASS / PASS | yes |
| [putnam_2015_b4](putnam_2015_b4/) | compile | (hf : (fun n : nat => f n) @ \oo --> ratr C) -> (hf : (fun n : nat => f n) @ \oo --> (ratr C : R)) (added) three marked ssralg compat lines after "From mathcomp Require Import reals normedtype sequences topology." (ad... | - | 4 | PASS / PASS | yes |
| [putnam_2017_a1](putnam_2017_a1/) | vacuous | (hS : IsQualifying S /\ forall T : set int, T `<=` S -> ~ IsQualifying T)  ->  (hS : IsQualifying S /\ forall T : set int, IIsQualifying T -> S `<=` T) [typo guard: the exact new line is "    (hS : IsQualifying S /\ f... | `putnam_2017_a1_statement_is_vacuous.v` | 2 | PASS / PASS | yes |
| [putnam_2022_a6](putnam_2022_a6/) | vacuous | sumIntervals: sum_n (fun i => s(nth (i+1))^(2*k-1) - s(nth i)^(2*k-1)) (n-1) -> sum_n (fun i => s(nth (2*i+1))^(2*k-1) - s(nth (2*i))^(2*k-1)) (N-1) hvalid: "(forall (i : 'I_n),  (s i < s (ordS i)) /\ ... < 1) -> vali... | `putnam_2022_a6_statement_is_vacuous.v` | 5 | PASS / PASS | yes |


## Not yet attempted (64 problems)

The audit's remaining rows were not processed in this round (budget); their verdicts are in the
audit table and they can be handled with the same procedure (`extended/verify.sh` accepts any
new folder). putnam_1972_b1, putnam_1973_b4, putnam_1975_a3, putnam_1977_a2, putnam_1977_a4, putnam_1978_b6, putnam_1980_a5, putnam_1981_b1, putnam_1981_b2, putnam_1982_a2, putnam_1987_b1, putnam_1991_b4, putnam_1992_b1, putnam_1993_a4, putnam_1994_b5, putnam_1995_a2, putnam_1995_b4, putnam_1996_a6, putnam_1997_a6, putnam_1998_a4, putnam_1998_b4, putnam_2001_b2, putnam_2001_b3, putnam_2003_a2, putnam_2005_a3, putnam_2007_a4, putnam_2007_b1, putnam_2008_a4, putnam_2008_b5, putnam_2011_a2, putnam_2013_a3, putnam_2013_b5, putnam_2014_a3, putnam_2014_a4, putnam_2014_a5, putnam_2014_b2, putnam_2014_b4, putnam_2015_a3, putnam_2015_a5, putnam_2015_b1, putnam_2015_b5, putnam_2016_a6, putnam_2016_b1, putnam_2016_b6, putnam_2017_a3, putnam_2017_b4, putnam_2017_b6, putnam_2018_a1, putnam_2018_a3, putnam_2019_a6, putnam_2019_b2, putnam_2019_b5, putnam_2020_a1, putnam_2020_a3, putnam_2020_a6, putnam_2020_b1, putnam_2021_a4, putnam_2021_a5, putnam_2021_a6, putnam_2021_b2, putnam_2021_b4, putnam_2022_a1, putnam_2022_b4, putnam_2022_b6.
