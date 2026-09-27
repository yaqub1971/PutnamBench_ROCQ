# Coverage compared with Humanfia's public Lean preview

Humanfia's leaderboard entry (672/672 in Lean 4) published a preview of twelve verified
Lean solutions on Hugging Face
(`huggingface.co/datasets/humanfia-lab/putnambench-solution-preview`): 1962 A1–A6,
1962 B1, B2, B3, B5, B6, and 1963 A2. Four of those problems (1962 A1, A3, B1, B3) have
no Rocq statement in PutnamBench at all (the benchmark has Rocq versions of 412 of its
672 problems), so a comparison is only meaningful for the remaining eight. The table
uses the size of Humanfia's Lean proof file as a rough difficulty hint, and its last
column lists the files of this repository that back each claim.

| Problem | Humanfia Lean solution (preview) | What this repository did in Rocq | Files in this repository |
|---|---|---|---|
| 1962 A2 | yes (53 KB) | upstream statement found **false** (answer key incomplete); fix proposed; corrected statement not proved | `putnam_1962_a2.v` (upstream), `putnam_1962_a2_statement_is_false.v`, `putnam_1962_a2_corrected.v` |
| 1962 A4 | yes (8 KB) | **proved**, fully verified (compile, `Print Assumptions` = R + classical axioms only, `rocqchk`) | `putnam_1962_a4.v` (proof) |
| 1962 A5 | yes (2.9 KB) | **proved**, fully verified (compile, no axioms, `rocqchk`) | `putnam_1962_a5.v` (proof) |
| 1962 A6 | yes (3.6 KB) | upstream statement found **vacuous** (contradictory hypotheses); fix proposed; corrected statement not proved | `putnam_1962_a6.v` (upstream), `putnam_1962_a6_statement_is_vacuous.v`, `putnam_1962_a6_corrected.v` |
| 1962 B2 | yes (1.3 KB) | **proved**, fully verified (compile, `Print Assumptions` = R + classical axioms only, `rocqchk`) | `putnam_1962_b2.v` (proof) |
| 1962 B5 | yes (12.6 KB) | upstream statement found **false** (wrong bound); fix proposed; **corrected statement proved**, fully verified | `putnam_1962_b5.v` (upstream), `putnam_1962_b5_statement_is_false.v`, `putnam_1962_b5_corrected.v`, `putnam_1962_b5_corrected_proof.v` (proof) |
| 1962 B6 | yes (68 KB) | not attempted | — |
| 1963 A2 | yes (5.9 KB) | **proved**, fully verified (compile, no axioms, `rocqchk`) | `putnam_1963_a2.v` (proof) |

Summary: five of the eight proved and verified (A4, A5, B2, 1963 A2, and B5 against
its corrected statement); three of the eight found defective as published (A2, A6, B5;
see `ISSUE_REPORT_rocq.md`); one not attempted (B6, by far the hardest going by
Humanfia's file size, and the only one of the eight whose Rocq statement uses the
Coquelicot library rather than MathComp). The corrected A6 and the corrected A2 are the
other natural targets, the latter being a substantial measure-theory proof. The
A4 and B2 statements were compared with the problem text before being proved and no
defect was found in them (A4's file does need one compatibility line to parse on
current MathComp-Analysis; see `ISSUE_REPORT_rocq.md`, section 4).

Status as of 27 September 2026.
