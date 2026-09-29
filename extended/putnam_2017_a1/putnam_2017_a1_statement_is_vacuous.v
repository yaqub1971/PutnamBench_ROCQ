(* ============================================================================
   PutnamBench 2017 A1 -- proof that the UPSTREAM statement is vacuous.
   The Definition and the Theorem below are upstream's statement verbatim
   (coq/src/putnam_2017_a1.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20)), apart from the
   three lines marked "(* compat: ... *)", closed by a one-line proof that only exploits
   the contradiction in hypothesis hS (no mathematics involved): its second conjunct
   "forall T : set int, T `<=` S -> ~ IsQualifying T", instantiated at T = S (S `<=` S
   holds trivially), gives ~ IsQualifying S, while its first conjunct is IsQualifying S.
   Hence the theorem holds whatever putnam_2017_a1_solution is.
   Compile with:  rocq compile -R . "" putnam_2017_a1_statement_is_vacuous.v
   (standalone; with Coq 8.18 use coqc instead of rocq compile).
   Print Assumptions at the end lists only the three classical axioms of
   mathcomp.classical (boolp.propositional_extensionality,
   boolp.functional_extensionality_dep, boolp.constructive_indefinite_description);
   they come from the statement itself: membership "n \in S" in a classical set
   S : set int is decided by boolp's asbool. No other assumption is used.
   Compat lines: the lines marked "(* compat: ... *)" are the ones of putnam_2017_a1.v
   (re-import of ssralg, needed on MathComp 2.5 for the ring notation 1 in the solution
   set); they change nothing in the meaning of the statement.
   Verified on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (Nix) and on
   Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (Ubuntu 24.04): compiles and
   prints the assumption list described above.
   About the warnings: the first import line below triggers library warnings emitted by
   MathComp itself (all_ssreflect is deprecated since 2.5, ambiguous coercion paths,
   overridden notations). They are library warnings, not warnings about this file: none
   of this file's own lines produce any. The import lines are kept exactly as upstream
   wrote them.
   ============================================================================ *)

(* The benchmark statement putnam_2017_a1.v, verbatim, closed by a proof that only
   exploits the contradiction in hS (no mathematics involved): *)
From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import classical_sets.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition putnam_2017_a1_solution : set int := [set x : int | x > 0 /\ (x = 1 \/ (5 %| x)%Z)].
Theorem putnam_2017_a1
    (IsQualifying : (set int) -> Prop)
    (IsQualifying_def : forall S, IsQualifying S <-> 
        (forall n : int, n \in S -> n > 0) /\
        2 \in S /\
        (forall n : int, n > 0 /\ (n ^ 2) \in S -> n \in S) /\
        (forall n : int, n \in S -> (n + 5) ^ 2 \in S))
    (S : set int)
    (hS : IsQualifying S /\ forall T : set int, T `<=` S -> ~ IsQualifying T)
    : ~` S `&` [set n : int | n > 0] = putnam_2017_a1_solution.
Proof.
(* T := S is a subset of S, so the 2nd conjunct of hS denies the 1st, IsQualifying S *)
by case: hS => hq /(_ S (fun _ h => h)) /(_ hq).
Qed.
Print Assumptions putnam_2017_a1.
