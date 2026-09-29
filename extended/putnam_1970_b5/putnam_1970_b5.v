(* ============================================================================
   PutnamBench 1970 B5 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1970_b5.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim, except for the lines
   marked "(* compat: ... *)".
   Problem: with u_n(x) = -n for x <= -n, x for -n < x <= n, n for x > n, a function
   F : R -> R is continuous iff u_n o F is continuous for every natural number n.
   Defect (naming; the mathematics is faithful): the theorem is declared as
     Theorem putnam_1970_b5_solution
   although the problem is a pure "show that" with nothing to determine, so the name
   should be putnam_1970_b5 (PutnamBench's informal and Lean statements are both named
   putnam_1970_b5; the suffix _solution is reserved for the answer Definition of
   "find/determine" problems, and this file has no such Definition). A harness or a
   proof file that looks for the theorem putnam_1970_b5 does not find it. The statement
   is neither false nor vacuous, so there is no _statement_is_false /
   _statement_is_vacuous file.
   Proposed fix: putnam_1970_b5_corrected.v (the theorem is renamed putnam_1970_b5;
   no other token changes).
   Reading the statement: "(ramp : int -> (R -> R) := ...)" is a let-binding (a
   definition of u_n, not a hypothesis); its middle test "-n <= x <= n" differs from the
   problem's "-n < x <= n" only at x = -n, which the first branch already catches, so
   ramp n is exactly u_n (for every n : int). "continuous" is MathComp-Analysis'
   continuity at every point of R (forall x, g @ x --> g x), "\o" is function
   composition, and n ranges over nat (n = 0 gives the constant function 0, which is
   continuous and changes nothing).
   Compat line: the line marked "(* compat: ... *)" was added because the upstream
   file does not compile at all on Rocq 9.1: a Variable outside a Section is an error
   since Rocq 9.0 (Coq 8.x only warns). It does not change the meaning of the
   statement; on Coq 8.18 it only silences the local-declaration warning of the
   Variable line. The repository's other compat lines are not needed here: the
   statement uses no 1 / %:R (only - and %:~R), it compiles on Rocq 9.1 / MathComp 2.5
   without the ssralg re-import, and its elaborated type is byte-identical with and
   without it (Set Printing All); it uses no derivative notation.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. The first import line below triggers warnings emitted by MathComp
   itself (among them, under Rocq 9.1 / MathComp 2.5, the deprecation of all_ssreflect;
   under both toolchains ambiguous coercion paths and overridden notations). They are
   library warnings, not warnings about this file: none of this file's own lines
   produce any. The import lines are kept exactly as upstream wrote them so that the
   statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals exp sequences topology normedtype.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Theorem putnam_1970_b5_solution
    (ramp : int -> (R -> R) := fun (n : int) => (fun (x : R) => if x <= -n%:~R then -n%:~R else (if -n%:~R <= x <= n%:~R then x else n%:~R)))
    (F : R -> R)
    : continuous F <-> (forall n : nat, continuous (ramp (n%:Z) \o F)).
Proof. Admitted.
