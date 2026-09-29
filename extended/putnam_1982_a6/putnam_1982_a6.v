(* ============================================================================
   PutnamBench 1982 A6 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1982_a6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim (no compat lines were needed:
   it compiles unchanged on both toolchains listed below).
   Problem: let b be a bijection of the positive integers and x_1, x_2, ... real numbers
   with |x_n| strictly decreasing, |b(n) - n| * |x_n| -> 0 and sum_(k=1)^n x_k -> 1.
   Prove or disprove: then sum_(k=1)^n x_(b(k)) -> 1. (Answer: disprove; the limit need
   not be 1. Hence putnam_1982_a6_solution := False.)
   Defect: the statement is VACUOUS (audit verdict "vacuous (machine-checked)").
     "forall (i j: nat), le i j -> Rabs (a i) > Rabs (a j)" demands |a i| > |a i| at
     i = j, so the left side of the biconditional is False for every a and
     "... <-> putnam_1982_a6_solution" (= False) holds trivially, with no mathematics.
     Machine-checked proof that only uses this contradiction:
     putnam_1982_a6_statement_is_vacuous.v.
     Further defects (each would also make the statement unfaithful): (1) the sequence a
     is a parameter of the theorem, outside the biconditional, so even with lt the
     theorem would say "for EVERY a, not (hypotheses and claim)" instead of "not (for
     every a and b, hypotheses imply claim)"; (2) the bijection condition is garbled:
     "exists f', forall x, f' (f x) = x /\ f (f' x) = x -> Series ..." makes the
     inverse property a premise of the conclusion inside an existential, not a
     hypothesis on f (for injective f it is met by f' (f x) := x + 1 whatever the
     series do); (3)
     "INR (f i - i)" is truncated nat subtraction (0 whenever f i <= i), not |b(n) - n|;
     (4) "Series a = 1" and "Series (fun i => a (f i)) = 1" do not say that the series
     converge (Coquelicot's Series is the midpoint of liminf and limsup of the partial
     sums, cut to a real). Proposed fix: putnam_1982_a6_corrected.v.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the file is written for Coq 8.x. The Require line below triggers
   library warnings only: under Rocq 9.1.1 "Loading Stdlib without prefix is
   deprecated" (it would prefer "From Stdlib Require Import ...") and, on both
   toolchains, Coquelicot's "New coercion path [real; Finite] : Rbar >-> Rbar is not
   definitionally an identity function". None of this file's own lines produce any.
   The line is kept exactly as upstream wrote it.
   ============================================================================ *)

Require Import Nat Reals Coquelicot.Coquelicot.
Open Scope R.
Definition putnam_1982_a6_solution := False.
Theorem putnam_1982_a6
    (a: nat -> R) 
    : ((Series a = 1 /\ forall (i j: nat), le i j -> Rabs (a i) > Rabs (a j)) /\
    forall (f: nat -> nat), Lim_seq (fun i => Rabs (INR (f i - i)) * Rabs (a i)) = 0 -> exists f', forall x, f' (f x) = x /\ f (f' x) = x -> 
    Series (fun i => a (f i)) = 1) <-> putnam_1982_a6_solution.    
Proof. Admitted.
