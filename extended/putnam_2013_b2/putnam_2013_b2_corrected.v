(* ============================================================================
   PutnamBench 2013 B2 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: let C be the set of cosine polynomials f(x) = 1 + sum_{n=1}^N a_n cos(2 pi n x)
   (N >= 1) with f(x) >= 0 for all real x and a_n = 0 whenever 3 divides n; determine the
   maximum of f(0) over C and prove that it is attained (answer: 3).
   Source: coq/src/putnam_2013_b2.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: E was defined as "fun f => forall (x : R), exists
   (a : nat -> R) (N : nat), f x = 1 + sum ... /\ f x >= 0 /\ ...", so the coefficients
   and the degree could depend on the point x. Then g(x) = 1 + c cos(2 pi x)^2 lies in E
   for every c >= 0 (N = 1, a_1 = c cos(2 pi x) at the point x), f(0) is unbounded on E,
   and the hypothesis hmub is unsatisfiable: the upstream theorem is VACUOUS
   (putnam_2013_b2_statement_is_vacuous.v proves it from hmub alone with c = |m|).
   Fix: apart from this header comment, this file differs from putnam_2013_b2.v (the
   upstream statement) in one line, the first line of the definition of E, where the
   quantifier prefixes are swapped:
     "fun f => forall (x : R), exists (a : nat -> R) (N : nat), f x = ..."
       -> "fun f => exists (a : nat -> R) (N : nat), forall (x : R), f x = ..."
   Now one coefficient sequence a and one N serve for all x, i.e. E f says: f is the
   function x |-> 1 + sum_{n=1}^N a_n cos(2 pi n x) (sum_n_m ... 1 N is inclusive), it
   is >= 0 everywhere, and a_n = 0 for every n with n mod 3 = 0. (The last conjunct does
   not mention x; under "forall x" it is equivalent to stating it once, since R is
   inhabited; it is left in place to keep the diff to one line.) This is the Lean
   statement's C = union of C_N: Lean also fixes one coefficient list per f. Everything
   else is upstream's and faithful: N = 0 is allowed (the constant 1, which is also in
   C_1 with a_1 = 0, so the set of values f(0) is the same as with N >= 1); a_0 and the
   a_n with n > N are unconstrained except by the multiple-of-3 clause and do not enter
   f; hm and hmub say that m is the maximum of {f(0) | f in E}, and the conclusion
   m = 3 determines it. The upstream shape (hypotheses "m is attained" and "m is an upper
   bound", conclusion m = solution) is kept; unlike the Lean IsGreatest form it does not
   itself assert that the maximum exists, but it still determines the answer: f(x) =
   1 + 4/3 cos(2 pi x) + 2/3 cos(4 pi x) = (1 + 2 cos(2 pi x))^2 / 3 is in E with f(0) = 3
   (machine-checked, see NOTES.md), so given the solution's bound f(0) <= 3, m = 3
   satisfies hm and hmub and the same statement with any other answer is false.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the Require line below triggers library warnings only: under
   Rocq 9.1.1 three "Loading Stdlib without prefix is deprecated" warnings (Rocq would
   prefer "From Stdlib Require Import ...") and Coquelicot's "New coercion path [real;
   Finite] : Rbar >-> Rbar" ambiguous-path warning; under Coq 8.18.0 only the latter.
   None of this file's own lines produce any. The line is kept exactly as upstream
   wrote it.
   ============================================================================ *)

Require Import Ensembles Finite_sets Reals Coquelicot.Coquelicot.
Definition putnam_2013_b2_solution : R := 3.
Theorem putnam_2013_b2
    (E: Ensemble (R -> R) := fun f => exists (a : nat -> R) (N : nat), forall (x : R), f x = 1 + sum_n_m (fun n => a n * cos (2 * PI * INR n * x)) 1 N /\ f x >= 0 /\ 
    forall (n: nat), n mod 3 = 0%nat -> a n = 0)
    (m: R)
    (hm : exists f: R -> R, E f /\ f 0 = m)
    (hmub : forall f : R -> R, E f -> f 0 <= m)
    : m = putnam_2013_b2_solution.
Proof. Admitted.
