(* ============================================================================
   PutnamBench 1982 A6 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: let b be a bijection of the positive integers and x_1, x_2, ... real numbers
   with |x_n| strictly decreasing, |b(n) - n| * |x_n| -> 0 and sum_(k=1)^n x_k -> 1;
   prove or disprove that then sum_(k=1)^n x_(b(k)) -> 1 (answer: disprove, so
   putnam_1982_a6_solution := False, unchanged).
   Source: coq/src/putnam_1982_a6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement (audit verdict "vacuous (machine-checked)"): the
   monotonicity hypothesis "forall (i j: nat), le i j -> Rabs (a i) > Rabs (a j)" fails
   at i = j, so the left side of "... <-> putnam_1982_a6_solution" is False for every a
   and the theorem holds trivially (putnam_1982_a6_statement_is_vacuous.v). Re-reading
   the whole statement found four more defects: the sequence a is quantified outside
   the biconditional (so the theorem would claim "for every a, not (...)"); the
   bijection condition is attached, inside an existential, as a premise of the
   conclusion instead of being a hypothesis on f; "INR (f i - i)" is truncated nat
   subtraction (0 when f i <= i) instead of |b(n) - n|; and "Series ... = 1" does not
   express convergence of the partial sums to 1 (Coquelicot's Series of a divergent
   series is still some real number).
   Fix (the four lines of the statement, before -> after):
     (a: nat -> R)
       -> : (forall (a: nat -> R),                          [a inside the claim]
     : ((Series a = 1 /\ forall (i j: nat), le i j -> ...) /\
       -> (is_series a 1 /\ forall (i j: nat), lt i j -> ...) ->
                         [partial sums converge to 1; strictly decreasing |a|]
     forall (f: nat -> nat), Lim_seq (fun i => Rabs (INR (f i - i)) * Rabs (a i)) = 0 -> exists f', forall x, f' (f x) = x /\ f (f' x) = x ->
       -> forall (f: nat -> nat), is_lim_seq (fun i => Rabs (INR (f i) - INR i) * Rabs (a i)) 0 -> (exists f', forall x, f' (f x) = x /\ f (f' x) = x) ->
                         [|f(i) - i| on R; limit 0; f has a two-sided inverse]
     Series (fun i => a (f i)) = 1) <-> putnam_1982_a6_solution.
       -> is_series (fun i => a (f i)) 1) <-> putnam_1982_a6_solution.
                         [the rearranged partial sums converge to 1]
   (the trailing blanks of two upstream lines are dropped). The result says: "for all
   a, f: if sum a_n -> 1 with |a_n| strictly decreasing, |f(n) - n| |a_n| -> 0 and f is
   a bijection of nat, then sum a_(f(n)) -> 1" iff False; this is the Lean statement
   (Tendsto of the partial sums in hypothesis and conclusion, BijOn b on Ici 1) with
   0-based indices: b : positive integers -> positive integers corresponds to
   f(n) = b(n + 1) - 1, x_n to a(n - 1), and |f(n) - n| = |b(n + 1) - (n + 1)|, so all
   hypotheses and the conclusion correspond exactly. is_lim_seq replaces
   "Lim_seq ... = 0" for clarity: for a nonnegative sequence the two are equivalent
   (machine-checked in a scratch file, see NOTES.md), so this is not a change of meaning.
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
    : (forall (a: nat -> R),
    (is_series a 1 /\ forall (i j: nat), lt i j -> Rabs (a i) > Rabs (a j)) ->
    forall (f: nat -> nat), is_lim_seq (fun i => Rabs (INR (f i) - INR i) * Rabs (a i)) 0 -> (exists f', forall x, f' (f x) = x /\ f (f' x) = x) ->
    is_series (fun i => a (f i)) 1) <-> putnam_1982_a6_solution.
Proof. Admitted.
