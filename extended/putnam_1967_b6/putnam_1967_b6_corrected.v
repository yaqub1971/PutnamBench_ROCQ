(* ============================================================================
   PutnamBench 1967 B6 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: let f be a real-valued function which is defined for x^2 + y^2 <= 1, has
   partial derivatives, and satisfies |f(x, y)| <= 1; show that some point (x0, y0) with
   x0^2 + y0^2 < 1 has (df/dx (x0, y0))^2 + (df/dy (x0, y0))^2 <= 16.
   Source: coq/src/putnam_1967_b6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: the second conjunct of fdiff,
   "forall y0 : R, differentiable (fun y => f y y0) y0", passes the lambda's variable y
   as the FIRST argument of f, so it only says that x |-> f x y0 is differentiable at
   x = y0 -- an instance of the first conjunct. fdiff is thus equivalent to
   differentiability in x alone and nothing is assumed about df/dy (f x y = |y|
   satisfies every upstream hypothesis), although the conclusion uses the derivative in
   y. Moreover the statement has no continuity hypothesis, which the problem's standard
   solution needs (see below) and which the benchmark's Lean statement has (fcont).
   Fix: apart from this header comment, this file differs from putnam_1967_b6.v (the
   upstream statement) in two lines of the statement:
     1. in fdiff,
          "(forall y0 : R, differentiable (fun y => f y y0) y0))"
        -> "(forall x y0 : R, differentiable (fun y => f x y) y0))":
        for every x the function y |-> f x y is differentiable at every y0, i.e. df/dy
        exists everywhere. With the unchanged first conjunct (df/dx exists everywhere)
        this is exactly the Lean hypothesis fdiff; upstream's outer "forall y" is kept and
        is simply not used by the second conjunct.
     2. new hypothesis, placed between fdiff and fbound as in the Lean statement:
          "(fcont : {within (fun p : R * R => p.1^+2 + p.2^+2 <= 1), continuous (fun p : R * R => f p.1 p.2)})":
        f, as a function of the point p = (x, y) of R x R, is continuous on the closed
        unit disk (continuity of its restriction to the disk: the Lean hypothesis
        ContinuousOn (fun p => f p.1 p.2) {p | p.1 ^ 2 + p.2 ^ 2 <= 1}).
        Why: the informal text does not say "continuous", but the problem's solution
        (the minimum over the closed disk of f(x, y) + 2 (x^2 + y^2), which is >= 1 on the
        circle and <= 1 at the centre, is attained at an interior point, where
        df/dx = -4x and df/dy = -4y) needs the minimum to exist, and partial derivatives
        alone do not make f continuous (2xy / (x^2 + y^2) has both everywhere). Without
        fcont the truth of the statement is not established. This is a deliberate
        deviation from the literal wording, following the Lean statement; see NOTES.md.
        The disk is written as a lambda (coerced to a set) because "[set p | ...]" would
        resolve to MathComp's finset notation here: upstream does not import
        classical_sets.
   Everything else is upstream's and faithful: fbound is |f x y| <= 1 on the closed disk;
   the point is in the open disk (< 1); the bound is <= 16; (fun x => f x y0)^`() x0 and
   (fun y => f x0 y)^`() y0 are df/dx and df/dy at (x0, y0). As in upstream and Lean, f
   is defined on all of R x R and has partial derivatives everywhere ("boosted" domain).
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp-Analysis 1.16: (1) a Variable
   outside a Section is an error since Rocq 9.0; (2) since MathComp-Analysis 1.9.0 the
   derivative notation f^`() exists only in classical_set_scope, which the upstream
   statement never opens. Neither changes the meaning of the statement. The notation
   {within A, continuous f} of the new line 2 is declared in classical_set_scope on both
   library versions, so that line also relies on the scope opened by compat line (2).
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the two "From mathcomp Require Import" lines below trigger
   warnings emitted by MathComp itself (all_ssreflect deprecated since MathComp 2.5 on
   Rocq 9.1, ambiguous coercion paths, overridden notations). They are library warnings,
   not warnings about this file: none of this file's own lines produce any. The import
   lines are kept exactly as upstream wrote them.
   ============================================================================ *)

From mathcomp Require Import all_ssreflect ssrnum ssralg.
From mathcomp Require Import reals normedtype derive topology sequences.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope. (* compat: since MathComp-Analysis 1.9.0 the derivative notations f^`() and f^`(2) exist only in classical_set_scope, which the upstream statement never opens. Opened before ring_scope so that the ring notations keep precedence. *)
Local Open Scope ring_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Theorem putnam_1967_b6
    (f : R -> R -> R)
    (fdiff : forall y : R, (forall x0 : R, differentiable (fun x => f x y) x0) /\ 
                            (forall x y0 : R, differentiable (fun y => f x y) y0))
    (fcont : {within (fun p : R * R => p.1^+2 + p.2^+2 <= 1), continuous (fun p : R * R => f p.1 p.2)})
    (fbound : forall x y : R, x^+2 + y^+2 <= 1 -> `| f x y | <= 1)
    : exists x0 y0 : R, x0^+2 + y0^+2 < 1 /\ 
        ((fun x : R => f x y0)^`() x0)^+2 + ((fun y : R => f x0 y)^`() y0)^+2 <= 16.
Proof. Admitted.