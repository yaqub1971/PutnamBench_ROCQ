(* ============================================================================
   PutnamBench 1967 B6 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1967_b6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim, except for the lines
   marked "(* compat: ... *)".
   Problem: let f be a real-valued function which is defined for x^2 + y^2 <= 1, has
   partial derivatives, and satisfies |f(x, y)| <= 1; show that some point (x0, y0) with
   x0^2 + y0^2 < 1 has (df/dx (x0, y0))^2 + (df/dy (x0, y0))^2 <= 16.
   Defects found in this statement (audit verdict: unfaithful):
     1. The second conjunct of fdiff, "forall y0 : R, differentiable (fun y => f y y0) y0",
        differentiates in the FIRST argument of f again: the variable y bound by the
        lambda is passed as the first argument, so the conjunct says that x |-> f x y0 is
        differentiable at the point x = y0, which is already an instance of the first
        conjunct. The hypothesis fdiff is therefore equivalent to differentiability in x
        alone (machine-checked, see NOTES.md), and nothing is assumed about df/dy, although
        the conclusion is about the derivative in y; e.g. f x y = |y|, which has no partial
        derivative in y at y = 0, satisfies all the hypotheses.
     2. Continuity of f on the closed disk (hypothesis fcont of the benchmark's Lean
        statement) is missing. The standard solution takes the minimum of
        f(x, y) + 2 (x^2 + y^2) over the closed disk and needs it; partial derivatives
        alone do not make f continuous (2xy / (x^2 + y^2) has both everywhere).
     No evidence file: the verdict is "unfaithful", not "false" or "vacuous"; the
     hypotheses are satisfiable (f = 0) and no counterexample to this statement is known.
     Proposed fix: putnam_1967_b6_corrected.v (one line of the statement changed, one
     hypothesis line added).
   Reading the statement: "differentiable g x0" for g : R -> R is MathComp-Analysis'
   (Frechet) differentiability at x0, equivalent to the existence of the derivative
   g^`() x0 (lemma derivable1_diffP); "g^`() x0" is that derivative (derive1). f is
   defined on all of R x R and has partial derivatives everywhere (the Lean file notes
   the same "boosted" domain).
   Compat lines: the lines marked "(* compat: ... *)" were added because the upstream
   file does not compile at all on Rocq 9.1 / MathComp-Analysis 1.16: (1) a Variable
   outside a Section is an error since Rocq 9.0; (2) since MathComp-Analysis 1.9.0 the
   derivative notation f^`() exists only in classical_set_scope, which the upstream
   statement never opens. Neither changes the meaning of the statement.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. The two "From mathcomp Require Import" lines below trigger warnings
   emitted by MathComp itself (all_ssreflect deprecated since MathComp 2.5 on Rocq 9.1,
   ambiguous coercion paths, overridden notations). They are library warnings, not
   warnings about this file: none of this file's own lines produce any. The import lines
   are kept exactly as upstream wrote them so that the statement stays identical to the
   benchmark's.
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
                            (forall y0 : R, differentiable (fun y => f y y0) y0))
    (fbound : forall x y : R, x^+2 + y^+2 <= 1 -> `| f x y | <= 1)
    : exists x0 y0 : R, x0^+2 + y0^+2 < 1 /\ 
        ((fun x : R => f x y0)^`() x0)^+2 + ((fun y : R => f x0 y)^`() y0)^+2 <= 16.
Proof. Admitted.