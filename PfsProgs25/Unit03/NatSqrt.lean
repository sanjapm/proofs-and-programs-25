/-!
# Structures: Square root of a natural number

We have seen the following types:

* Universes
* Function types
* Dependent function types

There is only one other basic type construction in Lean: **Inductive Types** and their generalization, **Indexed Inductive Types**.

We start with a special class of inductive types: structures. We will also see how to combine data and proofs and to prove with tactics.

## Square root of a natural number
-/

/-!
## A lemma

We will define a function that gives the square root of a product of two natural numbers. We will first prove a lemma that will be useful in the definition. This will be proved using tactics.

Note that all the `rw` tactics can be written as a single tactic with a list of rewrites.
-/
theorem sqrt_mul (a b : Nat) : (a * a) * (b * b) = (a * b) * (a * b) := by
  sorry
