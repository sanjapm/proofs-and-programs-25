import Mathlib
/-!
# Examples of programs and in Lean

We see our first examples of programs and proofs in Lean. A major goal is to illustrate *functional programming*, where we use recursions for loops and avoid mutable variables.
-/

def sumToN (n: Nat) : Nat := Id.run do
  let mut sum := 0
  for i in [1:n+1] do
    sum := sum + i
  return sum

#eval sumToN 10
