import Mathlib
/-!
# Examples of programs and in Lean

We see our first examples of programs and proofs in Lean. A major goal is to illustrate *functional programming*, where we use recursions for loops and avoid mutable variables.

We define recursively summing to `n` and prove a theorem about it.
-/

/--
The function `sumToN` computes the sum of the first `n` natural numbers.
-/
def sumToN (n: Nat) : Nat :=
  match n with
  | 0 => 0
  | m + 1 =>
    (sumToN m) + (m + 1)

#eval sumToN 10 -- 55

/--
The theorem `sumToN_eq` states that the sum of the first `n` natural numbers is `n * (n + 1) / 2`.
-/
theorem sumToN_eq (n: Nat) : 2 * sumToN n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    unfold sumToN
    rw [left_distrib, ih]
    ring
