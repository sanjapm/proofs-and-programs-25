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

def sumToN' (n: Nat) : Nat :=
  if n = 0 then 0 else (sumToN' (n - 1)) + n

#eval sumToN' 10 -- 55

theorem sumToN_eq' (n: Nat) : 2 * sumToN' n = n * (n + 1) := by
  rw [sumToN']
  split
  case isTrue h =>
    rw [h]
  case isFalse h =>
    rw [left_distrib, sumToN_eq']
    let m := n - 1
    have h' : n = m + 1 := by
      show n = n - 1 + 1
      symm
      apply Nat.sub_add_cancel
      exact Nat.pos_iff_ne_zero.mpr h
    rw [h']
    simp
    ring

def sumToN'' (n: Nat) : Nat := Id.run do
  let mut sum := 0
  for i in [0:n] do
    sum := sum + i
  return sum
