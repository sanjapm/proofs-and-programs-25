import Std
/-!
## Fibonacci numbers: memoization using the state monad

The naive way of computing Fibonacci numbers is very inefficient because it recomputes the same values many times. We can use the state monad to store the values of the Fibonacci numbers we have already computed. This is a simple example of memoization.

We will also take a more complicated example: Catalan numbers. The Catalan numbers are a sequence of natural numbers that occur in various counting problems, often involving recursively defined objects. They satisfy the recurrence relation:
* $C_0 = 1`,
* $C_{n+1} = \sum_{i=0}^n C_i C_{n-i}$, for $n \geq 0.$
-/
open Std
#check HashMap
#check StateM


abbrev CatalanM (α : Type)  := StateM (HashMap Nat Nat) α

def catalan (n : Nat): CatalanM Nat := do
  let memo ← get
  match memo.get? n with
  | some v => return v
  | none => do
    let result ← match n with
    | 0 => return 1
    | n + 1 => do
      let mut sum := 0
      for c:i in [0:n+1] do
        have := c.upper
        sum := sum + (←catalan i) * (←catalan (n-i))
      pure sum
    modify (·.insert n result)
    return result

#eval catalan 100 |>.run' {}
#check Std.Range
