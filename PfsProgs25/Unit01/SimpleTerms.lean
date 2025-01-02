/-!
# Simple Terms and Types

We consider a few terms and types in Lean. These are definitions that do not involve recursion/induction or propositions.
-/


/-!
## Function types
-/


/-!
## Curried functions

Suppose we want to define the function `f` of two variables `a` and `b` taking value `a + b + 1`. We can define it as a function of one variable `a` returning a function of one variable `b`.
-/
