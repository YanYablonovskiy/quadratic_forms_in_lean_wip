/-
E14_ZZ.lean

A simple quadratic form representing x ↦ x^2,
built with the Mathlib4 QuadraticMap API.
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic

open QuadraticMap

/-- The map `x ↦ x^2` as a quadratic form over any commutative ring. -/
def squareForm {R : Type*} [CommRing R] : QuadraticForm R R :=
  ofPolar (fun x => x * x)
    (by intros a x; simp; ring)                   -- Q (a • x) = a • Q x
    (by intros x y z; simp [polar]; ring)         -- bilinear in first arg
    (by intros a x y; simp [polar]; ring)         -- bilinear in second arg

/-- Instantiate the same form at `Int`. -/
def squareInt : QuadraticForm Int Int := squareForm

/--
Because `CoeFun` for `QuadraticMap` is definitional,
`(squareInt : Int → Int) x` literally reduces to `x*x`.
This `@[simp]` gives that reduction to `simp`.
-/
@[simp] theorem squareInt_toFun (x : Int) : squareInt x = x * x := rfl

/-- Now `polar squareInt x y` unfolds to `(x+y)^2 - x^2 - y^2 = 2*x*y`. -/
example (x y : Int) : polar squareInt x y = 2 * x * y := by
  simp [polar]; ring_nf



-- Test the evaluation on some simple values
#eval squareInt 0  -- Output: 0
#eval squareInt 1  -- Output: 1
#eval squareInt 2  -- Output: 4
#eval squareInt (-1) -- Output: 1


-- Test the associated polar form type
#check squareInt.polar_self
#check squareInt.polar_self 2


-- How to evaluate the polar form?
-- #eval squareInt.polar_self 2
