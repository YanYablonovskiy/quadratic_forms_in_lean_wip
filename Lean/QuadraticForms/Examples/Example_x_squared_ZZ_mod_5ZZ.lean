/-
E14_ZMod5.lean

A simple quadratic form representing x ↦ x^2
over the finite field ℤ/5ℤ,
built with the Mathlib4 QuadraticMap API.
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.ZMod.Basic

open QuadraticMap

/-- The map `x ↦ x^2` as a quadratic form over any commutative ring. -/
def squareForm {R : Type*} [CommRing R] : QuadraticForm R R :=
  ofPolar (fun x => x * x)
    (by intros a x; simp; ring)                  -- Q (a • x) = a • Q x
    (by intros x y z; simp [polar]; ring)         -- bilinear in first arg
    (by intros a x y; simp [polar]; ring)         -- bilinear in second arg

/-- Instantiate the form at `ZMod 5`. -/
def squareZMod5 : QuadraticForm (ZMod 5) (ZMod 5) := squareForm

/--
Because `CoeFun` for `QuadraticMap` is definitional,
`(squareZMod5 : ZMod 5 → ZMod 5) x` literally reduces to `x*x`.
This `@[simp]` theorem gives that reduction to `simp`.
-/
@[simp] theorem squareZMod5_toFun (x : ZMod 5) : squareZMod5 x = x * x := rfl

/-- Now `polar squareZMod5 x y` unfolds to `(x+y)^2 - x^2 - y^2 = 2*x*y` in `ZMod 5`. -/
example (x y : ZMod 5) : polar squareZMod5 x y = 2 * x * y := by
  simp [polar]; ring_nf

-- Test the evaluation on some simple values
#eval squareZMod5 0  -- Output: 0
#eval squareZMod5 1  -- Output: 1
#eval squareZMod5 2  -- Output: 4
#eval squareZMod5 3  -- Output: 4
#eval squareZMod5 4  -- Output: 1
#eval squareZMod5 (-1 : ZMod 5)  -- Output: 1

-- THIS FAILS
-- #eval squareZMod5 -1  -- Output: 1

-- Evaluate all input / output values
#eval List.map (fun x : ZMod 5 => (x, squareZMod5 x)) (List.finRange 5)
