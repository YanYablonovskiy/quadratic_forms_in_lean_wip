/-
E14_sum_of_two_squares_using_squareForm.lean

Build the quadratic form (x,y) ↦ x^2 + y^2 by taking
the orthogonal direct sum (prod) of two copies of
the one‐variable `squareForm`.
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Prod

open QuadraticMap

/-- The one‐variable form x ↦ x^2. -/
def squareForm {R : Type*} [CommRing R] : QuadraticForm R R :=
  ofPolar (fun x => x * x)
    (by intros a x; simp; ring)
    (by intros x y z; simp [polar]; ring)
    (by intros a x y; simp [polar]; ring)

/-- Sum of two copies of `squareForm`: (x,y) ↦ squareForm x + squareForm y. -/
def sumOfTwoSquares {R : Type*} [CommRing R] : QuadraticForm R (R × R) :=
  squareForm.prod squareForm

@[simp] theorem sumOfTwoSquares_toFun {R : Type*} [CommRing R] (p : R × R) :
    sumOfTwoSquares p = squareForm p.1 + squareForm p.2 :=
rfl

/- Unfold both `squareForm` and `sumOfTwoSquares`. -/
/-
@[simp] theorem sumOfTwoSquares_expand {R : Type*} [CommRing R] (x y : R) :
    sumOfTwoSquares (x, y) = x * x + y * y := by
    simp [sumOfTwoSquares_toFun]
-/


/-- Instantiate on `Int`. -/
def sumOfTwoSquaresInt : QuadraticForm Int (Int × Int) := sumOfTwoSquares

-- Quick checks
#eval sumOfTwoSquaresInt (1,2)    -- 1 + 4 = 5
#eval sumOfTwoSquaresInt (-3,4)   -- 9 + 16 = 25
#eval polar sumOfTwoSquaresInt (1,2) (3,5)  -- 2*(1*3 + 2*5) = 2*13 = 26
