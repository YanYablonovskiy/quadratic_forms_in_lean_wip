-- /-
-- E10_ZZ.lean
--DEFINED ELSEWHERE
-- A simple quadratic form representing x ↦ x^2,
-- built with the Mathlib4 QuadraticMap API.
-- -/
-- import Mathlib.LinearAlgebra.QuadraticForm.Basic

-- open QuadraticMap

-- /-- The map \(x\mapsto x^2\) as a quadratic form over any commutative ring. -/
-- def squareForm {R : Type*} [CommRing R] : QuadraticForm R R :=
--   ofPolar (fun x => x * x)
--     -- Q (a • x) = a * a • Q x
--     (by intros a x; simp)
--     -- bilinearity in the first argument of the polar form
--     (by intros x y z; simp [polar]; ring)
--     -- bilinearity in the second argument of the polar form
--     (by intros a x y; simp [polar]; ring)

-- /-- Instantiate the same form at `Int`. -/
-- def squareInt : QuadraticForm Int Int := squareForm

-- -- Optional sanity checks:
-- @[simp] theorem squareInt_apply (x : Int) :
--     squareInt.toFun x = x * x :=
--   rfl

-- example (x y : Int) :
--     polar squareInt x y = 2 * x * y := by
--   -- `polar` is by definition Q (x + y) - Q x - Q y
--   simp [polar]
