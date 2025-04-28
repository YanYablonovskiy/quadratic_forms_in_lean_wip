import Mathlib.LinearAlgebra.QuadraticForm.Basic

open QuadraticMap  -- brings `polar` and `polarBilin` into scope
open LinearMap    -- brings `BilinMap` into scope

namespace QuadraticForms

/-- A shorthand for “a quadratic form `Q : M → R` with the usual hypotheses.” -/
abbrev QuadForm (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :=
  QuadraticForm R M

namespace QuadForm
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]



/-- The companion bilinear map attached to a quadratic form. -/
def associatedBilinearMap (Q : QuadForm R M) : LinearMap.BilinMap R M R :=
  Q.polarBilin

@[simp]
theorem associatedBilinearMap_apply (Q : QuadForm R M) (x y : M) :
    associatedBilinearMap Q x y = Q (x + y) - Q x - Q y :=
rfl

/--  The symmetric bilinear form attached to `Q`.  -/
def associatedBilinForm (Q : QuadForm R M) : LinearMap.BilinForm R M :=
  Q.polarBilin  -- a `BilinMap R M R` coerces to `BilinForm R M`

/--  `Q` is nondegenerate iff its associated bilinear form is.  -/
def Nondegenerate (Q : QuadForm R M) : Prop :=
  Q.associatedBilinForm.Nondegenerate

-- Looked for the associated non-degenerate reference at, but didn't find one:
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/BilinearMap.html#LinearMap.BilinMap



/-- A quadratic form is *anisotropic* if Q(x) = 0 implies x = 0. -/
def Anisotropic (Q : QuadForm R M) : Prop :=
  ∀ x : M, Q x = 0 → x = 0

/-- A quadratic form is *isotropic* if there exists a nonzero x with Q(x) = 0. -/
def Isotropic (Q : QuadForm R M) : Prop :=
  ∃ x : M, x ≠ 0 ∧ Q x = 0


end QuadForm
end QuadraticForms
