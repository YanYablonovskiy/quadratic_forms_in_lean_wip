import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-- A simple quadratic form representing x² from ℤ to ℤ -/
def squareForm : QuadraticForm ℤ ℤ where
  toFun := fun x => x * x
  toFun_smul := by
    intro a x
    simp only [smul_eq_mul]  -- This simplifies a • x to a * x
    -- Need to show: (a * x)² = a² * x²
    rw [mul_mul_mul_comm a x a x]  -- Rearranges (a*x)*(a*x) to (a*a)*(x*x)
    -- rfl  -- Reflexivity finishes the proof
  exists_companion' := by
    -- We need to provide a bilinear form B such that (x+y)² = x² + y² + B(x,y)
    -- For the square function, B(x,y) = 2*x*y

    -- We'll prove this exists without directly constructing B
    have h : ∀ x y : ℤ, (x + y) * (x + y) = x * x + y * y + 2 * x * y := by
      intro x y
      ring


    -- We'll construct a bilinear map directly using LinearMap.BilinMap structure
    let B : LinearMap.BilinMap ℤ ℤ ℤ :=
      { toFun := fun x y => 2 * x * y,
        toFun_add_left := by
          intros x₁ x₂ y
          simp only [add_mul]
          ring
        toFun_add_right := by
          intros x y₁ y₂
          simp only [mul_add]
          ring
        toFun_smul_left := by
          intros r x y
          simp only [smul_eq_mul]
          ring
        toFun_smul_right := by
          intros r x y
          simp only [smul_eq_mul]
          ring }

    -- Use our bilinear map for the companion
    use B


    -- Define our companion bilinear map
    let B : LinearMap.BilinMap ℤ ℤ := fun x y => 2 * x * y

    -- Prove it's bilinear (we'll use the simp attribute to help)
    have B_add_left : ∀ (x₁ x₂ y : ℤ), B (x₁ + x₂) y = B x₁ y + B x₂ y := by
      intro x₁ x₂ y
      simp [B]
      ring

    have B_smul_left : ∀ (a x y : ℤ), B (a * x) y = a * B x y := by
      intro a x y
      simp [B]
      ring

    have B_add_right : ∀ (x y₁ y₂ : ℤ), B x (y₁ + y₂) = B x y₁ + B x y₂ := by
      intro x y₁ y₂
      simp [B]
      ring

    have B_smul_right : ∀ (a x y : ℤ), B x (a * y) = a * B x y := by
      intro a x y
      simp [B]
      ring

    -- Create the actual bilinear map using the lemmas we proved
    let bilin : LinearMap.BilinForm ℤ ℤ := {
      bilin := B,
      bilin_add_left := B_add_left,
      bilin_smul_left := B_smul_left,
      bilin_add_right := B_add_right,
      bilin_smul_right := B_smul_right
    }

    -- Use our bilinear form for the companion
    use bilin

    -- Prove the main property: (x+y)² = x² + y² + B(x,y)
    intro x y
    simp [bilin]
    -- Expand (x+y)²
    calc (x + y) * (x + y) = x * x + x * y + y * x + y * y := by simp [mul_add, add_mul]
                         _ = x * x + y * y + (x * y + y * x) := by ring
                         _ = x * x + y * y + 2 * x * y := by
                            rw [← mul_two, ← mul_add]
                            rw [mul_comm y x]
                            simp [mul_add, two_mul]
