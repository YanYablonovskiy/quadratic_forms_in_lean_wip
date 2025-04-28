import Mathlib.LinearAlgebra.QuadraticForm.Basic

-- Define a quadratic form for x² from ℤ to ℤ
def squareForm : QuadraticForm ℤ ℤ :=
{ toFun := fun x => x * x,
  toFun_smul := by
    intro a x
    -- In ℤ, a • x = a * x
    simp only [smul_eq_mul]
    -- Need to show: (a * x)² = a² • x²
    rw [mul_mul_mul_comm a x a x]
  exists_companion' := by
    -- We need a bilinear form B such that (x + y)² = x² + y² + B x y
    -- For squares, B x y = 2*x*y

    -- First define our bilinear map
    let B : BilinMap ℤ ℤ ℤ :=
    { toFun := fun x y => 2 * x * y,
      toFun_add_left := by
        intros x₁ x₂ y
        simp only [mul_add]
        ring
      toFun_add_right := by
        intros x y₁ y₂
        simp only [add_mul]
        ring
      toFun_smul_left := by
        intros r x y
        simp only [smul_eq_mul]
        ring
      toFun_smul_right := by
        intros r x y
        simp only [smul_eq_mul]
        ring
    }

    -- Now prove the identity (x+y)² = x² + y² + B x y
    use B
    intros x y
    -- Expand (x + y)²
    simp only [add_mul, mul_add]
    -- We get x*x + x*y + y*x + y*y
    -- We need to show this equals x*x + y*y + 2*x*y
    rw [mul_comm y x]
    ring
}
