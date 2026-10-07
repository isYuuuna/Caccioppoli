import Mathlib

/-!
# Abstract energy estimate

The analytic estimate used in the Caccioppoli inequality, isolated from PDE
and cutoff assumptions.
-/

open MeasureTheory

/-- The analytic energy estimate underlying the Caccioppoli inequality. -/
theorem energy_estimate
    {α : Type*} [MeasurableSpace α]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (μ : Measure α) (u η : α → ℝ) (g h : α → V)
    (hA : Integrable (fun x => η x ^ 2 * ‖g x‖ ^ 2) μ)
    (hB : Integrable (fun x => u x ^ 2 * ‖h x‖ ^ 2) μ)
    (hcross : Integrable (fun x => u x * η x * inner ℝ (g x) (h x)) μ)
    (henergy :
      (∫ x, η x ^ 2 * ‖g x‖ ^ 2 ∂μ) =
        -2 * ∫ x, u x * η x * inner ℝ (g x) (h x) ∂μ) :
    (∫ x, η x ^ 2 * ‖g x‖ ^ 2 ∂μ) ≤
      4 * ∫ x, u x ^ 2 * ‖h x‖ ^ 2 ∂μ := by
  have hpoint (x : α) :
      -2 * (u x * η x * inner ℝ (g x) (h x)) ≤
        (1 / 2 : ℝ) * (η x ^ 2 * ‖g x‖ ^ 2) +
          2 * (u x ^ 2 * ‖h x‖ ^ 2) := by
    -- Cauchy-Schwarz bounds the inner product by the product of the norms.
    have hcs := abs_real_inner_le_norm (g x) (h x)
    have hinner :
        |u x * η x * inner ℝ (g x) (h x)| ≤
          |u x| * |η x| * (‖g x‖ * ‖h x‖) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left hcs (by positivity)
    -- Young's inequality follows from nonnegativity of a square.
    have hyoung := sq_nonneg (|η x| * ‖g x‖ - 2 * (|u x| * ‖h x‖))
    calc
      -2 * (u x * η x * inner ℝ (g x) (h x)) ≤
          2 * |u x * η x * inner ℝ (g x) (h x)| := by
        have hneg := neg_le_abs (u x * η x * inner ℝ (g x) (h x))
        nlinarith
      _ ≤ 2 * (|u x| * |η x| * (‖g x‖ * ‖h x‖)) := by
        exact mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ = 2 * ((|η x| * ‖g x‖) * (|u x| * ‖h x‖)) := by ring
      _ ≤ (1 / 2 : ℝ) * (η x ^ 2 * ‖g x‖ ^ 2) +
          2 * (u x ^ 2 * ‖h x‖ ^ 2) := by
        nlinarith [sq_abs (η x), sq_abs (u x)]
  -- Integrate the pointwise inequality, using integrability of both sides.
  have hleft : Integrable
      (fun x => -2 * (u x * η x * inner ℝ (g x) (h x))) μ :=
    hcross.const_mul (-2)
  have hright : Integrable
      (fun x =>
        (1 / 2 : ℝ) * (η x ^ 2 * ‖g x‖ ^ 2) +
          2 * (u x ^ 2 * ‖h x‖ ^ 2)) μ := by
    exact (hA.const_mul (1 / 2 : ℝ)).add (hB.const_mul 2)
  have hint := integral_mono_ae hleft hright
    (Filter.Eventually.of_forall hpoint)
  -- Substitute the energy identity and simplify the integrated sums.
  have hintegrated :
      (∫ x, η x ^ 2 * ‖g x‖ ^ 2 ∂μ) ≤
        (1 / 2 : ℝ) * (∫ x, η x ^ 2 * ‖g x‖ ^ 2 ∂μ) +
          2 * ∫ x, u x ^ 2 * ‖h x‖ ^ 2 ∂μ := by
    calc
      (∫ x, η x ^ 2 * ‖g x‖ ^ 2 ∂μ) =
          -2 * ∫ x, u x * η x * inner ℝ (g x) (h x) ∂μ := henergy
      _ = ∫ x, -2 * (u x * η x * inner ℝ (g x) (h x)) ∂μ := by
        rw [← integral_const_mul]
      _ ≤ ∫ x,
          (1 / 2 : ℝ) * (η x ^ 2 * ‖g x‖ ^ 2) +
            2 * (u x ^ 2 * ‖h x‖ ^ 2) ∂μ := hint
      _ = (1 / 2 : ℝ) * (∫ x, η x ^ 2 * ‖g x‖ ^ 2 ∂μ) +
          2 * ∫ x, u x ^ 2 * ‖h x‖ ^ 2 ∂μ := by
        rw [integral_add (hA.const_mul (1 / 2 : ℝ)) (hB.const_mul 2)]
        rw [integral_const_mul, integral_const_mul]
  -- Rearrange to remove half of the energy from both sides.
  linarith
