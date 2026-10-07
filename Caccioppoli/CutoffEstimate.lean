import Mathlib
import Caccioppoli.EnergyEstimate

/-!
# Caccioppoli estimate from cutoff assumptions

This result specializes the abstract energy estimate to a ball and an
annulus, without formalizing derivatives or Sobolev spaces.
-/

open MeasureTheory

/-- Caccioppoli's estimate from an energy identity and cutoff properties. -/
theorem caccioppoli_of_cutoff
    {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) (r t : ℝ)
    (u η : EuclideanSpace ℝ (Fin d) → ℝ)
    (g h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hr : 0 < r) (ht : 0 < t)
    (hA : Integrable (fun y => η y ^ 2 * ‖g y‖ ^ 2) volume)
    (hBmeas : AEStronglyMeasurable
      (fun y => u y ^ 2 * ‖h y‖ ^ 2) volume)
    (hU : IntegrableOn (fun y => u y ^ 2)
      (Set.diff (Metric.ball x ((1 + t) * r)) (Metric.ball x r)) volume)
    (hcross : Integrable
      (fun y => u y * η y * inner ℝ (g y) (h y)) volume)
    (henergy :
      (∫ y, η y ^ 2 * ‖g y‖ ^ 2 ∂volume) =
        -2 * ∫ y, u y * η y * inner ℝ (g y) (h y) ∂volume)
    (heta : ∀ y ∈ Metric.ball x r, η y = 1)
    (hsupport : ∀ᵐ y ∂volume,
      y ∉ Set.diff (Metric.ball x ((1 + t) * r)) (Metric.ball x r) → h y = 0)
    (hbound : ∀ y, ‖h y‖ ≤ 1 / (r * t)) :
    (∫ y in Metric.ball x r, ‖g y‖ ^ 2 ∂volume) ≤
      (4 / (r * t) ^ 2) *
        ∫ y in Set.diff (Metric.ball x ((1 + t) * r)) (Metric.ball x r),
          u y ^ 2 := by
  let B := Metric.ball x r
  let B' := Metric.ball x ((1 + t) * r)
  let A := Set.diff B' B
  let C : ℝ := 1 / (r * t)
  have hrt : 0 < r * t := mul_pos hr ht
  have hC : 0 < C := by dsimp [C]; positivity
  have hBmeasurable : MeasurableSet B := (Metric.isOpen_ball).measurableSet
  have hAmeasurable : MeasurableSet A := by
    dsimp [A, B, B']
    exact Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet
  -- Stage A: the support and norm bounds give an integrable annular majorant.
  have hindicator : Integrable (A.indicator (fun y => u y ^ 2)) volume :=
    (integrable_indicator_iff hAmeasurable).2 hU
  have hmajor : Integrable
      (fun y => C ^ 2 * A.indicator (fun y => u y ^ 2) y) volume :=
    hindicator.const_mul (C ^ 2)
  have hB : Integrable (fun y => u y ^ 2 * ‖h y‖ ^ 2) volume := by
    apply hmajor.mono' hBmeas
    filter_upwards [hsupport] with y hzero
    by_cases hy : y ∈ A
    · have hnormSq : ‖h y‖ ^ 2 ≤ C ^ 2 := by
        have hsum := mul_nonneg (sub_nonneg.mpr (hbound y))
          (add_nonneg (norm_nonneg (h y)) hC.le)
        nlinarith
      have hprod := mul_le_mul_of_nonneg_left hnormSq (sq_nonneg (u y))
      simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ u y ^ 2 * ‖h y‖ ^ 2), Set.indicator_of_mem hy, mul_comm] using hprod
    · have hhy : h y = 0 := hzero hy
      simp [Set.indicator, hy, hhy]
  -- Stage B: invoke the abstract energy estimate as a black box.
  have henergyEstimate := energy_estimate volume u η g h hA hB hcross henergy
  -- Stage C: identify the ball integrand and bound its integral by the global one.
  have hballIntegrand :
      (∫ y in B, ‖g y‖ ^ 2 ∂volume) =
        ∫ y in B, η y ^ 2 * ‖g y‖ ^ 2 ∂volume := by
    apply setIntegral_congr_fun hBmeasurable
    intro y hy
    have hη : η y = 1 := by simpa [B] using heta y hy
    change ‖g y‖ ^ 2 = η y ^ 2 * ‖g y‖ ^ 2
    rw [hη]
    simp
  have hcomplementNonneg :
      0 ≤ ∫ y in Bᶜ, η y ^ 2 * ‖g y‖ ^ 2 ∂volume :=
    integral_nonneg (fun y => by positivity)
  have hsplit := integral_add_compl hBmeasurable hA
  have hballLeGlobal :
      (∫ y in B, ‖g y‖ ^ 2 ∂volume) ≤
        ∫ y, η y ^ 2 * ‖g y‖ ^ 2 ∂volume := by
    rw [hballIntegrand]
    linarith
  -- Stage D: the a.e. support localizes the weighted h integral to the annulus.
  have hlocalized :
      (∫ y, u y ^ 2 * ‖h y‖ ^ 2 ∂volume) =
        ∫ y in A, u y ^ 2 * ‖h y‖ ^ 2 ∂volume := by
    rw [← integral_indicator hAmeasurable]
    apply integral_congr_ae
    filter_upwards [hsupport] with y hzero
    by_cases hy : y ∈ A
    · simp [hy]
    · simp [hy, hzero hy]
  have hpointA (y : EuclideanSpace ℝ (Fin d)) :
      u y ^ 2 * ‖h y‖ ^ 2 ≤ C ^ 2 * u y ^ 2 := by
    have hnormSq : ‖h y‖ ^ 2 ≤ C ^ 2 := by
      have hsum := mul_nonneg (sub_nonneg.mpr (hbound y))
        (add_nonneg (norm_nonneg (h y)) hC.le)
      nlinarith
    calc
      u y ^ 2 * ‖h y‖ ^ 2 ≤ u y ^ 2 * C ^ 2 :=
        mul_le_mul_of_nonneg_left hnormSq (sq_nonneg (u y))
      _ = C ^ 2 * u y ^ 2 := by ring
  have hannulusBound :
      (∫ y in A, u y ^ 2 * ‖h y‖ ^ 2 ∂volume) ≤
        C ^ 2 * ∫ y in A, u y ^ 2 ∂volume := by
    calc
      (∫ y in A, u y ^ 2 * ‖h y‖ ^ 2 ∂volume) ≤
          ∫ y in A, C ^ 2 * u y ^ 2 ∂volume :=
        integral_mono_ae hB.integrableOn (hU.const_mul (C ^ 2))
          (Filter.Eventually.of_forall hpointA)
      _ = C ^ 2 * ∫ y in A, u y ^ 2 ∂volume := by rw [integral_const_mul]
  -- Stage E: combine the bounds and rewrite the cutoff constant.
  calc
    (∫ y in B, ‖g y‖ ^ 2 ∂volume) ≤
        ∫ y, η y ^ 2 * ‖g y‖ ^ 2 ∂volume := hballLeGlobal
    _ ≤ 4 * ∫ y, u y ^ 2 * ‖h y‖ ^ 2 ∂volume := henergyEstimate
    _ = 4 * ∫ y in A, u y ^ 2 * ‖h y‖ ^ 2 ∂volume := by rw [hlocalized]
    _ ≤ 4 * (C ^ 2 * ∫ y in A, u y ^ 2 ∂volume) :=
      mul_le_mul_of_nonneg_left hannulusBound (by norm_num)
    _ = (4 / (r * t) ^ 2) * ∫ y in A, u y ^ 2 ∂volume := by
      dsimp [C]
      ring
