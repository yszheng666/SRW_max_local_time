import SRWTightness.NonnegativeCenteredThirdMoment

open MeasureTheory

namespace SRWTightness

theorem abs_triple_mul_le_cubes (a b c : ℝ) :
    |a * b * c| ≤ |a| ^ 3 + |b| ^ 3 + |c| ^ 3 := by
  have hh (x y z : ℝ) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) (hx : x ≤ z) (hy : y ≤ z) :
      x * y * z ≤ z ^ 3 := by
    calc
      _ ≤ (z * z) * z := mul_le_mul_of_nonneg_right (mul_le_mul hx hy hy0 hz0) hz0
      _ = _ := by ring
  rw [abs_mul, abs_mul]
  rcases le_total |a| |b| with hab |hba
  · rcases le_total |b| |c| with hbc |hcb
    · have h := hh |a| |b| |c| (abs_nonneg _) (abs_nonneg _) (hab.trans hbc) hbc
      linarith [pow_nonneg (abs_nonneg a) 3, pow_nonneg (abs_nonneg b) 3]
    · have h := hh |a| |c| |b| (abs_nonneg _) (abs_nonneg _) hab hcb
      nlinarith [pow_nonneg (abs_nonneg a) 3, pow_nonneg (abs_nonneg c) 3]
  · rcases le_total |a| |c| with hac |hca
    · have h := hh |a| |b| |c| (abs_nonneg _) (abs_nonneg _) hac (hba.trans hac)
      linarith [pow_nonneg (abs_nonneg a) 3, pow_nonneg (abs_nonneg b) 3]
    · have h := hh |b| |c| |a| (abs_nonneg _) (abs_nonneg _) hba hca
      nlinarith [pow_nonneg (abs_nonneg b) 3, pow_nonneg (abs_nonneg c) 3]

/-- Third absolute moments provide integrability and a uniform joint product bound. -/
theorem third_product_moment_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y Z : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hiX : Integrable (fun ω ↦ |X ω| ^ 3) μ)
    (hiY : Integrable (fun ω ↦ |Y ω| ^ 3) μ)
    (hiZ : Integrable (fun ω ↦ |Z ω| ^ 3) μ) :
    Integrable (fun ω ↦ X ω * Y ω * Z ω) μ ∧
    |∫ ω, X ω * Y ω * Z ω ∂μ| ≤
      (∫ ω, |X ω| ^ 3 ∂μ) + (∫ ω, |Y ω| ^ 3 ∂μ) + (∫ ω, |Z ω| ^ 3 ∂μ) := by
  have hiB : Integrable (fun ω ↦ |X ω| ^ 3 + |Y ω| ^ 3 + |Z ω| ^ 3) μ :=
    (hiX.add hiY).add hiZ
  have hm : Measurable (fun ω ↦ X ω * Y ω * Z ω) := by fun_prop
  have hiP : Integrable (fun ω ↦ X ω * Y ω * Z ω) μ := hiB.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs]
      exact abs_triple_mul_le_cubes _ _ _))
  refine ⟨hiP, ?_⟩
  have hh := integral_mono hiP.abs hiB (fun ω ↦ abs_triple_mul_le_cubes (X ω) (Y ω) (Z ω))
  have hiXY : Integrable (fun ω ↦ |X ω| ^ 3 + |Y ω| ^ 3) μ := hiX.add hiY
  rw [integral_add hiXY hiZ, integral_add hiX hiY] at hh
  exact abs_integral_le_integral_abs.trans hh

end SRWTightness
