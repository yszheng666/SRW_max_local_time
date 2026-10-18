import SRWTightness.DensityEventLower

open MeasureTheory
namespace SRWTightness

/-- A nonnegative density on a null measurable restriction gives its ordinary event integral. -/
theorem restricted_density_event_real {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (hA : NullMeasurableSet A μ)
    (w : Ω → ℝ) (hw : Measurable w) (hn : ∀ ω ∈ A, 0 ≤ w ω)
    (B : Set Ω) (hB : MeasurableSet B) :
    ((μ.restrict A).withDensity (fun ω ↦ ENNReal.ofReal (w ω))).real B =
      ∫ ω in A ∩ B, w ω ∂μ := by
  have he := setIntegral_withDensity_eq_setIntegral_toReal_smul
    (μ := μ.restrict A) hw.ennreal_ofReal
    (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top)) (fun _ ↦ (1 : ℝ)) hB
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at he
  change _ = _ at he
  calc
    _ = ∫ ω in B, (ENNReal.ofReal (w ω)).toReal ∂μ.restrict A := he
    _ = ∫ ω in B, w ω ∂μ.restrict A := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_restrict_mem₀ hA)] with ω hω
      exact ENNReal.toReal_ofReal (hn ω hω)
    _ = _ := by rw [Measure.restrict_restrict hB, Set.inter_comm]

end SRWTightness
