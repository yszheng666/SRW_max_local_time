import SRWTightness.ReferenceRestriction

open MeasureTheory

namespace SRWTightness

/-- Enlarging the reference set and restricting the whole visit vector preserves its law. -/
theorem referenceMark_restriction_law (D K L : Finset Site) (hKL : K ⊆ L)
    (hLD : L ⊆ D) (α : ℝ) (hα : 0 ≤ α) (hcapL : α * capacity D L ≤ 1) :
    (referenceMarkLaw D L α).map (restrictMark hKL) = referenceMarkLaw D K α := by
  classical
  have hcapK : α * capacity D K ≤ 1 :=
    (mul_le_mul_of_nonneg_left (capacity_mono_set D K L hKL hLD) hα).trans hcapL
  letI := referenceMarkLaw_isProbabilityMeasure D L α hα hcapL
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcapK
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_restrictMark hKL) hs]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (referenceMarkLaw D L α).real ((restrictMark hKL) ⁻¹' s) =
    (referenceMarkLaw D K α).real s
  have hs' := (measurable_restrictMark hKL) hs
  rw [← integral_indicator_one hs', ← integral_indicator_one hs]
  have hF : Measurable (s.indicator (fun _ : Mark K ↦ (1 : ℝ))) := measurable_const.indicator hs
  have hb : ∀ Y : Mark K, ‖s.indicator (fun _ ↦ (1 : ℝ)) Y‖ ≤ 1 := by
    intro Y
    simp only [Set.indicator]
    split_ifs <;> norm_num
  simpa only [Set.indicator, Set.mem_preimage, Pi.one_apply] using
    referenceMark_restriction_integral D K L hKL hLD α hα hcapL _ hF 1 hb

end SRWTightness
