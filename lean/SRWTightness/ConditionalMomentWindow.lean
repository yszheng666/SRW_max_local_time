import SRWTightness.ConditionalNonnegativeMoment
import SRWTightness.ConditionalSubsetLaw

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- A positive lower bound for the conditioning probability controls every nonnegative moment. -/
theorem conditional_nonnegative_moment_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Set Ω) (f : Ω → ℝ)
    (c : ℝ) (hc : 0 < c) (hs : c ≤ μ.real s)
    (hf : Integrable f μ) (hn : ∀ ω, 0 ≤ f ω) :
    Integrable f (ProbabilityTheory.cond μ s) ∧
      (∫ ω, f ω ∂ProbabilityTheory.cond μ s) ≤ c⁻¹ * ∫ ω, f ω ∂μ := by
  have hpos : 0 < μ.real s := hc.trans_le hs
  have hne : μ s ≠ 0 := by
    intro h
    simp [Measure.real, h] at hpos
  have hrestrict := hf.mono_measure (Measure.restrict_le_self (μ := μ) (s := s))
  constructor
  · exact hrestrict.smul_measure (ENNReal.inv_ne_top.mpr hne)
  · rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
    change (μ.real s)⁻¹ * (∫ ω, f ω ∂μ.restrict s) ≤ _
    have hi := integral_mono_measure (Measure.restrict_le_self (μ := μ) (s := s))
      (Filter.Eventually.of_forall hn) hf
    calc
      _ ≤ c⁻¹ * (∫ ω, f ω ∂μ.restrict s) :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hc hs) (integral_nonneg hn)
      _ ≤ _ := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hc.le)

/-- Adding a subevent with uniformly positive conditional probability preserves moment control. -/
theorem conditional_nonnegative_moment_subwindow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s t : Set Ω) (f : Ω → ℝ)
    (hs : NullMeasurableSet s μ) (hs0 : μ s ≠ 0) (hts : t ⊆ s)
    (c : ℝ) (hc : 0 < c) (ht : c ≤ (ProbabilityTheory.cond μ s).real t)
    (hf : Integrable f (ProbabilityTheory.cond μ s)) (hn : ∀ ω, 0 ≤ f ω) :
    Integrable f (ProbabilityTheory.cond μ t) ∧
      (∫ ω, f ω ∂ProbabilityTheory.cond μ t) ≤
        c⁻¹ * ∫ ω, f ω ∂ProbabilityTheory.cond μ s := by
  have hh := conditional_nonnegative_moment_lower (ProbabilityTheory.cond μ s) t f c hc ht hf hn
  rw [conditional_subset_law μ s t hs hs0 hts] at hh
  exact hh

/-- A relative event-probability lower bound transfers a nonnegative conditional moment. -/
theorem conditional_nonnegative_moment_relative {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s t : Set Ω) (f : Ω → ℝ)
    (hs : NullMeasurableSet s μ) (hspos : 0 < μ.real s) (hts : t ⊆ s)
    (c : ℝ) (hc : 0 < c) (ht : c * μ.real s ≤ μ.real t)
    (hf : Integrable f (ProbabilityTheory.cond μ s)) (hn : ∀ ω, 0 ≤ f ω) :
    Integrable f (ProbabilityTheory.cond μ t) ∧
      (∫ ω, f ω ∂ProbabilityTheory.cond μ t) ≤
        c⁻¹ * ∫ ω, f ω ∂ProbabilityTheory.cond μ s := by
  have hs0 : μ s ≠ 0 := by
    intro h
    simp [Measure.real, h] at hspos
  have he := conditional_real_mul_of_subset μ s t hs hspos hts
  have hcond : c ≤ (ProbabilityTheory.cond μ s).real t := by
    apply (mul_le_mul_iff_left₀ hspos).mp
    simpa only [mul_comm] using (ht.trans_eq he.symm)
  exact conditional_nonnegative_moment_subwindow μ s t f hs hs0 hts c hc hcond hf hn

end SRWTightness
