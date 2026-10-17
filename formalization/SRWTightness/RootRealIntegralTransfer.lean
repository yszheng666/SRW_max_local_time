import SRWTightness.RootGeneratingBound
import SRWTightness.RootFirstMomentReal

open scoped ENNReal
open MeasureTheory
namespace SRWTightness

/-- A finite nonnegative integral bound proves real integrability and the same real bound. -/
theorem wordMark_real_integral_of_bound (μ : Measure WordMark) (f : WordMark → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ Y, 0 ≤ f Y)
    (hb : (∫⁻ Y, ENNReal.ofReal (f Y) ∂μ) ≤ ENNReal.ofReal B) :
    Integrable f μ ∧ (∫ Y, f Y ∂μ) ≤ B := by
  have hnonneg : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall hf
  have hi : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable
      (measurable_of_countable f).aestronglyMeasurable hnonneg).mp
      (ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hb

/-- The source count's real generating function matches its nonnegative formulation pointwise. -/
theorem wordMark_generating_ofReal (L₁ C₁ L₂ C₂ : Finset Site)
    (W : ℝ) (hW : 0 ≤ W) (Y : WordMark) :
    ENNReal.ofReal ((1 + W) ^ (wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y)) =
      (1 + ENNReal.ofReal W) ^ (wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y) := by
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by norm_num) hW]
  simp

end SRWTightness
