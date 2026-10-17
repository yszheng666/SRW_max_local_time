import SRWTightness.ReferenceWeightedMoments
import SRWTightness.EquilibriumWeightBilinear

open MeasureTheory

namespace SRWTightness

/-- Exponential and sixth moments for the actual equilibrium average within a common mark domain. -/
theorem referenceMark_equilibrium_moments (D M K : Finset Site) (hKM : K ⊆ M)
    (hMD : M ⊆ D) (hne : K.Nonempty) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D M ≤ 1) (L : ℝ) (hL : 0 < L)
    (hG : ∀ z : M, killedGreen D z z ≤ L) :
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 / (4 * L) →
      Integrable (fun Y : Mark M ↦ Real.exp (s * ∑ z : M, equilibriumWeight D K z * (Y z : ℝ)))
        (referenceMarkLaw D M α) ∧
      (∫ Y : Mark M, Real.exp (s * ∑ z : M, equilibriumWeight D K z * (Y z : ℝ))
        ∂referenceMarkLaw D M α) ≤ 1 + 4 * α * s) ∧
    Integrable (fun Y : Mark M ↦ (∑ z : M, equilibriumWeight D K z * (Y z : ℝ)) ^ 6)
      (referenceMarkLaw D M α) ∧
    (∫ Y : Mark M, (∑ z : M, equilibriumWeight D K z * (Y z : ℝ)) ^ 6
      ∂referenceMarkLaw D M α) ≤ 2949120 * α * L ^ 5 := by
  have hw : (∑ z : M, equilibriumWeight D K z) = 1 := by
    simpa only [Finset.sum_coe_sort] using
      equilibriumWeight_sum_over D M K hKM (hKM.trans hMD) hne
  refine ⟨?_, referenceMark_weighted_sixth_moment D M hMD α hα hcap
    (fun z ↦ equilibriumWeight D K z) (fun z ↦ equilibriumWeight_nonneg D K z) hw L hL hG⟩
  intro s hs hsmall
  exact referenceMark_weighted_exponential_bound D M hMD α hα hcap
    (fun z ↦ equilibriumWeight D K z) (fun z ↦ equilibriumWeight_nonneg D K z) hw L hL hG s hs hsmall

end SRWTightness
