import SRWTightness.ProjectedOccupation
import SRWTightness.TwoSiteActualChernoff

open MeasureTheory

namespace SRWTightness

/-- Restricting retained coordinates preserves simultaneous count thresholds. -/
theorem projected_mark_all_high_probability
    (D A K : Finset Site) (hAK : A ⊆ K) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (k : ℕ) (level : ℝ) :
    (markProductLaw D K α k).real
      {Y | ∀ v : A, level ≤ (sumMarks K k Y ⟨v, hAK v.property⟩ : ℝ)} =
    (markProductLaw D A α k).real
      {Y | ∀ v : A, level ≤ (sumMarks A k Y v : ℝ)} := by
  have hE : MeasurableSet
      {Y : MarkSamples A k | ∀ v : A, level ≤ (sumMarks A k Y v : ℝ)} :=
    (Set.to_countable _).measurableSet
  exact (markProductLaw_restrict D A K hAK hKD α hα hcap k).measureReal_preimage
    hE.nullMeasurableSet

/-- The two-site Chernoff bound holds inside a larger retained mark set. -/
theorem projected_two_site_chernoff
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (D K : Finset Site) (z w : Site) (hzw : z ≠ w)
    (hAK : ({z, w} : Finset Site) ⊆ K) (hKD : K ⊆ D)
    (α g W : ℝ) (hα : 0 ≤ α) (hg : 0 < g)
    (hcap : α * capacity D K ≤ 1) (hW : 0 ≤ W)
    (hsmall : twoSiteDiscreteRowMax D z w * W < 1)
    (u y : ℝ) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    (markProductLaw D K α k).real
      {Y | ∀ v : ({z, w} : Finset Site), g * y ^ 2 / 2 ≤
        (sumMarks K k Y ⟨v, hAK v.property⟩ : ℝ)} ≤
      Real.exp (-g * y ^ 2 * Real.log (1 + W) +
        α * u ^ 2 * W / (1 - twoSiteDiscreteRowMax D z w * W)) := by
  rw [projected_mark_all_high_probability D {z, w} K hAK hKD α hα hcap]
  have hAD := hAK.trans hKD
  exact two_site_actual_chernoff hOcc hRes D z w hzw (hAD (by simp)) (hAD (by simp))
    α g W hα hg
    ((mul_le_mul_of_nonneg_left (capacity_mono_set D {z, w} K hAK hKD) hα).trans hcap)
    hW hsmall u y k hk

end SRWTightness
