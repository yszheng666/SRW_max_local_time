import SRWTightness.SourceCommonPairParameters
import SRWTightness.TwoSiteActualChernoff
import SRWTightness.SourceTerminalCapacityHalf

open MeasureTheory

namespace SRWTightness

/-- Actual common coarse radii discharge the reference intensity and capacity premises. -/
theorem source_common_pair_chernoff
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (t : ℝ) (b w : Site) (j : ℕ) (hbw : b ≠ w) (a : ℝ) (ha : 1 ≤ a)
    (hma : 2 * a ≤ sourceCommonPairInnerRadius t j)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j)
    (hK : ({b, w} : Finset Site) ⊆ translateFinset b (diskFinset a))
    (hlog : diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 ≤
      Real.log (sourceCommonPairInnerRadius t j) - Real.log a)
    (W : ℝ) (hW : 0 ≤ W)
    (hsmall : (2 / Real.pi) * sourceCommonPairRowScale t b w j * W < 1)
    (u y : ℝ) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    (markProductLaw (sourceCommonPairDomain t b j) {b, w} (sourceCommonPairIntensity t j) k).real
      {Y | ∀ v : ({b, w} : Finset Site), (2 / Real.pi) * y ^ 2 / 2 ≤
        (sumMarks {b, w} k Y v : ℝ)} ≤
      Real.exp (-(2 / Real.pi) * y ^ 2 * Real.log (1 + W) +
        sourceCommonPairIntensity t j * u ^ 2 * W /
          (1 - (2 / Real.pi) * sourceCommonPairRowScale t b w j * W)) := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hα := sourceCommonPairIntensity_bounds t j hm
  have hcap : sourceCommonPairIntensity t j *
      capacity (sourceCommonPairDomain t b j) {b, w} ≤ 1 := by
    rw [sourceCommonPairDomain_eq]
    exact (source_terminal_capacity_half b (sourceCommonPairInnerRadius t j) 14 a {b, w}
      ha hma (by norm_num) (by linarith) hK hlog).trans (by norm_num)
  have hAD : ({b, w} : Finset Site) ⊆ sourceCommonPairDomain t b j := by
    rw [sourceCommonPairDomain_eq]
    apply hK.trans
    apply Finset.image_subset_image
    apply diskFinset_mono _ _ (by linarith)
    have hp := sourceCommonPairInnerRadius_pos t j
    nlinarith [Real.exp_one_gt_two]
  have he : (2 / Real.pi) * sourceCommonPairRowScale t b w j =
      twoSiteDiscreteRowMax (sourceCommonPairDomain t b j) b w := by
    unfold sourceCommonPairRowScale
    field_simp
  have hp := two_site_actual_chernoff hOcc hRes (sourceCommonPairDomain t b j) b w hbw
    (hAD (by simp)) (hAD (by simp)) (sourceCommonPairIntensity t j) (2 / Real.pi) W hα.1.le hg
    hcap hW (by simpa only [he] using hsmall) u y k hk
  simpa only [he] using hp

end SRWTightness
