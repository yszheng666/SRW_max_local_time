import SRWTightness.SourceCommonPairParameters
import SRWTightness.ProjectedMarkChernoff
import SRWTightness.SourceTerminalCapacityHalf

open MeasureTheory

namespace SRWTightness

/-- The source common mark law retains the two-site bound on a larger observation set. -/
theorem source_common_pair_projected_chernoff
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (t : ℝ) (b w : Site) (j : ℕ) (hbw : b ≠ w) (a : ℝ) (ha : 1 ≤ a)
    (hma : 2 * a ≤ sourceCommonPairInnerRadius t j)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j)
    (K : Finset Site) (hpair : ({b, w} : Finset Site) ⊆ K)
    (hK : K ⊆ translateFinset b (diskFinset a))
    (hlog : diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 ≤
      Real.log (sourceCommonPairInnerRadius t j) - Real.log a)
    (W : ℝ) (hW : 0 ≤ W)
    (hsmall : (2 / Real.pi) * sourceCommonPairRowScale t b w j * W < 1)
    (u y : ℝ) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    (markProductLaw (sourceCommonPairDomain t b j) K (sourceCommonPairIntensity t j) k).real
      {Y | ∀ v : ({b, w} : Finset Site), (2 / Real.pi) * y ^ 2 / 2 ≤
        (sumMarks K k Y ⟨v, hpair v.property⟩ : ℝ)} ≤
      Real.exp (-(2 / Real.pi) * y ^ 2 * Real.log (1 + W) +
        sourceCommonPairIntensity t j * u ^ 2 * W /
          (1 - (2 / Real.pi) * sourceCommonPairRowScale t b w j * W)) := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hα := sourceCommonPairIntensity_bounds t j hm
  have hcap : sourceCommonPairIntensity t j *
      capacity (sourceCommonPairDomain t b j) K ≤ 1 := by
    rw [sourceCommonPairDomain_eq]
    exact (source_terminal_capacity_half b (sourceCommonPairInnerRadius t j) 14 a K
      ha hma (by norm_num) (by linarith) hK hlog).trans (by norm_num)
  have hAD : K ⊆ sourceCommonPairDomain t b j := by
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
  have hp := projected_two_site_chernoff hOcc hRes (sourceCommonPairDomain t b j) K b w hbw
    hpair hAD (sourceCommonPairIntensity t j) (2 / Real.pi) W hα.1.le hg
    hcap hW (by simpa only [he] using hsmall) u y k hk
  simpa only [he] using hp

end SRWTightness
