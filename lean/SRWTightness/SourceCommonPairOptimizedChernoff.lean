import SRWTightness.SourceCommonPairParameters
import SRWTightness.SourceCommonPairProjectedChernoff
import SRWTightness.TwoSiteOptimizedExponent
import SRWTightness.SourceTerminalCapacityHalf

open MeasureTheory

namespace SRWTightness

/-- The actual common observation law with a single endpoint tilt and its quadratic error. -/
theorem source_common_pair_optimized_chernoff
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (t : ℝ) (b w : Site) (j : ℕ) (hbw : b ≠ w) (a : ℝ) (ha : 1 ≤ a)
    (hma : 2 * a ≤ sourceCommonPairInnerRadius t j)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j)
    (K : Finset Site) (hpair : ({b, w} : Finset Site) ⊆ K)
    (hK : K ⊆ translateFinset b (diskFinset a))
    (hlog : diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 ≤
      Real.log (sourceCommonPairInnerRadius t j) - Real.log a)
    (B y q u : ℝ) (hD : 0 < sourceCommonPairRowScale t b w j)
    (hB : 0 < B) (hBy : B < y) (hu : 0 ≤ u) (huq : u ≤ q)
    (hmatch : sourceCommonPairIntensity t j * q ^ 2 = (2 / Real.pi) * B ^ 2)
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    (markProductLaw (sourceCommonPairDomain t b j) K (sourceCommonPairIntensity t j) k).real
      {Y | ∀ v : ({b, w} : Finset Site), (2 / Real.pi) * y ^ 2 / 2 ≤
        (sumMarks K k Y ⟨v, hpair v.property⟩ : ℝ)} ≤
      Real.exp (-(y - B) ^ 2 / sourceCommonPairRowScale t b w j +
        (2 / Real.pi) * y ^ 2 *
          (twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j) B y) ^ 2 / 2) := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hadm := twoSiteOptimizedTilt_admissible (2 / Real.pi)
    (sourceCommonPairRowScale t b w j) B y hg hD hB hBy
  have hp := source_common_pair_projected_chernoff hOcc hRes t b w j hbw a ha hma hm
    K hpair hK hlog
    (twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j) B y)
    hadm.1.le hadm.2 u y k hk
  apply hp.trans
  apply Real.exp_le_exp.mpr
  exact twoSiteOptimizedTilt_exponent (2 / Real.pi) (sourceCommonPairRowScale t b w j)
    B y (sourceCommonPairIntensity t j) q u hg hD hB hBy
    (sourceCommonPairIntensity_bounds t j hm).1.le hu huq hmatch

end SRWTightness
