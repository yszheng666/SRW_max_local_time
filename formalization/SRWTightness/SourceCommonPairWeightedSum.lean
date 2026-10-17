import SRWTightness.SourceCommonPairWeightedAtom
import SRWTightness.CommonPairPositiveEndpoints

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

/-- The finite sum of actual GW-weighted positive endpoints has the quadratic counting factor. -/
theorem source_common_pair_weighted_sum
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (t : ℝ) (b w : Site) (j : ℕ) (hbw : b ≠ w) (a : ℝ) (ha : 1 ≤ a)
    (hma : 2 * a ≤ sourceCommonPairInnerRadius t j)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j)
    (K : Finset Site) (hpair : ({b, w} : Finset Site) ⊆ K)
    (hK : K ⊆ translateFinset b (diskFinset a))
    (hlog : diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 ≤
      Real.log (sourceCommonPairInnerRadius t j) - Real.log a)
    (hj : 1 ≤ j) (y : ℝ) (hD : 0 < sourceCommonPairRowScale t b w j)
    (hq : 0 < sourceCommonPairEndpoint t j) (hBy : sourceCommonPairScaledEndpoint t j < y)
    (ht : 1 ≤ t) (hqt : sourceCommonPairEndpoint t j ≤ 4 + 4 * t)
    (hcoeff : 0 ≤ sourceCommonPairIntensity t j *
      twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j)
        (sourceCommonPairScaledEndpoint t j) y /
      (1 - (2 / Real.pi) * sourceCommonPairRowScale t b w j *
        twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j)
          (sourceCommonPairScaledEndpoint t j) y) - 1 / (2 * ((j : ℝ) + 1))) :
    ∑ k ∈ commonPairPositiveEndpoints (sourceCommonPairEndpoint t j),
    (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} *
    (markProductLaw (sourceCommonPairDomain t b j) K (sourceCommonPairIntensity t j) k).real
      {Y | ∀ v : ({b, w} : Finset Site), (2 / Real.pi) * y ^ 2 / 2 ≤
        (sumMarks K k Y ⟨v, hpair v.property⟩ : ℝ)} ≤
      33 * t ^ 2 * Real.exp (1 - (sourceCommonPairEndpoint t j) ^ 2 / (2 * ((j : ℝ) + 1)) -
        (y - sourceCommonPairScaledEndpoint t j) ^ 2 / sourceCommonPairRowScale t b w j +
        (2 / Real.pi) * y ^ 2 *
          (twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j)
            (sourceCommonPairScaledEndpoint t j) y) ^ 2 / 2) := by
  let M := Real.exp (1 - (sourceCommonPairEndpoint t j) ^ 2 / (2 * ((j : ℝ) + 1)) -
        (y - sourceCommonPairScaledEndpoint t j) ^ 2 / sourceCommonPairRowScale t b w j +
        (2 / Real.pi) * y ^ 2 *
          (twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j)
            (sourceCommonPairScaledEndpoint t j) y) ^ 2 / 2)
  have hcard := commonPairPositiveEndpoints_card (sourceCommonPairEndpoint t j) t ht hq.le hqt
  calc
    _ ≤ ∑ k ∈ commonPairPositiveEndpoints (sourceCommonPairEndpoint t j), M := by
      apply Finset.sum_le_sum
      intro k hk
      have hs := commonPairPositiveEndpoints_spec (sourceCommonPairEndpoint t j) k hk
      have hsqrt := Real.sq_sqrt (show 0 ≤ 2 * (k : ℝ) by positivity)
      have huq : Real.sqrt (2 * (k : ℝ)) ≤ sourceCommonPairEndpoint t j := by
        nlinarith [Real.sqrt_nonneg (2 * (k : ℝ))]
      exact source_common_pair_weighted_atom hGW hOcc hRes t b w j hbw a ha hma hm
        K hpair hK hlog hj y (Real.sqrt (2 * (k : ℝ))) hD hq hBy
        (Real.sqrt_nonneg _) huq k hs.1 (by nlinarith) hcoeff
    _ = ((commonPairPositiveEndpoints (sourceCommonPairEndpoint t j)).card : ℝ) * M := by simp
    _ ≤ 33 * t ^ 2 * M := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)

end SRWTightness
