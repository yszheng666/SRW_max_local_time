import SRWTightness.SourceCommonPairParameters
import SRWTightness.SourceCommonPairProjectedChernoff
import SRWTightness.SourceCommonPairEndpoint
import SRWTightness.SourceCommonPairOptimizedChernoff
import SRWTightness.SourceTerminalCapacityHalf

open MeasureTheory

namespace SRWTightness

/-- The actual common observation law at the manuscript barrier endpoint and normalization. -/
theorem source_common_pair_endpoint_chernoff
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (t : ℝ) (b w : Site) (j : ℕ) (hbw : b ≠ w) (a : ℝ) (ha : 1 ≤ a)
    (hma : 2 * a ≤ sourceCommonPairInnerRadius t j)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j)
    (K : Finset Site) (hpair : ({b, w} : Finset Site) ⊆ K)
    (hK : K ⊆ translateFinset b (diskFinset a))
    (hlog : diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 ≤
      Real.log (sourceCommonPairInnerRadius t j) - Real.log a)
    (y u : ℝ) (hD : 0 < sourceCommonPairRowScale t b w j)
    (hq : 0 < sourceCommonPairEndpoint t j) (hBy : sourceCommonPairScaledEndpoint t j < y)
    (hu : 0 ≤ u) (huq : u ≤ sourceCommonPairEndpoint t j)
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    (markProductLaw (sourceCommonPairDomain t b j) K (sourceCommonPairIntensity t j) k).real
      {Y | ∀ v : ({b, w} : Finset Site), (2 / Real.pi) * y ^ 2 / 2 ≤
        (sumMarks K k Y ⟨v, hpair v.property⟩ : ℝ)} ≤
      Real.exp (-(y - (sourceCommonPairScaledEndpoint t j)) ^ 2 / sourceCommonPairRowScale t b w j +
        (2 / Real.pi) * y ^ 2 *
          (twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j) (sourceCommonPairScaledEndpoint t j) y) ^ 2 / 2) := by
  exact source_common_pair_optimized_chernoff hOcc hRes t b w j hbw a ha hma hm
    K hpair hK hlog (sourceCommonPairScaledEndpoint t j) y (sourceCommonPairEndpoint t j) u
    hD (sourceCommonPairScaledEndpoint_pos t j hm hq) hBy hu huq
    (sourceCommonPairScaledEndpoint_match t j hm) k hk

end SRWTightness
