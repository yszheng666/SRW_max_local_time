import SRWTightness.CommonPairEndpointSquareError
import SRWTightness.SourceCommonPairEndpointDeficit

namespace SRWTightness

/-- Replacing the normalized endpoint by the source barrier endpoint has a fixed exponent cost. -/
theorem source_common_pair_square_error (t : ℝ) (b w : Site) (j : ℕ)
    (ht : sourceScaleThreshold 4 ≤ t) (htE : 2 * sourceTotalTimeError ≤ t)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j) (hq : 0 ≤ sourceCommonPairEndpoint t j)
    (hd : 1 ≤ sourceTotalTime t - (j : ℝ))
    (hD : sourceTotalTime t - (j : ℝ) ≤ sourceCommonPairRowScale t b w j)
    (hBy : sourceCommonPairScaledEndpoint t j ≤ sourceTerminalHeight t)
    (he : |sourceCommonPairScaledEndpoint t j - sourceCommonPairEndpoint t j| ≤ 1) :
    -(sourceTerminalHeight t - sourceCommonPairScaledEndpoint t j) ^ 2 /
        sourceCommonPairRowScale t b w j ≤
      -(sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 /
        sourceCommonPairRowScale t b w j + 11 := by
  have hB := sourceCommonPairScaledEndpoint_ge t j hm hq
  have hgap := source_common_pair_endpoint_deficit t j ht htE hm hq hd
  exact common_pair_endpoint_square_error (sourceTerminalHeight t)
    (sourceCommonPairScaledEndpoint t j) (sourceCommonPairEndpoint t j)
    (sourceCommonPairRowScale t b w j) (by linarith) (sub_nonneg.mpr hB)
    (abs_le.mp he).2 (sub_nonneg.mpr hBy) (by linarith)

end SRWTightness
