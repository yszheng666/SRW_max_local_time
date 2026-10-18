import SRWTightness.SourceCommonPairParameters
import SRWTightness.SourceCommonPairProjectedChernoff
import SRWTightness.SourceCommonPairEndpoint
import SRWTightness.GWOneRootExponentialBound
import SRWTightness.TwoSiteGWWeightedExponent
import SRWTightness.SourceTerminalCapacityHalf

open MeasureTheory

namespace SRWTightness

/-- A positive GW endpoint weighted by the actual common two-site mark event. -/
theorem source_common_pair_weighted_atom
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (t : ℝ) (b w : Site) (j : ℕ) (hbw : b ≠ w) (a : ℝ) (ha : 1 ≤ a)
    (hma : 2 * a ≤ sourceCommonPairInnerRadius t j)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j)
    (K : Finset Site) (hpair : ({b, w} : Finset Site) ⊆ K)
    (hK : K ⊆ translateFinset b (diskFinset a))
    (hlog : diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 ≤
      Real.log (sourceCommonPairInnerRadius t j) - Real.log a)
    (hj : 1 ≤ j) (y u : ℝ) (hD : 0 < sourceCommonPairRowScale t b w j)
    (hq : 0 < sourceCommonPairEndpoint t j) (hBy : sourceCommonPairScaledEndpoint t j < y)
    (hu : 0 ≤ u) (huq : u ≤ sourceCommonPairEndpoint t j)
    (k : ℕ) (hkpos : 1 ≤ k) (hk : u ^ 2 / 2 = (k : ℝ))
    (hcoeff : 0 ≤ sourceCommonPairIntensity t j *
      twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j)
        (sourceCommonPairScaledEndpoint t j) y /
      (1 - (2 / Real.pi) * sourceCommonPairRowScale t b w j *
        twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j)
          (sourceCommonPairScaledEndpoint t j) y) - 1 / (2 * ((j : ℝ) + 1))) :
    (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} *
    (markProductLaw (sourceCommonPairDomain t b j) K (sourceCommonPairIntensity t j) k).real
      {Y | ∀ v : ({b, w} : Finset Site), (2 / Real.pi) * y ^ 2 / 2 ≤
        (sumMarks K k Y ⟨v, hpair v.property⟩ : ℝ)} ≤
      Real.exp (1 - (sourceCommonPairEndpoint t j) ^ 2 / (2 * ((j : ℝ) + 1)) -
        (y - sourceCommonPairScaledEndpoint t j) ^ 2 / sourceCommonPairRowScale t b w j +
        (2 / Real.pi) * y ^ 2 *
          (twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j)
            (sourceCommonPairScaledEndpoint t j) y) ^ 2 / 2) := by
  let g : ℝ := 2 / Real.pi
  let D := sourceCommonPairRowScale t b w j
  let B := sourceCommonPairScaledEndpoint t j
  let q := sourceCommonPairEndpoint t j
  let α := sourceCommonPairIntensity t j
  let W := twoSiteOptimizedTilt g D B y
  let F := -g * y ^ 2 * Real.log (1 + W) + α * u ^ 2 * W / (1 - g * D * W)
  have hg : 0 < g := by dsimp [g]; positivity
  have hB := sourceCommonPairScaledEndpoint_pos t j hm hq
  have hadm := twoSiteOptimizedTilt_admissible g D B y hg hD hB hBy
  have hp := source_common_pair_projected_chernoff hOcc hRes t b w j hbw a ha hma hm
    K hpair hK hlog W hadm.1.le hadm.2 u y k hk
  have hmass := geometricGW_one_root_exponential_bound hGW j k hj hkpos
  have hprod := mul_le_mul hmass hp (measureReal_nonneg) (Real.exp_nonneg _)
  have he := twoSiteOptimizedTilt_gw_weighted_exponent g D B y α q u ((j : ℝ) + 1)
    hg hD hB hBy (sourceCommonPairIntensity_bounds t j hm).1.le hu huq
    (sourceCommonPairScaledEndpoint_match t j hm) hcoeff
  calc
    _ ≤ Real.exp (1 - (k : ℝ) / ((j : ℝ) + 1)) * Real.exp F := hprod
    _ = Real.exp (1 + (-u ^ 2 / (2 * ((j : ℝ) + 1)) + F)) := by
      rw [← Real.exp_add, ← hk]
      congr 1
      rw [div_div]
      ring
    _ ≤ Real.exp (1 + (-q ^ 2 / (2 * ((j : ℝ) + 1)) - (y - B) ^ 2 / D +
        g * y ^ 2 * W ^ 2 / 2)) := by
      apply Real.exp_le_exp.mpr
      change 1 + (-u ^ 2 / (2 * ((j : ℝ) + 1)) +
        (-g * y ^ 2 * Real.log (1 + twoSiteOptimizedTilt g D B y) +
          α * u ^ 2 * twoSiteOptimizedTilt g D B y / (1 - g * D * twoSiteOptimizedTilt g D B y))) ≤ _
      linarith only [he]
    _ = _ := by congr 1; dsimp [q, B, D, g, W]; ring

end SRWTightness
