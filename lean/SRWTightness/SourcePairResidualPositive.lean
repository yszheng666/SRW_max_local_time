import SRWTightness.SourcePairCovarianceBounds
import SRWTightness.PairResidualMatrix

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The residual matrix of the two actual mark coordinates is positive definite. -/
theorem source_pair_residual_posDef (b : Site) (m H a L : ℝ)
    (hm : 2 ≤ m) (hH : 0 ≤ H) (hHm : 5 * H ≤ m) (hma : 2 * a ≤ m)
    (M : Finset Site) (hMD : M ⊆ translateFinset b (diskFinset (Real.exp 1 * m + H)))
    (z y : M) (hz : (z : Site) = b)
    (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ a)
    (hhi : a ≤ L * Real.sqrt (normSq ((y : Site) - b)))
    (u : ℝ) (hu : 0 < u)
    (hcap : sourceReferenceIntensity m H *
      capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) M ≤ 1)
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ))
    (hd : 0 < sourceLowerTime m - sourceEquilibriumTime b m a H)
    (hlarge : 4 * max sourcePairVarianceError
      (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 + Real.log L) ≤
        sourceLowerTime m - sourceEquilibriumTime b m a H) :
    let α := sourceReferenceIntensity m H
    let μ := markProductLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) M α k
    let F := normalizedMarkSum M k α (2 / Real.pi) u
    (pairResidualMatrix (covariance (F z) (F z) μ) (covariance (F y) (F y) μ)
      (covariance (F z) (F y) μ) (sourceEquilibriumTime b m a H)).PosDef := by
  obtain ⟨hzv, hyv, hcross⟩ := source_pair_covariance_bounds b m H a L hm hH hHm hma
    M hMD z y hz hρ hlo hhi u hu hcap k hk
  have hC : 0 ≤ max sourcePairVarianceError
      (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 + Real.log L) :=
    (le_trans (abs_nonneg _) hzv).trans (le_max_left _ _)
  exact pairResidualMatrix_posDef _ _ _ _ (sourceLowerTime m) _ hC hd hlarge
    (hzv.trans (le_max_left _ _)) (hyv.trans (le_max_left _ _))
    (hcross.trans (le_max_right _ _))

end SRWTightness
