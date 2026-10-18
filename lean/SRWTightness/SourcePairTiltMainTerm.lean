import SRWTightness.SourcePairCovarianceBounds
import SRWTightness.PairMarkTiltVariance
import SRWTightness.EquilibriumDiscreteErrorBounds

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Actual signed pair half-variance has the source main term with a uniform error. -/
theorem source_pair_tilt_half_variance_bound (b : Site) (m H a L : ℝ)
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
    (hKM : translateFinset b (diskFinset a) ⊆ M)
 :
    let α := sourceReferenceIntensity m H
    let D := translateFinset b (diskFinset (Real.exp 1 * m + H))
    let μ := markProductLaw D M α k
    let F := normalizedMarkSum M k α (2 / Real.pi) u
    let S := normalizedEquilibriumAverage D M (translateFinset b (diskFinset a)) k α (2 / Real.pi) u
    |covariance ((2 : ℝ) • (F z + F y - S)) ((2 : ℝ) • (F z + F y - S)) μ / 2 -
      (4 * sourceLowerTime m - 2 * sourceEquilibriumTime b m a H)| ≤
      4 * sourcePairVarianceError +
      4 * (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 + Real.log L) +
      1 / (2 / Real.pi) := by
  have ha : 2 ≤ a := by linarith
  have hzinner : Real.sqrt (normSq ((z : Site) - b)) < a - 1 := by
    rw [hz, sub_self]
    norm_num [normSq]
    linarith
  have hyinner : Real.sqrt (normSq ((y : Site) - b)) < a - 1 := by linarith
  have hα := (sourceReferenceIntensity_bounds m H (by linarith) hH hHm).1
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have ht := pair_mark_tilt_half_variance _ M b a ha hKM hMD z y hzinner hyinner
    (sourceReferenceIntensity m H) (2 / Real.pi) u hα hg hu hcap k hk
  obtain ⟨hzv, hyv, hcross⟩ := source_pair_covariance_bounds b m H a L hm hH hHm hma
    M hMD z y hz hρ hlo hhi u hu hcap k hk
  have hne : (translateFinset b (diskFinset a)).Nonempty := by
    refine ⟨b, ?_⟩
    rw [mem_translateFinset_iff, sub_self]
    exact zero_mem_diskFinset a (by linarith)
  have he0 := equilibriumDiscreteError_nonneg
    (translateFinset b (diskFinset (Real.exp 1 * m + H)))
    (translateFinset b (diskFinset a)) (2 / Real.pi) hg.le
  have he1 := equilibriumDiscreteError_uniform_upper
    (translateFinset b (diskFinset (Real.exp 1 * m + H)))
    (translateFinset b (diskFinset a)) (hKM.trans hMD) hne (2 / Real.pi) hg
  dsimp only [sourceEquilibriumTime, equilibriumDiscreteError] at ht hzv hyv hcross he0 he1 ⊢
  rw [ht]
  obtain ⟨hz1, hz2⟩ := abs_le.mp hzv
  obtain ⟨hy1, hy2⟩ := abs_le.mp hyv
  obtain ⟨hc1, hc2⟩ := abs_le.mp hcross
  have hf : 2 * (1 / (2 * (2 / Real.pi))) = 1 / (2 / Real.pi) := by ring
  apply abs_le.mpr
  constructor <;> linarith

end SRWTightness
