import SRWTightness.SourcePairCgfError
import SRWTightness.SourcePairTiltMainTerm
import SRWTightness.SourceTimePowerDecay

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- Uniform O(1) error in the actual source two-site signed cumulant. -/
theorem source_pair_cumulant (L : ℝ) :
    ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (a : ℝ) (M : Finset Site),
      let m := sourceLowerRadius t
      let D := translateFinset b (diskFinset (Real.exp 1 * m + 14))
      let α := sourceReferenceIntensity m 14
      2 * a ≤ m → M ⊆ D → translateFinset b (diskFinset a) ⊆ M →
      α * capacity D M ≤ 1 → ∀ (z y : M), (z : Site) = b →
      1 ≤ Real.sqrt (normSq ((y : Site) - b)) →
      4 * Real.sqrt (normSq ((y : Site) - b)) ≤ a →
      a ≤ L * Real.sqrt (normSq ((y : Site) - b)) →
      ∀ (u : ℝ), t ≤ u → ∀ (k : ℕ), u ^ 2 / 2 = (k : ℝ) →
      let F := normalizedMarkSum M k α (2 / Real.pi) u
      let S := normalizedEquilibriumAverage D M (translateFinset b (diskFinset a)) k α (2 / Real.pi) u
      |cgf ((2 : ℝ) • (F z + F y - S)) (markProductLaw D M α k) 1 -
        (4 * sourceLowerTime m - 2 * sourceEquilibriumTime b m a 14)| ≤
        1 + 4 * sourcePairVarianceError +
        4 * (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 + Real.log L) +
        1 / (2 / Real.pi) := by
  have herr : Tendsto (fun t ↦ sourceCgfErrorConstant 1 6 *
      sourceLowerTime (sourceLowerRadius t) ^ 3 / t) atTop (𝓝 0) := by
    convert (sourceLowerTime_pow_div_t_tendsto_zero 3).const_mul (sourceCgfErrorConstant 1 6) using 1
    · funext t; ring
    · simp
  have herr1 := (tendsto_order.1 herr).2 1 (by norm_num)
  filter_upwards [source_pair_cgf_error 1 (by norm_num), herr1,
    eventually_ge_atTop (sourceScaleThreshold 4)] with t happ he ht
  dsimp only
  intro b a M hma hMD hKM hcap z y hz hρ hlo hhi u hu k hk
  have hconds := sourceScaleThreshold_conditions t 4 (by norm_num) ht
  have hm := hconds.2.2.1
  have hu0 : 0 < u := by linarith [hconds.1]
  have ha : 0 < a := by linarith
  have hne : (translateFinset b (diskFinset a)).Nonempty := by
    refine ⟨b, ?_⟩
    rw [mem_translateFinset_iff, sub_self]
    exact zero_mem_diskFinset a ha
  have hw1 : (∑ x : M, equilibriumWeight
      (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
      (translateFinset b (diskFinset a)) x) = 1 := by
    simpa only [Finset.sum_coe_sort] using equilibriumWeight_sum_over _ M _ hKM (hKM.trans hMD) hne
  have hc := happ b M hMD hcap u (by simpa using hu) k hk z y
    (fun x ↦ equilibriumWeight _ (translateFinset b (diskFinset a)) x)
    (fun x ↦ equilibriumWeight_nonneg _ _ _) hw1
  have hv := source_pair_tilt_half_variance_bound b (sourceLowerRadius t) 14 a L
    (by linarith) (by norm_num) (by linarith) hma M hMD z y hz hρ hlo hhi u hu0 hcap k hk hKM
  dsimp only [normalizedEquilibriumAverage] at hc hv ⊢
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  obtain ⟨hv1, hv2⟩ := abs_le.mp hv
  apply abs_le.mpr
  constructor <;> linarith

end SRWTightness
