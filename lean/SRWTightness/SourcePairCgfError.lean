import SRWTightness.SourceCgfError
import SRWTightness.PairTiltCgf

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- Uniform source-scale cubic error for the actual signed two-site statistic. -/
theorem source_pair_cgf_error (c : ℝ) (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, ∀ (center : Site) (K : Finset Site),
      let m := sourceLowerRadius t
      let D := translateFinset center (diskFinset (Real.exp 1 * m + 14))
      let α := sourceReferenceIntensity m 14
      K ⊆ D → α * capacity D K ≤ 1 → ∀ (u : ℝ), c * t ≤ u →
      ∀ (k : ℕ), u ^ 2 / 2 = (k : ℝ) → ∀ (z y : K) (w : K → ℝ),
      (∀ x, 0 ≤ w x) → (∑ x, w x = 1) →
      let X := (2 : ℝ) • (normalizedMarkSum K k α (2 / Real.pi) u z +
        normalizedMarkSum K k α (2 / Real.pi) u y - normalizedWeightedSum K k α (2 / Real.pi) u w)
      let μ := markProductLaw D K α k
      |cgf X μ 1 - covariance X X μ / 2| ≤
        sourceCgfErrorConstant c 6 * (sourceLowerTime m) ^ 3 / t := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hS := sourceGreenScaleSlope_pos
  have he : ∀ᶠ t : ℝ in atTop,
      sourceUniformGreenScale (sourceLowerRadius t) / t < c * (2 / Real.pi) / (8 * 6) :=
    (tendsto_order.1 sourceUniformGreenScale_div_t_tendsto_zero).2 _ (by positivity)
  filter_upwards [he, eventually_ge_atTop (sourceScaleThreshold 4)] with t he ht
  dsimp only
  intro center K hKD hcap u hu k hk z y w hw hw1
  let m := sourceLowerRadius t
  let D := translateFinset center (diskFinset (Real.exp 1 * m + 14))
  let α := sourceReferenceIntensity m 14
  let L := sourceUniformGreenScale m
  let d := sourceLowerTime m
  have hconds := sourceScaleThreshold_conditions t 4 (by norm_num) ht
  have ht0 : 0 < t := by linarith [hconds.1]
  have hm : 70 ≤ m := hconds.2.2.1
  have hα := (sourceReferenceIntensity_bounds m 14 (by linarith) (by norm_num) (by linarith)).1
  have hαg : (2 / Real.pi : ℝ) ≤ α :=
    sourceReferenceIntensity_ge_greenConstant m 14 (by linarith) (by norm_num) (by linarith)
  have hαL : α ≤ L :=
    sourceReferenceIntensity_le_uniformGreenScale m 14 (by linarith) (by norm_num) (by linarith)
  have hLG := source_uniform_green_bound center m 14 (by linarith) (by norm_num) (by linarith)
  have hL : 0 < L := by dsimp [L]; linarith [hLG.1]
  have hd : 1 ≤ d := sourceLowerTime_ge_one t ht
  have hLS : L ≤ sourceGreenScaleSlope * d := sourceUniformGreenScale_le_time m hd
  have hu0 : 0 < u := (mul_pos hc ht0).trans_le hu
  have hr : (2 / Real.pi : ℝ) ≤ Real.sqrt (α * (2 / Real.pi)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [mul_le_mul_of_nonneg_right hαg hg.le]
  have hpre : L * (8 * 6) ≤ c * (2 / Real.pi) * t := by
    have hh := (div_le_iff₀ ht0).mp he.le
    have heq : c * (2 / Real.pi) / (8 * 6) * t = c * (2 / Real.pi) * t / (8 * 6) := by ring
    rw [heq] at hh
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * 6)).mp hh
  have hsmall : (6 : ℝ) ≤ (u * Real.sqrt (α * (2 / Real.pi))) / (8 * L) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * L)).mpr
    have huG := mul_le_mul_of_nonneg_right hu hg.le
    have huR := mul_le_mul_of_nonneg_left hr hu0.le
    nlinarith
  have hbound := pair_tilt_cgf_half_variance D K hKD z y w hw hw1 α (2 / Real.pi) u
    hα hg hu0 hcap L hL hαL (fun z ↦ hLG.2 z (hKD z.property)) hsmall k hk
  refine hbound.trans ?_
  have hn : 23592976 * L ^ 3 * (6 : ℝ) ^ 3 ≤
      23592976 * (sourceGreenScaleSlope * d) ^ 3 * 6 ^ 3 := by
    gcongr
  have hden : 12 * (c * t) * (2 / Real.pi) ^ 3 ≤
      12 * u * (Real.sqrt (α * (2 / Real.pi))) ^ 3 := by
    gcongr
  calc
    _ ≤ 23592976 * (sourceGreenScaleSlope * d) ^ 3 * 6 ^ 3 /
        (12 * (c * t) * (2 / Real.pi) ^ 3) :=
      div_le_div₀ (by positivity) hn (by positivity) hden
    _ = _ := by unfold sourceCgfErrorConstant; ring

end SRWTightness
