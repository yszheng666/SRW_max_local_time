import SRWTightness.ObservationCovarianceCgf
import SRWTightness.SourceGreenScaleComparison

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

noncomputable def sourceCgfErrorConstant (c B : ℝ) : ℝ :=
  23592976 * sourceGreenScaleSlope ^ 3 * B ^ 3 / (12 * c * (2 / Real.pi) ^ 3)

/-- Uniform large-t covariance approximation for every actual source-disk observation family.
The threshold is common to all finite dimensions, centers, valid supports and bounded signed tilts. -/
theorem source_observation_cgf_error (c B : ℝ) (hc : 0 < c) (hB : 0 < B) :
    0 < sourceCgfErrorConstant c B ∧
    ∀ᶠ t : ℝ in atTop, ∀ (ι : Type) [Fintype ι] (center : Site) (K : Finset Site),
      let m := sourceLowerRadius t
      let D := translateFinset center (diskFinset (Real.exp 1 * m + 14))
      let α := sourceReferenceIntensity m 14
      K ⊆ D → α * capacity D K ≤ 1 → ∀ (u : ℝ), c * t ≤ u →
      ∀ (k : ℕ), u ^ 2 / 2 = (k : ℝ) →
      ∀ (w : ι → K → ℝ), (∀ i z, 0 ≤ w i z) → (∀ i, ∑ z, w i z = 1) →
      ∀ (b : ι → ℝ), (∑ i, |b i|) ≤ B →
        let F := fun i ↦ normalizedWeightedSum K k α (2 / Real.pi) u (w i)
        let μ := markProductLaw D K α k
        |cgf (fun Y ↦ ∑ i, b i * F i Y) μ 1 -
          (∑ i, ∑ j, b i * b j * covariance (F i) (F j) μ) / 2| ≤
            sourceCgfErrorConstant c B * (sourceLowerTime m) ^ 3 / t := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hS := sourceGreenScaleSlope_pos
  constructor
  · unfold sourceCgfErrorConstant
    positivity
  have he : ∀ᶠ t : ℝ in atTop,
      sourceUniformGreenScale (sourceLowerRadius t) / t < c * (2 / Real.pi) / (8 * B) :=
    (tendsto_order.1 sourceUniformGreenScale_div_t_tendsto_zero).2 _ (by positivity)
  filter_upwards [he, eventually_ge_atTop (sourceScaleThreshold 4)] with t he ht
  dsimp only
  intro ι inst center K hKD hcap u hu k hk w hw hw1 b hb
  letI : Fintype ι := inst
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
  have hpre : L * (8 * B) ≤ c * (2 / Real.pi) * t := by
    have hh := (div_le_iff₀ ht0).mp he.le
    have heq : c * (2 / Real.pi) / (8 * B) * t = c * (2 / Real.pi) * t / (8 * B) := by ring
    rw [heq] at hh
    exact (le_div_iff₀ (by positivity : 0 < 8 * B)).mp hh
  have hsmall : (∑ i, |b i|) ≤ (u * Real.sqrt (α * (2 / Real.pi))) / (8 * L) := by
    apply hb.trans
    apply (le_div_iff₀ (by positivity : 0 < 8 * L)).mpr
    have huG := mul_le_mul_of_nonneg_right hu hg.le
    have huR := mul_le_mul_of_nonneg_left hr hu0.le
    nlinarith
  have hbound := observationFamily_cgf_covariance_taylor D K hKD α (2 / Real.pi) u
    hα hg hu0 hcap w hw hw1 b L hL hαL (fun z ↦ hLG.2 z (hKD z.property)) hsmall k hk
  refine hbound.trans ?_
  have hn : 23592976 * L ^ 3 * (∑ i, |b i|) ^ 3 ≤
      23592976 * (sourceGreenScaleSlope * d) ^ 3 * B ^ 3 := by
    gcongr
  have hden : 12 * (c * t) * (2 / Real.pi) ^ 3 ≤
      12 * u * (Real.sqrt (α * (2 / Real.pi))) ^ 3 := by
    gcongr
  calc
    _ ≤ 23592976 * (sourceGreenScaleSlope * d) ^ 3 * B ^ 3 /
        (12 * (c * t) * (2 / Real.pi) ^ 3) :=
      div_le_div₀ (by positivity) hn (by positivity) hden
    _ = _ := by unfold sourceCgfErrorConstant; ring

end SRWTightness
