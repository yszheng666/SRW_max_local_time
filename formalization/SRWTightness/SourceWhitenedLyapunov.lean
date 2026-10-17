import SRWTightness.ObservationWhitenedLyapunov
import SRWTightness.SourceTiltedCovariancePositive

open MeasureTheory ProbabilityTheory Filter Matrix WithLp
open scoped Topology MatrixOrder

namespace SRWTightness

noncomputable def sourceLyapunovConstant (c a : ℝ) : ℝ :=
  5898244 * sourceGreenScaleSlope ^ 3 /
    (2 * c * ((2 / Real.pi) * Real.sqrt (a / 2)) ^ 3)

/-- The actual source observation tilt has a uniformly bounded whitened Lyapunov sum. -/
theorem source_observation_whitened_lyapunov (c B P a : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hP : 0 < P) (ha : 0 < a) :
    0 < sourceLyapunovConstant c a ∧
    ∀ᶠ t : ℝ in atTop, ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (center : Site) (K : Finset Site),
      let m := sourceLowerRadius t
      let d := sourceLowerTime m
      let D := translateFinset center (diskFinset (Real.exp 1 * m + 14))
      let α := sourceReferenceIntensity m 14
      K ⊆ D → α * capacity D K ≤ 1 → (Fintype.card ι : ℝ) ≤ P * d →
      ∀ (u : ℝ), c * t ≤ u → ∀ (k : ℕ), u ^ 2 / 2 = (k : ℝ) →
      ∀ (w : ι → K → ℝ), (∀ i z, 0 ≤ w i z) → (∀ i, ∑ z, w i z = 1) →
      ∀ (b : ι → ℝ), (∑ i, |b i|) ≤ B →
        let q := u * Real.sqrt (α * (2 / Real.pi))
        let β := fun z ↦ (∑ i, b i * w i z) / q
        let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
        let F := fun i ↦ normalizedWeightedSum K k α (2 / Real.pi) u (w i)
        let μ := markProductLaw D K α k
        let ρ := μ.tilted (fun Y ↦ ∑ i, b i * F i Y)
        let Sigma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) μ
        let Gamma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) ρ
        let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
        let V : Mark K → EuclideanSpace ℝ ι :=
          fun Y ↦ toLp 2 (fun i ↦ U i Y - ∫ Z, U i Z ∂ν)
        let W := fun Y ↦ q⁻¹ • toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt Gamma)⁻¹) (V Y)
        (∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Sigma *ᵥ x)) →
        (∑ i : Fin k, ∫ Y, ‖W (Y i)‖ ^ 3 ∂ρ) ≤
          sourceLyapunovConstant c a * Fintype.card ι * Real.sqrt (Fintype.card ι) * d ^ 3 / t := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hS := sourceGreenScaleSlope_pos
  constructor
  · unfold sourceLyapunovConstant
    positivity
  have he : ∀ᶠ t : ℝ in atTop,
      sourceUniformGreenScale (sourceLowerRadius t) / t < c * (2 / Real.pi) / (8 * B) :=
    (tendsto_order.1 sourceUniformGreenScale_div_t_tendsto_zero).2 _ (by positivity)
  have hpos := source_observation_tilted_covariance_positive c B P a hc hB hP ha
  filter_upwards [he, hpos, eventually_ge_atTop (sourceScaleThreshold 4)] with t he hp ht
  dsimp only
  intro ι inst instDec center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo
  letI : Fintype ι := inst
  letI : DecidableEq ι := instDec
  let m := sourceLowerRadius t
  let d := sourceLowerTime m
  let D := translateFinset center (diskFinset (Real.exp 1 * m + 14))
  let α := sourceReferenceIntensity m 14
  let L := sourceUniformGreenScale m
  let F := fun i ↦ normalizedWeightedSum K k α (2 / Real.pi) u (w i)
  let μ := markProductLaw D K α k
  let ρ := μ.tilted (fun Y ↦ ∑ i, b i * F i Y)
  let Gamma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) ρ
  have hGamma := hp ι center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo
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
  have hbound := observationFamily_whitened_lyapunov D K hKD α (2 / Real.pi) u
    hα hg hu0 hcap w hw hw1 b L hL hαL (fun z ↦ hLG.2 z (hKD z.property)) hsmall k hk
    Gamma hGamma.2 (a / 2) (by positivity) hGamma.1
  refine hbound.trans ?_
  have hn : 5898244 * L ^ 3 * Fintype.card ι * Real.sqrt (Fintype.card ι) ≤
      5898244 * (sourceGreenScaleSlope * d) ^ 3 * Fintype.card ι *
        Real.sqrt (Fintype.card ι) := by gcongr
  have hden : 2 * (c * t) * ((2 / Real.pi) * Real.sqrt (a / 2)) ^ 3 ≤
      2 * u * (Real.sqrt (α * (2 / Real.pi)) * Real.sqrt (a / 2)) ^ 3 := by gcongr
  calc
    _ ≤ (5898244 * (sourceGreenScaleSlope * d) ^ 3 * Fintype.card ι *
          Real.sqrt (Fintype.card ι)) /
        (2 * (c * t) * ((2 / Real.pi) * Real.sqrt (a / 2)) ^ 3) :=
      div_le_div₀ (by positivity) hn (by positivity) hden
    _ = _ := by unfold sourceLyapunovConstant; ring

end SRWTightness
