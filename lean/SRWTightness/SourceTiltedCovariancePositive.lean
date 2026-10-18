import SRWTightness.EntrywiseCovariancePerturbation
import SRWTightness.SourceCovarianceError
import SRWTightness.SourceTimePowerDecay

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology

namespace SRWTightness

/-- Under the manuscript dimension bound, small physical tilts preserve a fixed covariance gap. -/
theorem source_observation_tilted_covariance_positive (c B P a : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hP : 0 < P) (ha : 0 < a) :
    ∀ᶠ t : ℝ in atTop, ∀ (ι : Type) [Fintype ι] (center : Site) (K : Finset Site),
      let m := sourceLowerRadius t
      let d := sourceLowerTime m
      let D := translateFinset center (diskFinset (Real.exp 1 * m + 14))
      let α := sourceReferenceIntensity m 14
      K ⊆ D → α * capacity D K ≤ 1 → (Fintype.card ι : ℝ) ≤ P * d →
      ∀ (u : ℝ), c * t ≤ u → ∀ (k : ℕ), u ^ 2 / 2 = (k : ℝ) →
      ∀ (w : ι → K → ℝ), (∀ i z, 0 ≤ w i z) → (∀ i, ∑ z, w i z = 1) →
      ∀ (b : ι → ℝ), (∑ i, |b i|) ≤ B →
        let F := fun i ↦ normalizedWeightedSum K k α (2 / Real.pi) u (w i)
        let μ := markProductLaw D K α k
        let Sigma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) μ
        let Gamma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j)
          (μ.tilted (fun Y ↦ ∑ l, b l * F l Y))
        (∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Sigma *ᵥ x)) →
        (∀ x : ι → ℝ, (a / 2) * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Gamma *ᵥ x)) ∧ Gamma.PosDef := by
  classical
  obtain ⟨hC, hcov⟩ := source_observation_covariance_error c B hc hB
  let C := sourceCovarianceErrorConstant c B
  have hlim : Tendsto (fun t : ℝ ↦ C * P *
      (sourceLowerTime (sourceLowerRadius t) ^ 4 / t)) atTop (𝓝 0) := by
    simpa using (sourceLowerTime_pow_div_t_tendsto_zero 4).const_mul (C * P)
  have hsmall := (tendsto_order.1 hlim).2 (a / 2) (by positivity)
  filter_upwards [hcov, hsmall, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (sourceScaleThreshold 4)] with t hcov hs ht htlarge
  dsimp only
  intro ι inst center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo
  letI : Fintype ι := inst
  let m := sourceLowerRadius t
  let d := sourceLowerTime m
  let D := translateFinset center (diskFinset (Real.exp 1 * m + 14))
  let α := sourceReferenceIntensity m 14
  let F := fun i ↦ normalizedWeightedSum K k α (2 / Real.pi) u (w i)
  let μ := markProductLaw D K α k
  let Sigma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) μ
  let Gamma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j)
    (μ.tilted (fun Y ↦ ∑ l, b l * F l Y))
  let ε := C * d ^ 3 / t
  have hd : 0 ≤ d := (sourceLowerTime_square_upper t htlarge).1
  have hε : 0 ≤ ε := div_nonneg (mul_nonneg hC.le (pow_nonneg hd _)) ht.le
  have hentry (i j : ι) : |Gamma i j - Sigma i j| ≤ ε :=
    hcov ι center K hKD hcap u hu k hk w hw hw1 b hb i j
  have hsize : ε * Fintype.card ι ≤ a / 2 := by
    calc
      _ ≤ ε * (P * d) := mul_le_mul_of_nonneg_left hdim hε
      _ = C * P * (d ^ 4 / t) := by dsimp [ε]; ring
      _ ≤ _ := hs.le
  have hGamma : Gamma.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using
      (covariance_comm (X := F j) (Y := F i)
        (μ := μ.tilted (fun Y ↦ ∑ l, b l * F l Y)))
  exact ⟨entrywise_covariance_lower Gamma Sigma a ε hε hentry hlo hsize,
    entrywise_covariance_posDef Gamma Sigma hGamma a ε ha hε hentry hlo hsize⟩

end SRWTightness
