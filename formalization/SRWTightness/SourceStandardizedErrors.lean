import SRWTightness.WhitenedErrorNorm
import SRWTightness.SourceCumulantErrors
import SRWTightness.EntrywiseCovariancePerturbation

open MeasureTheory ProbabilityTheory Filter Matrix WithLp
open scoped Topology MatrixOrder

namespace SRWTightness

/-- The actual source mean and covariance errors after standardization by the target covariance. -/
theorem source_observation_standardized_errors (c B a : ℝ)
    (hc : 0 < c) (hB : 0 < B) (ha : 0 < a) :
    ∀ᶠ t : ℝ in atTop, ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (center : Site) (K : Finset Site),
      let m := sourceLowerRadius t
      let d := sourceLowerTime m
      let D := translateFinset center (diskFinset (Real.exp 1 * m + 14))
      let α := sourceReferenceIntensity m 14
      K ⊆ D → α * capacity D K ≤ 1 → ∀ (u : ℝ), c * t ≤ u →
      ∀ (k : ℕ), u ^ 2 / 2 = (k : ℝ) →
      ∀ (w : ι → K → ℝ), (∀ i z, 0 ≤ w i z) → (∀ i, ∑ z, w i z = 1) →
      ∀ (b : ι → ℝ), (∑ i, |b i|) ≤ B →
        let F := fun i ↦ normalizedWeightedSum K k α (2 / Real.pi) u (w i)
        let μ := markProductLaw D K α k
        let ρ := μ.tilted (fun Y ↦ ∑ l, b l * F l Y)
        let Sigma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) μ
        let Gamma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) ρ
        let A := (CFC.sqrt Sigma)⁻¹
        let v : EuclideanSpace ℝ ι := toLp 2
          (fun i ↦ (∫ Y, F i Y ∂ρ) - ∑ l, b l * Sigma i l)
        (∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Sigma *ᵥ x)) →
        Sigma.PosDef ∧
        ‖toEuclideanCLM (𝕜 := ℝ) A v‖ ≤
          Real.sqrt (Fintype.card ι) * (sourceMeanErrorConstant c B * d ^ 3 / t) /
            Real.sqrt a ∧
        ‖(toLp 2 (fun ij : ι × ι ↦ (A * Gamma * Aᵀ - 1) ij.1 ij.2) :
          EuclideanSpace ℝ (ι × ι))‖ ≤
          Fintype.card ι * (sourceCovarianceErrorConstant c B * d ^ 3 / t) / a := by
  obtain ⟨hM, hmean⟩ := source_observation_mean_error c B hc hB
  obtain ⟨hC, hcov⟩ := source_observation_covariance_error c B hc hB
  filter_upwards [hmean, hcov, eventually_ge_atTop (sourceScaleThreshold 4)] with t hm hv ht
  dsimp only
  intro ι inst instDec center K hKD hcap u hu k hk w hw hw1 b hb hlo
  letI : Fintype ι := inst
  letI : DecidableEq ι := instDec
  let m := sourceLowerRadius t
  let d := sourceLowerTime m
  let D := translateFinset center (diskFinset (Real.exp 1 * m + 14))
  let α := sourceReferenceIntensity m 14
  let F := fun i ↦ normalizedWeightedSum K k α (2 / Real.pi) u (w i)
  let μ := markProductLaw D K α k
  let ρ := μ.tilted (fun Y ↦ ∑ l, b l * F l Y)
  let Sigma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) μ
  let Gamma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) ρ
  let A := (CFC.sqrt Sigma)⁻¹
  let v : EuclideanSpace ℝ ι := toLp 2
    (fun i ↦ (∫ Y, F i Y ∂ρ) - ∑ l, b l * Sigma i l)
  have hd : 0 ≤ d := (sourceLowerTime_square_upper t ht).1
  have ht0 : 0 < t := by
    have hh := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
    linarith
  have hsym : Sigma.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using (covariance_comm (X := F j) (Y := F i) (μ := μ))
  have hSigma : Sigma.PosDef := entrywise_covariance_posDef Sigma Sigma hsym a 0 ha
    (by norm_num) (by intro i j; simp) hlo (by simp; positivity)
  have hvm (i : ι) : |v i| ≤ sourceMeanErrorConstant c B * d ^ 3 / t :=
    hm ι center K hKD hcap u hu k hk w hw hw1 b hb i
  have hvc (i j : ι) : |(Gamma - Sigma) i j| ≤
      sourceCovarianceErrorConstant c B * d ^ 3 / t :=
    hv ι center K hKD hcap u hu k hk w hw hw1 b hb i j
  refine ⟨hSigma, whitened_mean_error_norm_le Sigma hSigma a ha hlo v _ (by positivity) hvm, ?_⟩
  have hnorm := matrix_whitened_error_norm_le Sigma (Gamma - Sigma) hSigma a ha hlo _
    (by positivity) hvc
  have he : A * (Gamma - Sigma) * Aᵀ = A * Gamma * Aᵀ - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, matrix_whitening_covariance Sigma hSigma]
  change ‖(toLp 2 (fun ij : ι × ι ↦ (A * (Gamma - Sigma) * Aᵀ) ij.1 ij.2) :
    EuclideanSpace ℝ (ι × ι))‖ ≤ _ at hnorm
  rw [he] at hnorm
  exact hnorm

end SRWTightness
