import SRWTightness.SourcePairCompensatedWindowBound
import SRWTightness.SourcePairGaussianDensityUpper
import SRWTightness.GaussianMeanDensityUpper

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The actual uncorrected comparison Gaussian retains a uniform pair-window probability bound. -/
theorem source_pair_gaussian_window_bound (hKernel : FiniteGaussianBridgeKernelInput)
    (hGaussian : GaussianEndpointResidualInput)
    (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : 4 * sourcePairResidualError + 3 + sourceEquilibriumTimeError +
      sourceLowerTimeError ≤ Real.log A)
    (hsmall : (diskEquilibriumWeightConstant / A) / (2 / Real.pi) ≤ 1 / 16)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (hhi : A * diskEnergyGapRatio ^ i ≤
      4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)))
    (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ))
    (At q f : ℝ) (nn mm l : ℕ) (hq : 0 < q) (hf : 0 ≤ f)
    (hd : 0 < sourceLowerTime (sourceLowerRadius t))
    (hv : sourceLowerTime (sourceLowerRadius t) / 2 ≤
      sourceObservationTime t A I (I - i + 1))
    (hqu : q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
 :
    let m := sourceLowerRadius t
    let D := translateFinset b (diskFinset (Real.exp 1 * m + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity m 14
    let μ := markProductLaw D M α k
    let F := normalizedMarkSum M k α (2 / Real.pi) u
    let G := fun a ↦ normalizedWeightedSum M k α (2 / Real.pi) u
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y a)
    let last := Fin.last (I - i)
    let mean := fun j ↦ ∑ l, pairObservationTilt last l * covariance (G j) (G l) μ
    let V := fun c d : Bool ↦ covariance (F (if c then y else z)) (F (if d then y else z)) μ
    let T := fun j : Fin (I - i + 1) ↦ sourceObservationTime t A I (j.val + 1)
    let Sigma : Matrix (PairObservationIndex (I - i + 1)) _ ℝ :=
      fun j l ↦ covariance (G j) (G l) μ
    let d := sourceLowerTime m
    let v := T last
    ((gaussianMeanCoordinateLaw mean Sigma).prod (independentBridgeLaw ℕ)).real
      (sourcePairWindowEvent t A I i At q f nn mm l) ≤
      Real.exp (1 / 2) *
        (32 * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2) * (f + l + 1) / (d * (d - v))) := by
  dsimp only
  let m := sourceLowerRadius t
  let D := translateFinset b (diskFinset (Real.exp 1 * m + 14))
  let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let α := sourceReferenceIntensity m 14
  let μ := markProductLaw D M α k
  let F := normalizedMarkSum M k α (2 / Real.pi) u
  let G := fun a ↦ normalizedWeightedSum M k α (2 / Real.pi) u
    (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y a)
  let last := Fin.last (I - i)
  let mean := fun j ↦ ∑ l, pairObservationTilt last l * covariance (G j) (G l) μ
  let V := fun c d : Bool ↦ covariance (F (if c then y else z)) (F (if d then y else z)) μ
  let T := fun j : Fin (I - i + 1) ↦ sourceObservationTime t A I (j.val + 1)
  let K := pairObservationCovarianceMatrix T (fun _ ↦ 0) V
  let d := sourceLowerTime m
  let v := T last
  let Sigma : Matrix (PairObservationIndex (I - i + 1)) _ ℝ :=
    fun j l ↦ covariance (G j) (G l) μ
  let e := fun j : Fin (I - i + 1) ↦ geometricDiskPointError b A
    (Real.exp 1 * m + 14) diskEnergyGapRatio (2 / Real.pi) (I + 1)
    (sourcePairAverageIndex I i j)
  have hblock : Sigma = pairObservationCovarianceMatrix T e V :=
    source_pair_observation_covariance b t A hA ht I hI i hi z y hz hρ hlo u hu k hk
  have hcomp : Sigma + Matrix.diagonal (pairObservationError e) = K := by
    rw [hblock, pairObservationCovarianceMatrix_compensate]
  have hden := source_pair_gaussian_density_upper b t A hA ht hlog hsmall
    I hI i hi z y hz hρ hlo hhi u hu k hk
  change (Sigma + Matrix.diagonal (pairObservationError e)).PosDef ∧ Sigma.PosDef ∧
    ∀ x, gaussianCovarianceDensity Sigma x ≤
      ENNReal.ofReal (Real.exp (1 / 2)) *
        gaussianCovarianceDensity (Sigma + Matrix.diagonal (pairObservationError e)) x at hden
  rw [hcomp] at hden
  have hp := gaussian_mean_density_event_upper (independentBridgeLaw ℕ)
    Sigma K hden.2.1 hden.1 (Real.exp (1 / 2)) (Real.exp_nonneg _) hden.2.2 mean
    (sourcePairWindowEvent t A I i At q f nn mm l)
    (sourcePairWindowEvent_measurable t A I i At q f nn mm l)
  have hb := source_pair_compensated_window_bound hKernel hGaussian b t A hA ht hlog
    (by linarith) I hI i hi z y hz hρ hlo hhi u hu k hk At q f nn mm l hq hf hd hv hqu
  exact hp.trans (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _))

end SRWTightness
