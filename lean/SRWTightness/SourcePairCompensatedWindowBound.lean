import SRWTightness.SourcePairResidualWindowBound
import SRWTightness.SourcePairGaussianEndpointResidual
import SRWTightness.SourcePairResidualWindowInclusion
import SRWTightness.PairResidualEventTransfer
import SRWTightness.GaussianTranslation

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The actual compensated comparison Gaussian event has the late-pair window prefactor. -/
theorem source_pair_compensated_window_bound (hKernel : FiniteGaussianBridgeKernelInput)
    (hGaussian : GaussianEndpointResidualInput)
    (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : 4 * sourcePairResidualError + 3 + sourceEquilibriumTimeError +
      sourceLowerTimeError ≤ Real.log A)
    (hsmall : (diskEquilibriumWeightConstant / A) / (2 / Real.pi) ≤ 1 / 2)
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
    let K := pairObservationCovarianceMatrix T (fun _ ↦ 0) V
    let d := sourceLowerTime m
    let v := T last
    ((gaussianMeanCoordinateLaw mean K).prod (independentBridgeLaw ℕ)).real
      (sourcePairWindowEvent t A I i At q f nn mm l) ≤
      32 * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2) * (f + l + 1) / (d * (d - v)) := by
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
  let B := fun j k : Fin (I - i + 1) ↦ min (T j) (T k)
  let Rcov := pairResidualMatrix (V false false) (V true true) (V false true) v
  let e := geometricDiskPointError b A (Real.exp 1 * m + 14)
    diskEnergyGapRatio (2 / Real.pi) (I + 1) (sourcePairAverageIndex I i last)
  let C := 2 * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2)
  let E := (fun p : (PairObservationIndex (I - i + 1) → ℝ) ×
    (ℕ → GaussianCoefficientSpace) ↦ (mean + p.1, p.2)) ⁻¹'
      sourcePairWindowEvent t A I i At q f nn mm l
  let S := finiteGaussianPrefixWindow (sourceObservationTime t A I)
    (I - i + 1) (I + 1) last q (q - f - l - 1 - 2 * e) (q - f - l - 2 * e)
  let a := pairResidualWindowLocation last mean At nn mm
  letI := gaussianCoordinateLaw_isProbabilityMeasure B
  have hR : Rcov.PosDef := source_pair_node_residual_posDef b t A hA ht
    (by linarith) I hI i hi z y hz hρ hlo hhi u hu k hk
  have hden : ∀ x, (gaussianCovarianceDensity Rcov x).toReal ≤ C / (d - v) :=
    source_pair_node_residual_density_upper b t A hA ht
      (by linarith) I hI i hi z y hz hρ hlo hhi u hu k hk
  have hh : 0 < d - v := (source_pair_residual_time b t A sourcePairResidualError hA ht
    (le_max_left _ _) (by linarith) I hI i hi).1
  have hC : 0 ≤ C / (d - v) := div_nonneg (by dsimp [C]; positivity) hh.le
  have hdecomp : gaussianCoordinateLaw K =
      ((gaussianCoordinateLaw B).prod (gaussianCoordinateLaw Rcov)).map
        (pairResidualCoordinates last) := by
    have hp := source_pair_gaussian_endpoint_residual hGaussian b t A hA ht hlog
      I hI i hi z y hz hρ hlo hhi u hu k hk
    dsimp only at hp
    convert hp using 1
    congr 1
    funext p j
    cases j <;> rfl
  have hE0 := sourcePairWindowEvent_measurable t A I i At q f nn mm l
  have hE : MeasurableSet E := hE0.preimage
    ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hS : MeasurableSet S := finiteGaussianPrefixWindow_measurable _ _ _ _ _ _ _
  have ha : Measurable a := pairResidualWindowLocation_measurable _ _ _ _ _
  have hsub := source_pair_residual_window_inclusion b t A hA ht I hI i hi
    z y hz hρ hlo u hu k hk At q f nn mm l
  have hp := pair_residual_event_upper last (gaussianCoordinateLaw B)
    (independentBridgeLaw ℕ) Rcov hR (C / (d - v)) hC hden
    (gaussianCoordinateLaw K) hdecomp S hS E hE a ha hsub
  have he := source_pair_error_bounds b t A hA ht I hI i
  dsimp only at he
  have he0 : 0 ≤ e := he.1 (Sum.inl last)
  have heu : e ≤ 1 / 2 := (Finset.single_le_sum (fun j _ ↦ he.1 j)
    (Finset.mem_univ (Sum.inl last))).trans (he.2.trans hsmall)
  have hb := source_pair_brownian_window_scaled hKernel t A I i hA ht hI
    q f e l hq hf he0 heu hd hv hqu
  change ((gaussianMeanCoordinateLaw mean K).prod (independentBridgeLaw ℕ)).real
    (sourcePairWindowEvent t A I i At q f nn mm l) ≤ _
  rw [gaussianMeanCoordinateLaw_prod_real _ _ _ _ hE0]
  exact hp.trans ((mul_le_mul_of_nonneg_left hb hC).trans_eq (by
    dsimp [C, d, v, T, m, last]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring))

end SRWTightness
