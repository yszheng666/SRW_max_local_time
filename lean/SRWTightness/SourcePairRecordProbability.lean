import SRWTightness.SourceAnnularPairIntegral
import SRWTightness.SourcePairReferenceDistanceUpper
import SRWTightness.SourceRootGWHorizon

open MeasureTheory ProbabilityTheory Filter

namespace SRWTightness

/-- The actual disk-killed SRW pair-prefix record probability including its independent auxiliary bridges. -/
noncomputable def sourcePairRecordProbability (t A : ℝ) (b : Site) (I i : ℕ)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (f : ℝ) : ℝ :=
  let ℓ := sourceRootDepth (Real.exp t) (sourceLowerRadius t)
  let n := ℓ - 1
  let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let F := killedChildRecords (diskFinset (Real.exp t))
    (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
    (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
    (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
      (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n)
  (pathLaw.prod (independentBridgeLaw ℕ)).real
    ((fun p ↦ (F p.1, p.2)) ⁻¹' sourcePairForestEvent t A b I i z y f n)

/-- The original SRW pair-prefix record has the late-distance upper bound. -/
theorem source_pair_record_distance_upper
    (hPotential : PotentialKernelAsymptoticInput) (hUpper : GWBarrierUpperInput)
    (hKernel : FiniteGaussianBridgeKernelInput) (hGaussian : GaussianEndpointResidualInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (A : ℝ)
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
    (γ : ℝ)
    (hv : sourceLowerTime (sourceLowerRadius t) / 2 ≤
      sourceObservationTime t A I (I - i + 1))
    (hblo : Real.exp t / 4 ≤ Real.sqrt (normSq b))
    (hbhi : Real.sqrt (normSq b) ≤ Real.exp t / 3),
    ∀ [MeasurableSpace (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSingletonClass (List (Mark (translateFinset b
        (diskFinset (A * diskEnergyGapRatio ^ I)))))],
    MarkedGWJointInput (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) →
    let d := sourceLowerTime (sourceLowerRadius t)
    let h := d - sourceObservationTime t A I (I - i + 1)
    let ρ := Real.sqrt (normSq ((y : Site) - b))
    sourcePairRecordProbability t A b I i z y (h ^ γ) ≤
      (C / ρ ^ 2) * ((1 + h ^ γ) / h) * Real.exp (-2 * t - 2 * h ^ γ) := by
  obtain ⟨B, W, c₀, T, hB, hW, hc₀, hcompare⟩ := source_annular_pair_integral hPotential
  obtain ⟨C, hC, hreference⟩ := source_pair_reference_distance_upper hUpper hKernel hGaussian hBE
  have herror : ∀ᶠ t : ℝ in atTop, sourceForestQuadraticError B W 8 t < 1 :=
    (tendsto_order.mp (source_forest_quadratic_error_tendsto_zero B W 8)).2 1 (by norm_num)
  refine ⟨Real.exp 1 * C, by positivity, ?_⟩
  filter_upwards [hreference, eventually_ge_atTop T, herror] with t href htT herr
  intro b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi γ hv hblo hbhi instM instMS hjoint
  let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let ℓ := sourceRootDepth (Real.exp t) (sourceLowerRadius t)
  let n := ℓ - 1
  let d := sourceLowerTime (sourceLowerRadius t)
  let h := d - sourceObservationTime t A I (I - i + 1)
  let ρ := Real.sqrt (normSq ((y : Site) - b))
  letI : MeasurableSpace (FiniteExcursionRecord (Mark K) n) := ⊤
  letI : MeasurableSingletonClass (FiniteExcursionRecord (Mark K) n) := ⟨fun _ ↦ trivial⟩
  letI : MeasurableSpace (List (FiniteExcursionRecord (Mark K) n)) := ⊤
  letI : MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) n)) := ⟨fun _ ↦ trivial⟩
  have hA4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have hpow : 1 ≤ diskEnergyGapRatio ^ I := one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
  have ha : 1 ≤ A * diskEnergyGapRatio ^ I := by nlinarith
  have hb := hcompare b t A (h ^ γ) I i z y hA ht hI htT ha ((hI I).mpr le_rfl)
    hblo hbhi ℓ rfl hjoint
  let Q := ∫ g in sourceGWCoarseBandEvent t n,
    sourcePairMarkProbability t A b I i z y (geometricGWPopulation g n) (h ^ γ)
      ∂geometricGWRecordLaw 1 n
  let E := sourceForestQuadraticError B W 8 t
  change c₀ * Real.exp (-E) * Q ≤ sourcePairRecordProbability t A b I i z y (h ^ γ) ∧
    sourcePairRecordProbability t A b I i z y (h ^ γ) ≤ Real.exp E * Q at hb
  have hQ : Q ≤ (C / ρ ^ 2) * ((1 + h ^ γ) / h) * Real.exp (-2 * t - 2 * h ^ γ) := by
    dsimp [Q, n, ℓ]
    rw [source_root_gw_horizon]
    exact href b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi γ hv
  have hQ0 : 0 ≤ Q := integral_nonneg (fun _ ↦ measureReal_nonneg)
  have he : Real.exp E ≤ Real.exp 1 := Real.exp_le_exp.mpr herr.le
  calc
    _ ≤ Real.exp E * Q := hb.2
    _ ≤ Real.exp 1 * ((C / ρ ^ 2) * ((1 + h ^ γ) / h) *
        Real.exp (-2 * t - 2 * h ^ γ)) :=
      mul_le_mul he hQ hQ0 (Real.exp_nonneg _)
    _ = _ := by ring

end SRWTightness
