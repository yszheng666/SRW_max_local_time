import SRWTightness.SourceAnnularTerminalIntegral
import SRWTightness.SourceMarkedReferenceSuccess
import SRWTightness.SourceRootGWHorizon

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- The actual disk-killed SRW record success probability including its independent auxiliary bridges. -/
noncomputable def sourceRecordSuccessProbability (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) : ℝ :=
  let ℓ := sourceRootDepth (Real.exp t) (sourceLowerRadius t)
  let n := ℓ - 1
  let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let F := killedChildRecords (diskFinset (Real.exp t))
    (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
    (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
    (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
      (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n)
  (pathLaw.prod (independentBridgeLaw ℕ)).real
    ((fun p ↦ (F p.1, p.2)) ⁻¹' sourceCoarseTerminalForestEvent t A γ b I z n)

/-- Uniform order exp(-2t) bounds for the actual SRW coarse/terminal record event with auxiliary bridges. -/
theorem source_record_success_probability_with_margin (J : ℝ) (hPotential : PotentialKernelAsymptoticInput)
    (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A c C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
      J + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ∀ b : Site,
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∃ I : ℕ,
        (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)), (z : Site) = b ∧
      ∀ [MeasurableSpace (List (Mark (translateFinset b
        (diskFinset (A * diskEnergyGapRatio ^ I)))))]
        [MeasurableSingletonClass (List (Mark (translateFinset b
          (diskFinset (A * diskEnergyGapRatio ^ I)))))],
      MarkedGWJointInput (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) →
      c * Real.exp (-2 * t) ≤ sourceRecordSuccessProbability t A γ b I z ∧
        sourceRecordSuccessProbability t A γ b I z ≤ C * Real.exp (-2 * t) := by
  obtain ⟨B, W, c₀, T, hB, hW, hc₀, hcompare⟩ := source_annular_terminal_integral hPotential
  obtain ⟨A, c₁, C₁, hA, hlog, hc₁, hC₁, hreference⟩ := source_marked_reference_success_with_margin J
    hLower hUpper hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive
    hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  have herror : ∀ᶠ t : ℝ in atTop, sourceForestQuadraticError B W 8 t < 1 :=
    (tendsto_order.mp (source_forest_quadratic_error_tendsto_zero B W 8)).2 1 (by norm_num)
  refine ⟨A, c₀ * Real.exp (-1) * c₁, Real.exp 1 * C₁, hA, hlog, by positivity, by positivity, ?_⟩
  filter_upwards [hreference, eventually_ge_atTop T, herror] with t href ht herr
  intro b hblo hbhi
  obtain ⟨I, hI, z, hz, hbounds⟩ := href b
  refine ⟨I, hI, z, hz, ?_⟩
  intro instM instMS hjoint
  let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let ℓ := sourceRootDepth (Real.exp t) (sourceLowerRadius t)
  let n := ℓ - 1
  letI : MeasurableSpace (FiniteExcursionRecord (Mark K) n) := ⊤
  letI : MeasurableSingletonClass (FiniteExcursionRecord (Mark K) n) := ⟨fun _ ↦ trivial⟩
  letI : MeasurableSpace (List (FiniteExcursionRecord (Mark K) n)) := ⊤
  letI : MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) n)) := ⟨fun _ ↦ trivial⟩
  have hA4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have hpow : 1 ≤ diskEnergyGapRatio ^ I :=
    one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
  have ha : 1 ≤ A * diskEnergyGapRatio ^ I := by nlinarith
  have hb := hcompare b t A γ I z ht ha ((hI I).mpr le_rfl) hblo hbhi ℓ rfl hjoint hγ
  let Q := ∫ g in sourceGWCoarseBandEvent t n,
    sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation g n)
      ∂geometricGWRecordLaw 1 n
  let E := sourceForestQuadraticError B W 8 t
  change c₀ * Real.exp (-E) * Q ≤ sourceRecordSuccessProbability t A γ b I z ∧
    sourceRecordSuccessProbability t A γ b I z ≤ Real.exp E * Q at hb
  have hQ : c₁ * Real.exp (-2 * t) ≤ Q ∧ Q ≤ C₁ * Real.exp (-2 * t) := by
    dsimp [Q, n, ℓ]
    rw [source_root_gw_horizon]
    exact hbounds
  have hQ0 : 0 ≤ Q := (by positivity : 0 ≤ c₁ * Real.exp (-2 * t)).trans hQ.1
  have hlo : Real.exp (-1) ≤ Real.exp (-E) := Real.exp_le_exp.mpr (by dsimp [E]; linarith)
  have hhi : Real.exp E ≤ Real.exp 1 := Real.exp_le_exp.mpr herr.le
  constructor
  · calc
      _ = (c₀ * Real.exp (-1)) * (c₁ * Real.exp (-2 * t)) := by ring
      _ ≤ (c₀ * Real.exp (-E)) * Q := mul_le_mul
        (mul_le_mul_of_nonneg_left hlo hc₀.le) hQ.1 (by positivity) (by positivity)
      _ ≤ _ := hb.1
  · calc
      _ ≤ Real.exp E * Q := hb.2
      _ ≤ Real.exp 1 * (C₁ * Real.exp (-2 * t)) :=
        mul_le_mul hhi hQ.2 hQ0 (Real.exp_nonneg _)
      _ = _ := by ring


/-- Uniform order exp(-2t) bounds for the actual SRW coarse/terminal record event with auxiliary bridges. -/
theorem source_record_success_probability (hPotential : PotentialKernelAsymptoticInput)
    (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A c C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ∀ b : Site,
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∃ I : ℕ,
        (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)), (z : Site) = b ∧
      ∀ [MeasurableSpace (List (Mark (translateFinset b
        (diskFinset (A * diskEnergyGapRatio ^ I)))))]
        [MeasurableSingletonClass (List (Mark (translateFinset b
          (diskFinset (A * diskEnergyGapRatio ^ I)))))],
      MarkedGWJointInput (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) →
      c * Real.exp (-2 * t) ≤ sourceRecordSuccessProbability t A γ b I z ∧
        sourceRecordSuccessProbability t A γ b I z ≤ C * Real.exp (-2 * t) := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ :=
    source_record_success_probability_with_margin 0 hPotential hLower hUpper hReconstruct hBE hGaussian
      hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  exact ⟨A, c, C, hA, hc, hC, hp⟩

end SRWTightness
