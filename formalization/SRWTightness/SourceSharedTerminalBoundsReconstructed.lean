import SRWTightness.SourceSharedTerminalBounds

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_terminal_mark_window_integral_with_margin_shared_reconstructed (J : ℝ)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (A : ℝ) (hTerminal : SourceTerminalEstimate J A γ) :
    ∃ c C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
      J + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ∀ b : Site, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
        (z : Site) = b ∧ ∀ (L : ℕ) (q : ℝ) (S : Set GeometricGWRecord),
        S ⊆ sourceGWCoarseWindowEvent t L q →
        (∀ r ∈ S, sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L ∈
          Set.Icc (Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
            (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)))) →
        let d := sourceLowerTime (sourceLowerRadius t)
        let μ := geometricGWRecordLaw 1 L
        let P := fun r ↦ sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L)
        (c * (Real.exp (-2 * d - 2 * q) / d)) * μ.real S ≤ ∫ r in S, P r ∂μ ∧
          (∫ r in S, P r ∂μ) ≤
            (C * Real.exp 2 * (Real.exp (-2 * d - 2 * q) / d)) * μ.real S := by
  obtain ⟨c, C, hA, hlog, hc, hC, hp⟩ := hTerminal
  refine ⟨c, C, hA, hlog, hc, hC, ?_⟩
  filter_upwards [hp, eventually_ge_atTop (sourceGaussianThreshold A),
    eventually_ge_atTop (sourceScaleThreshold 4), source_lower_time_eventually_ge 1]
    with t hp htA ht4 hd
  intro b
  obtain ⟨I, hI, z, hz, hb⟩ := hp b
  obtain ⟨J, hJ, hcap⟩ := source_reference_capacity b t A hA htA
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht4).2.2.1
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)).1
  refine ⟨I, hI, z, hz, ?_⟩
  intro L q S hS hband
  apply source_gw_window_integral_bounds t L q c C _ S (by linarith) hc.le hC.le
  · intro r
    exact source_terminal_mark_probability_mem t A γ b I z _ hα.le hcap
  · exact hS
  · intro r hr
    exact hb L r (hband r hr)

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_marked_window_weight_with_margin_shared_reconstructed (J : ℝ) (hLower :
  GWBarrierLowerInput)
  (hUpper : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (A : ℝ) (hTerminal : SourceTerminalEstimate J A γ) :
    ∃ c C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
      J + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ∀ b : Site, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
        (z : Site) = b ∧
        let L := (sourceCoarseGeneration t).toNat
        let μ := geometricGWRecordLaw 1 L
        let P := fun r ↦ sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L)
        Integrable P μ ∧ (∀ r, 0 ≤ P r) ∧ ∀ q : ℝ,
        q ∈ Set.Icc (Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
          (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))) →
        let d := sourceLowerTime (sourceLowerRadius t)
        let E := sourceGWCoarseWindowEvent t L q
        let B := sourceGWCoarseBandEvent t L
        (E ⊆ B → c * (Real.exp (-2 * t) * (1 + q) / d) ≤ ∫ r in E, P r ∂μ) ∧
          (∫ r in B ∩ E, P r ∂μ) ≤ C * (Real.exp (-2 * t) * (1 + q) / d) := by
  obtain ⟨a, b', hA, hlog, ha, hb, hterminal⟩ :=
    source_terminal_mark_window_integral_with_margin_shared_reconstructed J
    hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf A hTerminal
  obtain ⟨g, G, hg, hG, hcoarse⟩ := source_gw_coarse_probability hLower hUpper
  obtain ⟨w, W, hw, hW, hweight⟩ := source_coarse_terminal_weight
  refine ⟨(a * g) * w, (b' * Real.exp 2 * G) * W, hA, hlog,
    by positivity, by positivity, ?_⟩
  filter_upwards [hterminal, hcoarse, hweight,
    eventually_ge_atTop (sourceGaussianThreshold A),
    eventually_ge_atTop (sourceScaleThreshold 4), source_lower_time_eventually_ge 1]
    with t hterminal hcoarse hweight htA ht4 hd
  intro b
  obtain ⟨I, hI, z, hz, hi⟩ := hterminal b
  obtain ⟨J, hJ, hcap⟩ := source_reference_capacity b t A hA htA
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht4).2.2.1
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)).1
  refine ⟨I, hI, z, hz, ?_⟩
  dsimp only
  refine ⟨source_terminal_mark_probability_integrable t A γ b I _ z hα.le hcap,
    (fun r ↦ (source_terminal_mark_probability_mem t A γ b I z _ hα.le hcap).1), ?_⟩
  intro q hq
  let L := (sourceCoarseGeneration t).toNat
  let d := sourceLowerTime (sourceLowerRadius t)
  let E := sourceGWCoarseWindowEvent t L q
  let B := sourceGWCoarseBandEvent t L
  let μ := geometricGWRecordLaw 1 L
  let P := fun r ↦ sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L)
  let wt := Real.exp (-2 * d - 2 * q) / d
  let wg := (1 + q) / (L : ℝ) ^ 2 * Real.exp (-(sourceTerminalRoot t q ^ 2 / (2 * (L : ℝ))))
  let v := Real.exp (-2 * t) * (1 + q) / d
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hwt : 0 ≤ wt := by dsimp [wt]; positivity
  have hgw : g * wg ≤ μ.real E ∧ μ.real E ≤ G * wg := hcoarse q hq.1 hq.2
  have hww : w * v ≤ wg * wt ∧ wg * wt ≤ W * v := hweight q hq.1 hq.2
  change (E ⊆ B → ((a * g) * w) * v ≤ ∫ r in E, P r ∂μ) ∧
    (∫ r in B ∩ E, P r ∂μ) ≤ ((b' * Real.exp 2 * G) * W) * v
  constructor
  · intro hEB
    have hl : (a * wt) * μ.real E ≤ ∫ r in E, P r ∂μ :=
      (hi L q E Set.Subset.rfl (fun r hr ↦ (hEB hr).2)).1
    calc
      _ = (a * g) * (w * v) := by ring
      _ ≤ (a * g) * (wg * wt) := mul_le_mul_of_nonneg_left hww.1 (by positivity)
      _ = (a * wt) * (g * wg) := by ring
      _ ≤ (a * wt) * μ.real E := mul_le_mul_of_nonneg_left hgw.1 (by positivity)
      _ ≤ _ := hl
  · have hu : (∫ r in B ∩ E, P r ∂μ) ≤ (b' * Real.exp 2 * wt) * μ.real (B ∩ E) :=
      (hi L q (B ∩ E) Set.inter_subset_right (fun r hr ↦ hr.1.2)).2
    have hm : μ.real (B ∩ E) ≤ μ.real E := measureReal_mono Set.inter_subset_right
    calc
      _ ≤ (b' * Real.exp 2 * wt) * μ.real (B ∩ E) := hu
      _ ≤ (b' * Real.exp 2 * wt) * (G * wg) :=
        mul_le_mul_of_nonneg_left (hm.trans hgw.2) (by positivity)
      _ = (b' * Real.exp 2 * G) * (wg * wt) := by ring
      _ ≤ (b' * Real.exp 2 * G) * (W * v) :=
        mul_le_mul_of_nonneg_left hww.2 (by positivity)
      _ = _ := by ring

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_marked_reference_success_with_margin_shared_reconstructed (J : ℝ) (hLower :
  GWBarrierLowerInput)
  (hUpper : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (A : ℝ) (hTerminal : SourceTerminalEstimate J A γ) :
    ∃ c C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
      J + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ∀ b : Site, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
        (z : Site) = b ∧
        let L := (sourceCoarseGeneration t).toNat
        let μ := geometricGWRecordLaw 1 L
        let P := fun r ↦ sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L)
        c * Real.exp (-2 * t) ≤ (∫ r in sourceGWCoarseBandEvent t L, P r ∂μ) ∧
          (∫ r in sourceGWCoarseBandEvent t L, P r ∂μ) ≤ C * Real.exp (-2 * t) := by
  obtain ⟨c, C, hA, hlog, hc, hC, hp⟩ :=
    source_marked_window_weight_with_margin_shared_reconstructed J hLower
    hUpper
    hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf A hTerminal
  refine ⟨c / 2, 9 * C, hA, hlog, by positivity, by positivity, ?_⟩
  filter_upwards [hp, source_lower_time_eventually_ge 4] with t ht hd
  intro b
  obtain ⟨I, hI, z, hz, hPi, hP0, hw⟩ := ht b
  refine ⟨I, hI, z, hz, ?_⟩
  exact source_gw_band_integral_scale t _ c C _ hc.le hC.le hd hPi hP0 hw

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_record_success_probability_with_margin_shared_reconstructed (J : ℝ) (hPotential :
  PotentialKernelAsymptoticInput)
    (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (A : ℝ) (hTerminal : SourceTerminalEstimate J A γ) :
    ∃ c C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
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
  obtain ⟨c₁, C₁, hA, hlog, hc₁, hC₁, hreference⟩ :=
    source_marked_reference_success_with_margin_shared_reconstructed J
    hLower hUpper hBE hGaussian hReflection hBridge hReverse hPositive
    hInitial hHit Cm γ hMoment hIncrement hγ hγhalf A hTerminal
  have herror : ∀ᶠ t : ℝ in atTop, sourceForestQuadraticError B W 8 t < 1 :=
    (tendsto_order.mp (source_forest_quadratic_error_tendsto_zero B W 8)).2 1 (by norm_num)
  refine ⟨c₀ * Real.exp (-1) * c₁, Real.exp 1 * C₁, hA, hlog, by positivity, by positivity, ?_⟩
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

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_local_time_success_probability_with_margin_shared_reconstructed (J : ℝ) (hPotential :
  PotentialKernelAsymptoticInput)
    (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (A : ℝ) (hTerminal : SourceTerminalEstimate J A γ) :
    ∃ c C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
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
      c * Real.exp (-2 * t) ≤ (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent t A γ b I z) ∧
        (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent t A γ b I z) ≤ C * Real.exp (-2 * t) := by
  obtain ⟨c, C, hA, hlog, hc, hC, hb⟩ :=
    source_record_success_probability_with_margin_shared_reconstructed J
    hPotential hLower hUpper hBE hGaussian hReflection hBridge hReverse
    hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf A hTerminal
  refine ⟨c, C, hA, hlog, hc, hC, ?_⟩
  filter_upwards [hb, source_walk_success_probability_identification] with t ht heq
  intro b hblo hbhi
  obtain ⟨I, hI, z, hz, hbounds⟩ := ht b hblo hbhi
  refine ⟨I, hI, z, hz, ?_⟩
  intro instM instMS hjoint
  have hA4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have hpow : 1 ≤ diskEnergyGapRatio ^ I :=
    one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
  have ha : 1 ≤ A * diskEnergyGapRatio ^ I := by nlinarith
  rw [← heq A γ b I z hγ ha ((hI I).mpr le_rfl) hblo hbhi]
  exact hbounds hjoint

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_local_time_success_probability_radius_with_margin_shared_reconstructed (J : ℝ)
  (hPotential :
  PotentialKernelAsymptoticInput)
    (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (A : ℝ) (hTerminal : SourceTerminalEstimate J A γ) :
    ∃ c C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
      J + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ R : ℝ in atTop, ∀ b : Site,
      R / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ R / 3 →
      ∃ I : ℕ,
        (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius (Real.log R) / (Real.log R) ^ 6 ↔
          i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)), (z : Site) = b ∧
      ∀ [MeasurableSpace (List (Mark (translateFinset b
        (diskFinset (A * diskEnergyGapRatio ^ I)))))]
        [MeasurableSingletonClass (List (Mark (translateFinset b
          (diskFinset (A * diskEnergyGapRatio ^ I)))))],
      MarkedGWJointInput (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) →
      c * (R ^ 2)⁻¹ ≤ (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent (Real.log R) A γ b I z) ∧
        (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent (Real.log R) A γ b I z) ≤ C * (R ^ 2)⁻¹ := by
  obtain ⟨c, C, hA, hlog, hc, hC, hb⟩ :=
    source_local_time_success_probability_with_margin_shared_reconstructed J
    hPotential hLower hUpper hBE hGaussian hReflection hBridge hReverse
    hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf A hTerminal
  refine ⟨c, C, hA, hlog, hc, hC, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hb, eventually_gt_atTop (0 : ℝ)]
    with R hlarge hR
  have he : Real.exp (-2 * Real.log R) = (R ^ 2)⁻¹ := by
    rw [show -2 * Real.log R = -(Real.log R + Real.log R) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log hR, pow_two]
  simpa only [Real.exp_log hR, he] using hlarge

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_onepoint_with_margin_shared_reconstructed (J : ℝ) (hPotential :
  PotentialKernelAsymptoticInput)
    (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (hLattice : LatticeAnnulusCountInput)
    (hJoint : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWJointInput (Mark K))
    (A : ℝ) (hTerminal : SourceTerminalEstimate J A γ) :
    ∃ c C c₁ C₁ : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
      J + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A ∧
      0 < c ∧ 0 < C ∧ 0 < c₁ ∧ 0 < C₁ ∧ ∀ᶠ R : ℝ in atTop,
      ∃ (I : sourceCandidateAnnulus R → ℕ)
        (z : ∀ b : sourceCandidateAnnulus R,
          translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b))),
      (∀ b : sourceCandidateAnnulus R, (z b : Site) = (b : Site)) ∧
      (∀ (b : sourceCandidateAnnulus R) (i : ℕ),
        A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius (Real.log R) / (Real.log R) ^ 6 ↔ i ≤ I b) ∧
      (∀ b : sourceCandidateAnnulus R,
        c * (R ^ 2)⁻¹ ≤ sourceEnlargedLaw.real
          (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b)) ∧
        sourceEnlargedLaw.real (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b)) ≤
          C * (R ^ 2)⁻¹) ∧
      c₁ ≤ (∫ p, sourceSuccessCount R A γ I z p ∂sourceEnlargedLaw) ∧
        (∫ p, sourceSuccessCount R A γ I z p ∂sourceEnlargedLaw) ≤ C₁ := by
  classical
  obtain ⟨c, C, hA, hlog, hc, hC, hp⟩ :=
    source_local_time_success_probability_radius_with_margin_shared_reconstructed J
    hPotential hLower hUpper hBE hGaussian hReflection hBridge hReverse
    hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf A hTerminal
  obtain ⟨a, B, ha, hB, hm⟩ := source_success_count_bounds hLattice
  refine ⟨c, C, a * c, B * C, hA, hlog, hc, hC, mul_pos ha hc, mul_pos hB hC, ?_⟩
  filter_upwards [hp, hm, Real.tendsto_log_atTop.eventually
    source_local_time_success_nullMeasurable, eventually_gt_atTop (0 : ℝ)]
    with R hp hm hn hR
  have hchoose (b : sourceCandidateAnnulus R) :
      ∃ (i : ℕ) (z : translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ i))),
      (∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤
        sourceLowerRadius (Real.log R) / (Real.log R) ^ 6 ↔ j ≤ i) ∧
      (z : Site) = (b : Site) ∧
      c * (R ^ 2)⁻¹ ≤ (pathLaw.prod (independentBridgeLaw ℕ)).real
        (sourceLocalTimeSuccessEvent (Real.log R) A γ b i z) ∧
      (pathLaw.prod (independentBridgeLaw ℕ)).real
        (sourceLocalTimeSuccessEvent (Real.log R) A γ b i z) ≤ C * (R ^ 2)⁻¹ := by
    have hb := (mem_sourceCandidateAnnulus R hR b).mp b.property
    obtain ⟨i, hi, z, hz, hbnd⟩ := hp b hb.1 hb.2
    let K := translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ i))
    letI : MeasurableSpace (List (Mark K)) := ⊤
    letI : MeasurableSingletonClass (List (Mark K)) := ⟨fun _ ↦ trivial⟩
    exact ⟨i, z, hi, hz, hbnd (hJoint K)⟩
  choose I z hI hz hlo hhi using hchoose
  have hcut (b : sourceCandidateAnnulus R) :
      1 ≤ A * diskEnergyGapRatio ^ I b ∧
      A * diskEnergyGapRatio ^ I b ≤ sourceLowerRadius (Real.log R) / (Real.log R) ^ 6 := by
    have hA4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
      (diskPointGaussianMinimumRadius_ge_base.trans hA)
    have hpow : 1 ≤ diskEnergyGapRatio ^ I b :=
      one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
    exact ⟨by nlinarith, (hI b (I b)).mpr le_rfl⟩
  refine ⟨I, z, hz, hI, ?_, hm A γ c C hγ hc hC I z hcut (fun b ↦ ⟨hlo b, hhi b⟩)⟩
  intro b
  have hb := (mem_sourceCandidateAnnulus R hR b).mp b.property
  have hs := hn A γ b (I b) (z b) hγ (hcut b).1 (hcut b).2
    (by simpa only [Real.exp_log hR] using hb.1)
    (by simpa only [Real.exp_log hR] using hb.2)
  rw [source_site_success_probability (Real.log R) A γ b (I b) (z b) hs]
  exact ⟨hlo b, hhi b⟩

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_continuation_first_upper_shared_reconstructed (hGW : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (J A : ℝ) (hTerminal : SourceTerminalEstimate J A γ) :
    ∃ C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ∀ b : Site, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
        (z : Site) = b ∧ ∀ ν k : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t →
        Real.sqrt (2 * (k : ℝ)) ≤ 4 + sourceBarrierSlope t * ν →
        sourceContinuationProbability t A γ b I z ν k ≤
          C * ((ν : ℝ) + 1) * Real.sqrt (Real.sqrt (2 * (k : ℝ))) / t ^ 2 *
            Real.exp (-2 * sourceLowerTime (sourceLowerRadius t)) *
            Real.exp (-((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) -
              Real.sqrt (2 * (k : ℝ))) ^ 2 /
                (2 * ((sourceCoarseGeneration t : ℝ) - ν)))) := by
  obtain ⟨G, hG, hg⟩ := source_continuation_weighted_band hGW
  obtain ⟨c, C, hA, hlog, hc, hC, hp⟩ := hTerminal
  refine ⟨G * C, hA, by positivity, ?_⟩
  filter_upwards [hg, hp, source_continuation_length_eq,
    eventually_ge_atTop (sourceGaussianThreshold A),
    eventually_ge_atTop (sourceScaleThreshold 4)] with t hg hp hlen htA ht4
  intro b
  obtain ⟨I, hI, z, hz, hb⟩ := hp b
  obtain ⟨J, hJ, hcap⟩ := source_reference_capacity b t A hA htA
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht4).2.2.1
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)).1
  refine ⟨I, hI, z, hz, ?_⟩
  intro ν k hν hx
  by_cases hk : k = 0
  · simp [sourceContinuationProbability, hk]
  · have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    let L := sourceContinuationLength t ν
    have hL := hlen ν hν
    have hLreal : (L : ℝ) = (sourceCoarseGeneration t : ℝ) - ν := by
      dsimp [L]; linarith
    have hh := hg ν L k C
      (fun r ↦ sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L))
      hν hL hk0 hx hC.le
      (fun r ↦ source_terminal_mark_probability_mem t A γ b I z _ hα.le hcap)
      (fun r hr ↦ (hb L r hr.2).2)
    unfold sourceContinuationProbability
    rw [if_neg hk]
    change (∫ r in sourceContinuationBand t ν L,
      sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L)
      ∂geometricGWRecordLaw k L) ≤ _
    rw [hLreal] at hh
    exact hh

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_continuation_upper_bound_shared_reconstructed (hGW : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (J A : ℝ) (hTerminal : SourceTerminalEstimate J A γ) :
    ∃ C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ∀ b : Site, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
        (z : Site) = b ∧ ∀ ν k : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t →
        Real.sqrt (2 * (k : ℝ)) ≤ 4 + sourceBarrierSlope t * ν →
        sourceContinuationProbability t A γ b I z ν k ≤
          C * ((ν : ℝ) + 1) ^ (3 / 2 : ℝ) *
            Real.exp (-2 * t - 2 * ν + 2 * Real.sqrt (2 * (k : ℝ))) := by
  obtain ⟨C, hA, hC, hp⟩ := source_continuation_first_upper_shared_reconstructed hGW
    hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf J A hTerminal
  obtain ⟨D, hD, hd⟩ := source_continuation_decay
  refine ⟨C * D, hA, by positivity, ?_⟩
  filter_upwards [hp, hd] with t hp hd
  intro b
  obtain ⟨I, hI, z, hz, hb⟩ := hp b
  refine ⟨I, hI, z, hz, ?_⟩
  intro ν k hν hx
  let x := Real.sqrt (2 * (k : ℝ))
  let F := ((ν : ℝ) + 1) * Real.sqrt x / t ^ 2 *
    Real.exp (-2 * sourceLowerTime (sourceLowerRadius t)) *
    Real.exp (-((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - x) ^ 2 /
      (2 * ((sourceCoarseGeneration t : ℝ) - ν))))
  have hfirst : sourceContinuationProbability t A γ b I z ν k ≤ C * F := by
    convert hb ν k hν hx using 1 <;> dsimp [F, x] <;> ring
  have hdecay : F ≤ D * ((ν : ℝ) + 1) ^ (3 / 2 : ℝ) *
      Real.exp (-2 * t - 2 * ν + 2 * x) := hd ν x hν (Real.sqrt_nonneg _) hx
  calc
    _ ≤ C * F := hfirst
    _ ≤ C * (D * ((ν : ℝ) + 1) ^ (3 / 2 : ℝ) *
        Real.exp (-2 * t - 2 * ν + 2 * x)) := mul_le_mul_of_nonneg_left hdecay hC.le
    _ = _ := by ring

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_continuation_radius_upper_bound_shared_reconstructed (hGW : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (J A : ℝ) (hTerminal : SourceTerminalEstimate J A γ) :
    ∃ C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ∀ b : Site, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
        (z : Site) = b ∧ ∀ ν k : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t →
        Real.sqrt (2 * (k : ℝ)) ≤ 4 + sourceBarrierSlope t * ν →
        sourceContinuationProbability t A γ b I z ν k ≤
          C * ((ν : ℝ) + 1) ^ (3 / 2 : ℝ) / (Real.exp t) ^ 2 *
            Real.exp (-2 * ν + 2 * Real.sqrt (2 * (k : ℝ))) := by
  obtain ⟨C, hA, hC, hp⟩ := source_continuation_upper_bound_shared_reconstructed hGW
    hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf J A hTerminal
  refine ⟨C, hA, hC, ?_⟩
  filter_upwards [hp] with t hp
  intro b
  obtain ⟨I, hI, z, hz, hb⟩ := hp b
  refine ⟨I, hI, z, hz, ?_⟩
  intro ν k hν hx
  have hh := hb ν k hν hx
  rw [continuation_radius_decay_identity] at hh
  convert hh using 1 <;> ring

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_continuation_pair_radius_upper_bound_shared_reconstructed (hGW : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (J A : ℝ) (hTerminal : SourceTerminalEstimate J A γ) :
    ∃ C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, ∃ I₀ I₁ : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₀) ∧
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₁) ∧
      ∃ (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
        (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))),
      (z₀ : Site) = b ∧ (z₁ : Site) = w ∧
      ∀ ν k l : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t →
      k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
      sourceContinuationProbability t A γ b I₀ z₀ ν k *
        sourceContinuationProbability t A γ w I₁ z₁ ν l ≤
      C * ((ν : ℝ) + 1) ^ 3 / (Real.exp t) ^ 4 * Real.exp (-4 * ν) *
        Real.exp (2 * Real.sqrt (2 * (k : ℝ)) + 2 * Real.sqrt (2 * (l : ℝ))) := by
  obtain ⟨C, hA, hC, ht⟩ := source_continuation_radius_upper_bound_shared_reconstructed hGW
    hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf J A hTerminal
  refine ⟨C ^ 2, hA, pow_pos hC 2, ?_⟩
  filter_upwards [ht, source_deficit_large_conditions] with t ht hlarge
  intro b w
  obtain ⟨I₀, hI₀, z₀, hz₀, hb⟩ := ht b
  obtain ⟨I₁, hI₁, z₁, hz₁, hw⟩ := ht w
  refine ⟨I₀, I₁, hI₀, hI₁, z₀, z₁, hz₀, hz₁, ?_⟩
  intro ν k l hν hk hl
  have hθ := (sourceBarrierSlope_bounds t hlarge.1 hlarge.2.1).1
  exact continuation_pair_product_bound C (ν : ℝ) t _ _ _ _ hC.le (Nat.cast_nonneg _)
    (source_continuation_probability_nonneg t A γ w I₁ z₁ ν l)
    (hb ν k hν (source_early_root_height_of_cap t ν k hθ hk))
    (hw ν l hν (source_early_root_height_of_cap t ν l hθ hl))

end SRWTightness
