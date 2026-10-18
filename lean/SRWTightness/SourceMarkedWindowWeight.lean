import SRWTightness.SourceTerminalMarkWindow
import SRWTightness.SourceCoarseTerminalWeight
import SRWTightness.SourceGWCoarseProbability
import SRWTightness.SourceGWBandWindows

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- Actual marked window integrals have the normalized one-point weight. -/
theorem source_marked_window_weight_with_margin (J : ℝ) (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)
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
  obtain ⟨A, a, b', hA, hlog, ha, hb, hterminal⟩ := source_terminal_mark_window_integral_with_margin J
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  obtain ⟨g, G, hg, hG, hcoarse⟩ := source_gw_coarse_probability hLower hUpper
  obtain ⟨w, W, hw, hW, hweight⟩ := source_coarse_terminal_weight
  refine ⟨A, (a * g) * w, (b' * Real.exp 2 * G) * W, hA, hlog,
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


/-- Actual marked window integrals have the normalized one-point weight. -/
theorem source_marked_window_weight (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)
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
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ :=
    source_marked_window_weight_with_margin 0 hLower hUpper hReconstruct hBE hGaussian
      hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  exact ⟨A, c, C, hA, hc, hC, hp⟩

end SRWTightness
