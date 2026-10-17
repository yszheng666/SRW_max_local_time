import SRWTightness.SourceWalkTerminalObservation
import SRWTightness.SourceWalkContinuousSuccess

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- The complete record event is the manuscript local-time event on each finite-exit walk. -/
theorem source_walk_success_identification :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ) (b : Site) (I : ℕ)
      (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      1 ≤ A * diskEnergyGapRatio ^ I →
      A * diskEnergyGapRatio ^ I ≤ sourceLowerRadius t / t ^ 6 →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) →
      Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ (ω : Sample), domainExit (diskFinset (Real.exp t)) 0 ω ≠ ⊤ →
      ∀ β : ℕ → GaussianCoefficientSpace,
      (sourceActualForest t b _ ω, β) ∈ sourceCoarseTerminalForestEvent t A γ b I z
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) ↔
      (ω, β) ∈ sourceLocalTimeBridgeSuccessEvent t A γ b I z := by
  filter_upwards [source_walk_terminal_observation, source_gw_band_terminal_positive,
    source_root_gw_horizon_large] with t hobs hpos hn
  intro A γ b I z ha hcut hblo hbhi ω hfin β
  let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
  have hℓ : 0 < sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by omega
  constructor
  · rintro ⟨r, hr, hband, hterm⟩
    change sourceActualForest t b K ω = [r] at hr
    have hpop := source_actual_forest_population t b K hℓ ω r hr n le_rfl
    have hroot : sourceActualCount t b 0 ω = 1 := by
      rw [← source_actual_forest_length t b K ω, hr]
      rfl
    refine ⟨hroot, ?_, (source_actual_forest_coarse_band t b K hℓ ω r hr).mp hband, ?_⟩
    · rw [← hpop]
      exact hpos n _ hband
    · exact (hobs A γ b I z ha hcut hblo hbhi ω hfin r hr β).mp hterm
  · rintro ⟨hroot, hk, hband, hterm⟩
    have hlen : (sourceActualForest t b K ω).length = 1 := by
      rw [source_actual_forest_length, hroot]
    obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp hlen
    refine ⟨r, hr, (source_actual_forest_coarse_band t b K hℓ ω r hr).mpr hband, ?_⟩
    exact (hobs A γ b I z ha hcut hblo hbhi ω hfin r hr β).mpr hterm

/-- The record probability equals the manuscript continuous local-time success probability. -/
theorem source_walk_success_probability_identification :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ) (b : Site) (I : ℕ)
      (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      0 ≤ γ → 1 ≤ A * diskEnergyGapRatio ^ I →
      A * diskEnergyGapRatio ^ I ≤ sourceLowerRadius t / t ^ 6 →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) →
      Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      sourceRecordSuccessProbability t A γ b I z =
        (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent t A γ b I z) := by
  filter_upwards [source_walk_success_identification] with t ht
  intro A γ b I z hγ ha hcut hblo hbhi
  rw [← source_walk_bridge_continuous_probability t A γ b I z hγ]
  apply congrArg ENNReal.toReal
  apply measure_congr
  have hf := (Measure.quasiMeasurePreserving_fst
    (μ := pathLaw) (ν := independentBridgeLaw ℕ)).ae
      (domainExit_ne_top_ae (diskFinset (Real.exp t)) 0)
  filter_upwards [hf] with p hp
  apply propext
  exact ht A γ b I z ha hcut hblo hbhi p.1 hp p.2

end SRWTightness
