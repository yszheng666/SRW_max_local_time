import SRWTightness.SourceActualFineLeaves
import SRWTightness.SourceFineRootPositive
import SRWTightness.SourceFineContinuationBand
import SRWTightness.SourceContinuationForestEvent
import SRWTightness.SourceWalkSuccessIdentification
import SRWTightness.SourceCandidateExitDomains

open MeasureTheory Filter
namespace SRWTightness

/-- Original continuous local-time success implies the actual remaining forest success event,
with its original root count and unchanged terminal bridge observations. -/
theorem source_fine_success_inclusion (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ) (b : Site) (I : ℕ)
      (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      0 ≤ γ → 1 ≤ A * diskEnergyGapRatio ^ I →
      A * diskEnergyGapRatio ^ I ≤ sourceLowerRadius t / t ^ 6 →
      b ∈ sourceCandidateAnnulus (Real.exp t) → ∀ ν : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ∀ᵐ p ∂pathLaw.prod (independentBridgeLaw ℕ),
      p ∈ sourceLocalTimeSuccessEvent t A γ b I z →
      (sourceActualFineForest t b (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν p.1,
        p.2) ∈ sourceContinuationForestEvent t A γ b I z ν
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        (sourceActualCount t b ν p.1) := by
  filter_upwards [source_walk_success_identification, source_candidate_exit_domains,
    source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hident hD hN htime hm ht0
  intro A γ b I z hγ ha hcut hb ν hν
  let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let ℓ := sourceRootDepth (Real.exp t) (sourceLowerRadius t)
  let n := ℓ - (ν + 1)
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hi : ν + 1 ≤ ℓ := by have hp : 0 < ℓ - 1 := hN.1; omega
  have hℓ : 0 < ℓ := by omega
  have hdepth : ν + n = ℓ - 1 := by dsimp [n]; omega
  have hpaths : ∀ᵐ ω ∂pathLaw,
      (sourceActualFineForest t b K ν ω).flatMap (finiteRecordLeaves n) =
        (sourceActualForest t b K ω).flatMap (finiteRecordLeaves (ℓ - 1)) ∧
      (∀ j ≤ n, geometricGWPopulation (forestPopulationList n
        (sourceActualFineForest t b K ν ω)) j = sourceActualCount t b (ν + j) ω) ∧
      (sourceWalkCoarseBand t b ω → forestPopulationList n
        (sourceActualFineForest t b K ν ω) ∈ sourceContinuationBand t ν n) ∧
      (0 < sourceActualCount t b (ℓ - 1) ω → 0 < sourceActualCount t b ν ω) ∧
      domainExit (diskFinset (Real.exp t)) 0 ω ≠ ⊤ := by
    filter_upwards [source_actual_fine_leaves hF t b K ν hm hi (hD b hb 0),
      source_fine_continuation_population hF t b K ν hm hi (hD b hb 0),
      source_fine_continuation_band hF t b K ν hm hi (hD b hb 0),
      source_fine_root_positive hF t b K ν hm hi (hD b hb 0),
      domainExit_ne_top_ae (diskFinset (Real.exp t)) 0] with ω hl hp hc hr hf
    exact ⟨hl, hp, hc, hr, hf⟩
  have hprod := (Measure.quasiMeasurePreserving_fst
    (μ := pathLaw) (ν := independentBridgeLaw ℕ)).ae hpaths
  filter_upwards [hprod, source_walk_bridge_continuous_ae t A γ b I z hγ] with p hp hevent
  intro hsuccess
  have hbridge : p ∈ sourceLocalTimeBridgeSuccessEvent t A γ b I z :=
    Eq.mpr hevent hsuccess
  have hbgeom := (mem_sourceCandidateAnnulus (Real.exp t) (Real.exp_pos t) b).mp hb
  have hfull := (hident A γ b I z ha hcut hbgeom.1 hbgeom.2 p.1 hp.2.2.2.2 p.2).mpr hbridge
  obtain ⟨r, hr, _, hterm⟩ := hfull
  change sourceActualForest t b K p.1 = [r] at hr
  have hleaf := hp.1
  rw [hr, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hleaf
  have hpop := hp.2.1 n le_rfl
  rw [hdepth] at hpop
  have hrootpop := source_actual_forest_population t b K hℓ p.1 r hr (ℓ - 1) le_rfl
  refine ⟨(hp.2.2.2.1 hsuccess.2.1).ne', hp.2.2.1 hsuccess.2.2.1, ?_⟩
  change ((sourceActualFineForest t b K ν p.1).flatMap (finiteRecordLeaves n), p.2) ∈
    sourceTerminalListBridgeEvent t A γ b I z
      (geometricGWPopulation (forestPopulationList n (sourceActualFineForest t b K ν p.1)) n)
  rw [hleaf, hpop, ← hrootpop]
  exact hterm

end SRWTightness
