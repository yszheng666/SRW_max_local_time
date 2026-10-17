import SRWTightness.SourceActualAverageVector
import SRWTightness.SourcePairListOriginal
import SRWTightness.SourcePairForestEvent
import SRWTightness.SourcePairCommonThreshold
import SRWTightness.SourcePairPrefixAtNode

open MeasureTheory Filter

namespace SRWTightness

/-- Two successes with their own bridges imply the first site's pair record event almost surely in its bridges. -/
theorem source_pair_success_record_inclusion :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ) (b w : Site) (I J i : ℕ)
      (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
      (hlog : sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A)
      (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
      (hi : i ≤ I)
      (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
      (z' : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ J)))
      (hy : (y : Site) = w) (hz' : (z' : Site) = w)
      (hblo : Real.exp t / 4 ≤ Real.sqrt (normSq b))
      (hbhi : Real.sqrt (normSq b) ≤ Real.exp t / 3),
      ∀ᵐ β ∂independentBridgeLaw ℕ, ∀ (ω : Sample),
      domainExit (diskFinset (Real.exp t)) 0 ω ≠ ⊤ →
      ∀ β' : ℕ → GaussianCoefficientSpace,
      (ω, β) ∈ sourceLocalTimeSuccessEvent t A γ b I z →
      (ω, β') ∈ sourceLocalTimeSuccessEvent t A γ w J z' →
      let h := sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1)
      (sourceActualForest t b _ ω, β) ∈ sourcePairForestEvent t A b I i z y (h ^ γ)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) := by
  filter_upwards [source_actual_terminal_coordinate, source_actual_average_vector,
    source_root_gw_horizon_large, eventually_ge_atTop (sourceScaleThreshold 4)]
    with t hcoord havg hn ht4
  intro A γ b w I J i hA ht hlog hI hi z y z' hy hz' hblo hbhi
  let h := sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1)
  filter_upwards [source_pair_list_original_ae t A b I i hA ht hI z y (h ^ γ)] with β hβ
  intro ω hfin β' hb hw
  let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
  let k := sourceActualCount t b n ω
  have hℓ : 0 < sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by omega
  have hlen : (sourceActualForest t b M ω).length = 1 := by
    rw [source_actual_forest_length]
    exact hb.1
  obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp hlen
  have hpop : geometricGWPopulation (finiteRecordPopulationList n r) n = k :=
    source_actual_forest_population t b M hℓ ω r hr n le_rfl
  refine ⟨r, hr, (source_actual_forest_coarse_band t b M hℓ ω r hr).mpr hb.2.2.1, ?_⟩
  rw [hpop]
  apply (hβ k (finiteRecordLeaves n r)).mpr
  have hA4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have hpow : 1 ≤ diskEnergyGapRatio ^ I := one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
  have ha : 1 ≤ A * diskEnergyGapRatio ^ I := by nlinarith
  have hs := source_pair_common_threshold t A γ b w I J z z' hz' ht4 ω β β' hb hw
  have hc := hcoord A b I ha ((hI I).mpr le_rfl) hblo hbhi ω hfin r hr
  have hv := havg A b I ha ((hI I).mpr le_rfl) hblo hbhi ω hfin r hr z
  have hp := source_success_pair_prefix_at_node t A γ b hA ht hlog I hI z
    (ω, β) hb (⟨I - i, by omega⟩ : Fin (I + 1))
  change _ ∧ _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc z]
    exact hs.1
  · rw [hc y, hy]
    exact hs.2
  · rw [hv]
    exact hp.2
  · rw [hv]
    exact hp.1

end SRWTightness
