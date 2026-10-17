import SRWTightness.SourceSeedFromMoments
import SRWTightness.SecondMomentRatio

open MeasureTheory Filter

namespace SRWTightness

/-- The actual canonical success count has the complete positive-probability ratio chain. -/
theorem source_canonical_ratio (A : ℝ) (hA : 1 ≤ A)
    (hMoments : SourceCanonicalMomentEstimate A)
    (hAllForest : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWForestJointInput (Mark K))
    (hAllMix : ∀ (α β : Type) [MeasurableSpace α] [MeasurableSpace β]
      [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable α] [Countable β]
      [MeasurableSpace (List α)] [MeasurableSpace (List β)]
      [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)],
      OrderedForestMixtureInput α β) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      let W := sourceCenteredSuccessCount t A (2 / 5) I
      0 < (∫ p, W p ∂sourceEnlargedLaw) ∧
      0 < (∫ p, W p ^ 2 ∂sourceEnlargedLaw) ∧
      c ^ 2 / D ≤ (∫ p, W p ∂sourceEnlargedLaw) ^ 2 /
        (∫ p, W p ^ 2 ∂sourceEnlargedLaw) ∧
      (∫ p, W p ∂sourceEnlargedLaw) ^ 2 / (∫ p, W p ^ 2 ∂sourceEnlargedLaw) ≤
        sourceEnlargedLaw.real {p | 0 < W p} ∧
      sourceEnlargedLaw.real {p | 0 < W p} ≤
        pathLaw.real {ω | diskCenter (Real.exp t) ≤ Real.sqrt (diskMax (Real.exp t) ω)} := by
  obtain ⟨c, C, D, hc, hC, hD, hm⟩ := hMoments
  refine ⟨c, D, hc, hD, ?_⟩
  filter_upwards [hm, source_canonical_count_integrable,
    eventually_ge_atTop (sourceScaleThreshold 4)] with t hm hi ht
  obtain ⟨I, hI, hlo, hhi, hsecond⟩ := hm
  letI : ∀ j : ℕ, MeasurableSpace (FiniteExcursionRecord WordMark j) := fun _ ↦ ⊤
  letI : ∀ j : ℕ, MeasurableSingletonClass (FiniteExcursionRecord WordMark j) :=
    fun _ ↦ ⟨fun _ ↦ trivial⟩
  letI : ∀ j : ℕ, MeasurableSpace (List (FiniteExcursionRecord WordMark j)) := fun _ ↦ ⊤
  letI : ∀ j : ℕ, MeasurableSingletonClass (List (FiniteExcursionRecord WordMark j)) :=
    fun _ ↦ ⟨fun _ ↦ trivial⟩
  letI : ∀ b : Site, MeasurableSpace
      (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))) := fun _ ↦ ⊤
  letI : ∀ b : Site, MeasurableSingletonClass
      (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))) :=
    fun _ ↦ ⟨fun _ ↦ trivial⟩
  letI : ∀ (b : Site) (ν : ℕ), MeasurableSpace
      (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν) :=
    fun _ _ ↦ ⊤
  letI : ∀ (b : Site) (ν : ℕ), MeasurableSingletonClass
      (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν) :=
    fun _ _ ↦ ⟨fun _ ↦ trivial⟩
  letI : ∀ (b : Site) (ν : ℕ), MeasurableSpace (List
      (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)) :=
    fun _ _ ↦ ⊤
  letI : ∀ (b : Site) (ν : ℕ), MeasurableSingletonClass (List
      (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)) :=
    fun _ _ ↦ ⟨fun _ ↦ trivial⟩
  have hs := hsecond
    (fun b _ ↦ hAllForest (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
    (fun b w ν _ _ _ ↦ by
      letI := finiteExcursionRecord_countable
        (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
      letI := finiteExcursionRecord_countable
        (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))))
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
      exact hAllMix _ _)
  obtain ⟨hi₁, hi₂⟩ := hi A (2 / 5) hA (by norm_num) I hI
  have hnon := source_centered_success_count_nonneg t A (2 / 5) I
  have hmean := hc.trans_le hlo
  refine ⟨I, hI, hmean, second_moment_pos_of_mean_pos sourceEnlargedLaw _ hi₁ hi₂
    hnon hmean, second_moment_ratio_lower_bound sourceEnlargedLaw _ hi₁ hi₂ hnon
    c D hc hD hlo hs, second_moment_ratio_probability sourceEnlargedLaw _ hi₁ hi₂
    hnon hmean, ?_⟩
  exact source_canonical_positive_probability_le_seed t A (2 / 5) I
    (by linarith) ht hI

end SRWTightness
