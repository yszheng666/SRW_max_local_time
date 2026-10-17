import SRWTightness.SourceCanonicalMoments
import SRWTightness.SourceCanonicalCountIntegrable
import SRWTightness.SourceCanonicalSuccessMaximum
import SRWTightness.SecondMomentSupportProbability

open MeasureTheory Filter
namespace SRWTightness

/-- The certified source moments imply a fixed positive seed probability on the original
path space. All generic forest interfaces are supplied before choosing time or observation level. -/
theorem source_seed_from_moments (A : ℝ) (hA : 1 ≤ A)
    (hMoments : SourceCanonicalMomentEstimate A)
    (hAllForest : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWForestJointInput (Mark K))
    (hAllMix : ∀ (α β : Type) [MeasurableSpace α] [MeasurableSpace β]
      [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable α] [Countable β]
      [MeasurableSpace (List α)] [MeasurableSpace (List β)]
      [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)],
      OrderedForestMixtureInput α β) :
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ t : ℝ in atTop,
      p ≤ pathLaw.real {ω | diskCenter (Real.exp t) ≤ Real.sqrt (diskMax (Real.exp t) ω)} := by
  obtain ⟨c, C, D, hc, hC, hD, hm⟩ := hMoments
  refine ⟨c ^ 2 / D, div_pos (pow_pos hc 2) hD, ?_⟩
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
  have hp := second_moment_positive_probability sourceEnlargedLaw
    (sourceCenteredSuccessCount t A (2 / 5) I) hi₁ hi₂
    (source_centered_success_count_nonneg t A (2 / 5) I) c D hc hD hlo hs
  exact hp.trans (source_canonical_positive_probability_le_seed t A (2 / 5) I
    (by linarith) ht hI)

end SRWTightness
