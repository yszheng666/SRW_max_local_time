import SRWTightness.SourcePairSuccessRecordInclusion
import SRWTightness.SourcePairRecordProbability
import SRWTightness.SourceSiteBridgeLaw

open MeasureTheory Filter

namespace SRWTightness

/-- On the common enlarged probability space the two successes are bounded by one pair record. -/
theorem source_pair_success_probability_le_record :
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
      let h := sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1)
      sourceEnlargedLaw.real
        (sourceSiteSuccessEvent t A γ b I z ∩ sourceSiteSuccessEvent t A γ w J z') ≤
        sourcePairRecordProbability t A b I i z y (h ^ γ) := by
  filter_upwards [source_pair_success_record_inclusion] with t happ
  intro A γ b w I J i hA ht hlog hI hi z y z' hy hz' hblo hbhi
  let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
  let h := sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1)
  letI : MeasurableSpace (List (Mark M)) := ⊤
  letI : MeasurableSingletonClass (List (Mark M)) := ⟨fun _ ↦ trivial⟩
  letI : MeasurableSpace (List (FiniteExcursionRecord (Mark M) n)) := ⊤
  letI : MeasurableSingletonClass (List (FiniteExcursionRecord (Mark M) n)) := ⟨fun _ ↦ trivial⟩
  let E : Set (Sample × (ℕ → GaussianCoefficientSpace)) :=
    (fun p ↦ (sourceActualForest t b M p.1, p.2)) ⁻¹'
      sourcePairForestEvent t A b I i z y (h ^ γ) n
  have hF : Measurable (sourceActualForest t b M) := measurable_killedChildRecords _ _ _ _ _
  have hE : MeasurableSet E := (sourcePairForestEvent_measurable t A b I i z y (h ^ γ) n).preimage
    ((hF.comp measurable_fst).prodMk measurable_snd)
  have hb := (Measure.quasiMeasurePreserving_snd
    (μ := pathLaw) (ν := independentBridgeLaw ℕ)).ae
    (happ A γ b w I J i hA ht hlog hI hi z y z' hy hz' hblo hbhi)
  have hball := (source_site_projection_preserving b).quasiMeasurePreserving.ae hb
  have hfin := (Measure.quasiMeasurePreserving_fst
    (μ := pathLaw) (ν := sourceSiteBridgeLaw)).ae
      (domainExit_ne_top_ae (diskFinset (Real.exp t)) 0)
  have hinc : ∀ᵐ p ∂sourceEnlargedLaw,
      p ∈ (sourceSiteSuccessEvent t A γ b I z ∩ sourceSiteSuccessEvent t A γ w J z') →
      p ∈ sourceSiteProjection b ⁻¹' E := by
    filter_upwards [hball, hfin] with p hp hf
    intro hs
    exact hp p.1 hf (p.2 w) hs.1 hs.2
  have hmarg := (source_site_projection_preserving b).measureReal_preimage hE.nullMeasurableSet
  change _ ≤ (pathLaw.prod (independentBridgeLaw ℕ)).real E
  rw [← hmarg]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hinc)

end SRWTightness
