import SRWTightness.SourceEarlyCompletionGeometry
import SRWTightness.SourceEarlyCommonObservation
import SRWTightness.FiniteRootCompletionInput

open MeasureTheory Filter
namespace SRWTightness

/-- The generic completion recursion applies to the actual early source domains. -/
theorem source_early_completion_recursion (hrec : FiniteRootCompletionInput) :
    ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ → ∃ a₀ : ℕ, 1 ≤ a₀ ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let D := sourceCommonPairDomain t b j
      let L₁ := sourceEntranceDomain m 1 ℓ b ν
      let C₁ := sourceExitDomain m 1 ℓ b ν
      let L₂ := sourceEntranceDomain m 1 ℓ w ν
      let C₂ := sourceExitDomain m 1 ℓ w ν
      ∀ x : Site,
        (∀ᵐ Y ∂killedWordMarkLaw D x,
          ∀ z ∈ wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y, z ∈ rootCompletionSet C₁ C₂) ∧
        ∀ p : ℕ, killedRootBinomialMoment D L₁ C₁ L₂ C₂ x (p + 1) =
          ∫⁻ Y, ((wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y).map
            (fun z ↦ killedRootBinomialMoment D L₁ C₁ L₂ C₂ z p)).sum ∂killedWordMarkLaw D x := by
  obtain ⟨Jmin, ho⟩ := source_early_common_observation
  refine ⟨Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨a₀, ha₀, ho⟩ := ho J₀ hJ₀
  obtain ⟨a₁, hl⟩ := source_early_distance_levels J₀
  refine ⟨max a₀ a₁, ha₀.trans (le_max_left _ _), ?_⟩
  filter_upwards [ho, hl, source_early_completion_geometry,
    source_early_root_observation_geometry] with t ho hl hc hg
  intro b w hbw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := sourceEarlyDistanceGap a J₀
  let ν := a + J + 5
  have ha₀' := (le_max_left a₀ a₁).trans ha
  have ha1 : 1 ≤ a := ha₀.trans ha₀'
  have hν := (hl a ((le_max_right a₀ a₁).trans ha) hrange).2.2
  have hKD := (ho b w hbw ha₀' hrange).2.2.2.1
  have hb := hg b w ν J hbw ha1 hν rfl b (by simp)
  have hw := hg b w ν J hbw ha1 hν rfl w (by simp)
  obtain ⟨hdis, hsites⟩ := hc b w ν J hbw ha1 hν rfl
  apply hrec _ _ _ _ _ hb.1 hw.1 (hb.2.1.trans hKD) (hw.2.1.trans hKD) hdis
  intro z hz
  obtain ⟨hK, hb, hw⟩ := hsites z hz
  exact ⟨hKD hK, hb, hw⟩

end SRWTightness
