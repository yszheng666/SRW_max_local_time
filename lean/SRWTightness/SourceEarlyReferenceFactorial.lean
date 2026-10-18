import SRWTightness.ReferenceRootFactorialBound
import SRWTightness.ReferenceRootFirstMean
import SRWTightness.RootMeanSup
import SRWTightness.SourceEarlyFutureRootBound
import SRWTightness.SourceEarlyCompletionGeometry

open scoped ENNReal
open MeasureTheory Filter
namespace SRWTightness

/-- Equation 8.18 for the actual common reference law, retaining its real first mean. -/
theorem source_early_reference_factorial (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hinput : PotentialKernelAsymptoticInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
      ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let R := killedRootMeanSup (sourceCommonPairDomain t b j)
        (sourceEntranceDomain m 1 ℓ b ν) (sourceExitDomain m 1 ℓ b ν)
        (sourceEntranceDomain m 1 ℓ w ν) (sourceExitDomain m 1 ℓ w ν)
      R ≤ ENNReal.ofReal (C * ((J : ℝ) + 1)) ∧
      ∀ p : ℕ, rootBinomialMoment (sourceCommonWordLaw t b w j)
        (sourceEntranceDomain m 1 ℓ b ν) (sourceExitDomain m 1 ℓ b ν)
        (sourceEntranceDomain m 1 ℓ w ν) (sourceExitDomain m 1 ℓ w ν) (p + 1) ≤
        ENNReal.ofReal (∫ Y, ((sourceCommonWordRootCount t b ν Y +
          sourceCommonWordRootCount t w ν Y : ℕ) : ℝ) ∂sourceCommonWordLaw t b w j) *
        R ^ p := by
  obtain ⟨C, hC, Jf, hf⟩ := source_early_future_root_bound hLast hinput
  obtain ⟨Jo, ho⟩ := source_early_common_observation
  refine ⟨C, hC, max Jf Jo, ?_⟩
  intro J₀ hJ₀
  obtain ⟨af, haf, hf⟩ := hf J₀ ((le_max_left _ _).trans hJ₀)
  obtain ⟨ao, hao, ho⟩ := ho J₀ ((le_max_right _ _).trans hJ₀)
  obtain ⟨al, hl⟩ := source_early_distance_levels J₀
  refine ⟨max af (max ao al), haf.trans (le_max_left _ _), ?_⟩
  filter_upwards [hf, ho, hl, source_early_completion_geometry,
    source_early_root_observation_geometry] with t hf ho hl hc hg
  intro b w hbw ha hrange
  dsimp only
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
  have haf' := (le_max_left af (max ao al)).trans ha
  have hao' := (le_max_left ao al).trans ((le_max_right _ _).trans ha)
  have hal' := (le_max_right ao al).trans ((le_max_right _ _).trans ha)
  have ha1 : 1 ≤ a := haf.trans haf'
  have hν := (hl a hal' hrange).2.2
  have hKD := (ho b w hbw hao' hrange).2.2.2.1
  have hb := hg b w ν J hbw ha1 hν rfl b (by simp)
  have hw := hg b w ν J hbw ha1 hν rfl w (by simp)
  have hC₁ : C₁ ⊆ D := hb.2.1.trans hKD
  have hC₂ : C₂ ⊆ D := hw.2.1.trans hKD
  obtain ⟨hdis, hsites⟩ := hc b w ν J hbw ha1 hν rfl
  have hexit : ∀ z ∈ rootCompletionSet C₁ C₂, z ∈ D ∧ z ∉ C₁ ∧ z ∉ C₂ := by
    intro z hz
    obtain ⟨hK, h₁, h₂⟩ := hsites z hz
    exact ⟨hKD hK, h₁, h₂⟩
  have hmean : ∀ x ∈ rootCompletionSet C₁ C₂,
      killedRootBinomialMoment D L₁ C₁ L₂ C₂ x 1 ≤
        ENNReal.ofReal (C * ((J : ℝ) + 1)) := by
    intro x hx
    rw [killedRootBinomialMoment_one_ofReal hLast D L₁ C₁ L₂ C₂ hb.1 hw.1 hC₁ hC₂ x]
    apply ENNReal.ofReal_le_ofReal
    change sourceFutureRootMean t b w x j ν ≤ C * ((J : ℝ) + 1)
    rcases hx with hx | hx
    · exact hf b w hbw haf' hrange b (by simp) x hx
    · exact hf b w hbw haf' hrange w (by simp) x hx
  refine ⟨killedRootMeanSup_le D L₁ C₁ L₂ C₂ _ hmean, ?_⟩
  intro p
  have hh := reference_root_factorial_bound hrec D (sourceCommonPairObservation b w)
    L₁ C₁ L₂ C₂ hb.1 hw.1 hC₁ hC₂ hdis hexit (sourceCommonPairIntensity t j)
    (killedRootMeanSup D L₁ C₁ L₂ C₂)
    (killedRootMean_le_sup D L₁ C₁ L₂ C₂) p
  rw [reference_root_first_mean_ofReal hLast D _ L₁ C₁ L₂ C₂ hb.1 hw.1 hC₁ hC₂] at hh
  exact hh

end SRWTightness
