import SRWTightness.SourceCommonReferenceWord
import SRWTightness.ReferenceWordRootMean
import SRWTightness.SourceEarlyCommonObservation
import SRWTightness.SourceEarlyCommonIntensity
import SRWTightness.SourceEarlyRootObservationGeometry

open MeasureTheory Filter
namespace SRWTightness

/-- Equation 8.14: each label's actual ordered short-root count under the common reference law
has mean alpha_j times its own short-annulus capacity. Source geometry and reference mixing are
internal; the only new input is the generic finite-walk last-visit identity. -/
theorem source_early_common_root_mean (hLast : FiniteLastVisitCountInput) :
    ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ → ∃ a₀ : ℕ, 1 ≤ a₀ ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      IsProbabilityMeasure (sourceCommonWordLaw t b w j) ∧
      ∀ z ∈ ({b, w} : Finset Site),
      Integrable (fun Y ↦ (sourceCommonWordRootCount t z ν Y : ℝ))
        (sourceCommonWordLaw t b w j) ∧
      (∫ Y, (sourceCommonWordRootCount t z ν Y : ℝ) ∂sourceCommonWordLaw t b w j) =
        sourceCommonPairIntensity t j * capacity
          (sourceExitDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) z ν)
          (sourceEntranceDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) z ν) := by
  obtain ⟨Jmin, hobs⟩ := source_early_common_observation
  refine ⟨Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨a₀, ha₀, ho⟩ := hobs J₀ hJ₀
  obtain ⟨a₁, hl⟩ := source_early_distance_levels J₀
  refine ⟨max a₀ a₁, ha₀.trans (le_max_left _ _), ?_⟩
  filter_upwards [ho, hl, source_early_common_intensity,
    source_early_root_observation_geometry] with t ho hl hi hg
  intro b w hbw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  have ha1 : 1 ≤ a := ha₀.trans ((le_max_left _ _).trans ha)
  have hν := (hl a ((le_max_right _ _).trans ha) hrange).2.2
  have hj : j ≤ 2 * sourceCoarseLowerLevel t := by dsimp [j]; omega
  obtain ⟨_, _, _, hKD, hcap⟩ := ho b w hbw ((le_max_left _ _).trans ha) hrange
  have hα := (hi j hj).2.1.le
  have hc := hcap.trans (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  refine ⟨referenceWordMarkLaw_probability _ _ _ hα hc, ?_⟩
  intro z hz
  obtain ⟨hLC, hCK, _⟩ := hg b w ν J hbw ha1 hν rfl z hz
  exact ⟨integrable_referenceWordMark_roots hLast _ _ _ _ hLC (hCK.trans hKD) _,
    referenceWordMark_root_mean hLast _ _ _ _ hKD (hLC.trans hCK) hLC
      (hCK.trans hKD) _ hα hc⟩

end SRWTightness
