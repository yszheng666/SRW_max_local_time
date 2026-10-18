import SRWTightness.ExternalStoppedWordMass
import SRWTightness.ChildFirstExit

open MeasureTheory
namespace SRWTightness

/-- The actual killed word is an admissible first-exit word almost surely. -/
theorem killed_word_admissible (C : Finset Site) (x : Site) :
    ∀ᵐ ω ∂pathLaw, AdmissibleExitWord C x (domainExitLocation C x ω) (killedPathWord C x ω) := by
  filter_upwards [domainExit_ne_top_ae C x] with ω hfin
  refine ⟨?_, killedPathWord_exitLocation C x ω, position_domain_exit_not_mem C x ω hfin⟩
  intro i hi
  rw [killedPathWord_position C x ω i hi.le]
  exact position_before_domainSteps_mem C x ω hfin i hi

/-- A non-admissible word has zero prescribed-exit bridge mass, without a cylinder-mass input. -/
theorem killed_word_bridge_zero_of_not_admissible (C : Finset Site) (x e : Site)
    (w : PathWord) (hw : ¬ AdmissibleExitWord C x e w) :
    killedWordBridgeProbability C x e w = 0 := by
  have he : pathLaw.real {ω | killedPathWord C x ω = w ∧ domainExitLocation C x ω = e} = 0 := by
    calc
      _ = pathLaw.real ∅ := by
        apply measureReal_congr
        filter_upwards [killed_word_admissible C x] with ω hω
        change (killedPathWord C x ω = w ∧ domainExitLocation C x ω = e) = False
        apply propext
        constructor
        · rintro ⟨hu, he⟩
          rw [hu, he] at hω
          exact hw hω
        · exact False.elim
      _ = 0 := measureReal_empty
  simp only [killedWordBridgeProbability, he, zero_div]

/-- Every nonzero prescribed-exit bridge atom is supported on genuine first-exit words. -/
theorem killed_word_bridge_admissible (C : Finset Site) (x e : Site) (w : PathWord)
    (hw : killedWordBridgeProbability C x e w ≠ 0) : AdmissibleExitWord C x e w := by
  by_contra h
  exact hw (killed_word_bridge_zero_of_not_admissible C x e w h)

end SRWTightness
