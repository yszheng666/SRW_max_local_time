import SRWTightness.AdmissibleWordKilledIdentity
import SRWTightness.KilledWordPrefixCongruence
import SRWTightness.FiniteDirectionPrefixMass

namespace SRWTightness

/-- A prescribed admissible stopped word is exactly its finite increment cylinder. -/
theorem admissibleExitWord_event_prefix (C : Finset Site) (x e : Site) (w : PathWord)
    (hw : AdmissibleExitWord C x e w) :
    {ω | killedPathWord C x ω = w} = {ω | ∀ i < w.length, ω i = wordPath w i} := by
  ext ω
  constructor
  · intro he i hi
    have hlen : domainSteps C x ω = w.length := congrArg PathWord.length he
    have heval := congrArg (fun u : PathWord ↦ wordPath u i) he
    have hiD : i < domainSteps C x ω := by omega
    simpa [wordPath, killedPathWord, extendWord, hiD, hi] using heval
  · intro hp
    obtain ⟨hfin, hlen⟩ := admissibleExitWord_domainSteps C x e w hw
    have hh := killedPathWord_eq_of_prefix C x (wordPath w) ω hfin
      (fun i hi ↦ (hp i (by omega)).symm)
    exact hh.symm.trans (admissibleExitWord_killedPathWord C x e w hw)

/-- The full stopped-word cylinder-probability input holds for the actual SRW law. -/
theorem stoppedWordProbabilityInput_internal : StoppedWordProbabilityInput := by
  intro C x e w hw
  rw [admissibleExitWord_event_prefix C x e w hw]
  exact finite_direction_prefix_real_mass w.length (wordPath w)

end SRWTightness
