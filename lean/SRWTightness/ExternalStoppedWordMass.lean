import SRWTightness.KilledWordBridge

namespace SRWTightness

/-- A finite direction word with its prescribed first exit from C. -/
def AdmissibleExitWord (C : Finset Site) (x e : Site) (w : PathWord) : Prop :=
  (∀ k < w.length, x + position (wordPath w) k ∈ C) ∧
    x + position (wordPath w) w.length = e ∧ e ∉ C

/-- Standard independent uniform-increment cylinder mass for a word stopped at its first exit.
This explicit finite-word foundation contains no exterior conditioning or source estimates. -/
def StoppedWordProbabilityInput : Prop :=
  ∀ (C : Finset Site) (x e : Site) (w : PathWord), AdmissibleExitWord C x e w →
    pathLaw.real {ω | killedPathWord C x ω = w} = (1 / 4 : ℝ) ^ w.length

/-- The actual stopped-word bridge atom is the cylinder mass divided by the exit probability. -/
theorem killed_word_bridge_mass (hW : StoppedWordProbabilityInput)
    (C : Finset Site) (x e : Site) (w : PathWord) (hw : AdmissibleExitWord C x e w) :
    killedWordBridgeProbability C x e w = (1 / 4 : ℝ) ^ w.length / traceExitProbability C x e := by
  have hevent : {ω | killedPathWord C x ω = w ∧ domainExitLocation C x ω = e} =
      {ω | killedPathWord C x ω = w} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · exact And.left
    · intro hω
      refine ⟨hω, ?_⟩
      rw [← killedPathWord_exitLocation C x ω, hω]
      exact hw.2.1
  unfold killedWordBridgeProbability
  rw [hevent, hW C x e w hw]

end SRWTightness
