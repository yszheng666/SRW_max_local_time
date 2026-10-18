import SRWTightness.ExteriorWordReassembly
import SRWTightness.StoppedWordProbabilityInternal

namespace SRWTightness

/-- Equal exterior data and equal internal words imply equality of the entire finite path. -/
theorem exterior_word_records_injective (K C : Finset Site) (label : Site → Bool)
    (x : Site) (u v : PathWord)
    (he : wordExteriorRecord K C label x u = wordExteriorRecord K C label x v)
    (hi : wordChildRecords K C x (fun _ w ↦ w) u =
      wordChildRecords K C x (fun _ w ↦ w) v) : u = v := by
  rw [← reassembleExteriorWord_actual K C label x u,
    ← reassembleExteriorWord_actual K C label x v, he, hi]

/-- A realized joint exterior/internal-word fiber is exactly one killed-word event. -/
theorem exterior_word_fiber_singleton (D K C : Finset Site) (label : Site → Bool)
    (x : Site) (w : PathWord) :
    {ω | killedChildRecords D K C x (fun _ u ↦ u) ω =
        wordChildRecords K C x (fun _ u ↦ u) w ∧
      killedExteriorRecord D K C label x ω = wordExteriorRecord K C label x w} =
        {ω | killedPathWord D x ω = w} := by
  ext ω
  constructor
  · rintro ⟨hi, he⟩
    exact exterior_word_records_injective K C label x (killedPathWord D x ω) w he hi
  · intro hw
    change wordChildRecords K C x (fun _ u ↦ u) (killedPathWord D x ω) = _ ∧
      wordExteriorRecord K C label x (killedPathWord D x ω) = _
    rw [hw]
    exact ⟨rfl, rfl⟩

/-- Every admissible realized exterior/internal-word fiber has its exact cylinder mass. -/
theorem exterior_word_fiber_cylinder_mass (D K C : Finset Site) (label : Site → Bool)
    (x e : Site) (w : PathWord) (hw : AdmissibleExitWord D x e w) :
    pathLaw.real {ω | killedChildRecords D K C x (fun _ u ↦ u) ω =
        wordChildRecords K C x (fun _ u ↦ u) w ∧
      killedExteriorRecord D K C label x ω = wordExteriorRecord K C label x w} =
        (1 / 4 : ℝ) ^ w.length := by
  rw [exterior_word_fiber_singleton]
  exact stoppedWordProbabilityInput_internal D x e w hw

end SRWTightness
