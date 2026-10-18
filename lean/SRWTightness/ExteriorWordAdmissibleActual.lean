import SRWTightness.ExteriorWordAdmissibility
import SRWTightness.ExteriorRecordExitRenewal
import SRWTightness.ExteriorRecordNoVisit
import SRWTightness.AdmissibleWordSuffix
import SRWTightness.ChildWordFirstTimes

namespace SRWTightness

/-- Every actual admissible killed word produces locally admissible retained exterior pieces. -/
theorem exteriorWordAdmissible_actual (D K C : Finset Site) (label : Site → Bool)
    (hKC : K ⊆ C) (hCD : C ⊆ D) (x e : Site) (w : PathWord)
    (hw : AdmissibleExitWord D x e w) :
    ExteriorWordAdmissible D K C label x (wordExteriorRecord K C label x w) := by
  have aux : ∀ N : ℕ, ∀ (x e : Site) (w : PathWord), w.length = N →
      AdmissibleExitWord D x e w →
      ExteriorWordAdmissible D K C label x (wordExteriorRecord K C label x w) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro x e w hN hw
      have hend : x + position (wordPath w) w.length ∉ C := by
        rw [hw.2.1]
        exact fun he ↦ hw.2.2 (hCD he)
      by_cases hvisit : ∃ i < w.length, x + position (wordPath w) i ∈ K
      · obtain ⟨a, b, hab, hb, hpre, ha, hin, hout⟩ :=
          word_first_child_times K C hKC x w hend hvisit
        have hpos (i : ℕ) (hi : i ≤ a) :
            x + position (wordPath (slicePathWord w 0 a)) i =
              x + position (wordPath w) i := by
          rw [slicePathWord_position w 0 a i (by omega)]
          have hz : shift 0 (wordPath w) = wordPath w := by
            funext j
            simp only [shift, Nat.zero_add]
          rw [hz]
        have htail := ih (w.length - b) (by omega)
          (x + position (wordPath w) b) e (slicePathWord w b w.length) rfl
          (admissibleExitWord_suffix D x e w hw b hb)
        rw [wordExteriorRecord_exit_renewal K C hKC label x w a b hab hb hpre ha hin hout]
        rw [ExteriorWordAdmissible]
        refine ⟨?_, ?_, ?_, ha, rfl, hout, htail⟩
        · intro i hi
          change i < a at hi
          rw [hpos i hi.le]
          exact hw.1 i (by omega)
        · intro i hi
          change i < a at hi
          rw [hpos i hi.le]
          exact hpre i hi
        · exact hpos a le_rfl
      · have hnone : ∀ i ≤ w.length, x + position (wordPath w) i ∉ K := by
          intro i hi hmem
          by_cases he : i = w.length
          · exact hend (he ▸ hKC hmem)
          · exact hvisit ⟨i, by omega, hmem⟩
        rw [wordExteriorRecord_no_visit K C label x w hnone, ExteriorWordAdmissible]
        exact ⟨⟨e, hw⟩, hnone⟩
  exact aux w.length x e w rfl hw

end SRWTightness
