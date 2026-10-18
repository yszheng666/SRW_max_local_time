import SRWTightness.ExteriorWordPairAdmissibility
import SRWTightness.KilledWordBridgeSupport
import SRWTightness.ExternalExteriorBridge
import Mathlib.Algebra.BigOperators.Ring.List

open MeasureTheory
namespace SRWTightness

/-- A joint fiber containing an inadmissible inserted word is empty. -/
theorem exterior_word_fiber_zero_of_not_admissible (D K C : Finset Site) (hKC : K ⊆ C)
    (label : Site → Bool) (x : Site) (h : ExteriorPathRecord) (us : List PathWord)
    (hn : ¬∀ pair ∈ h.1.zip us,
      AdmissibleExitWord C pair.1.2.2.1 pair.1.2.2.2 pair.2) :
    pathLaw.real {ω | killedChildRecords D K C x (fun _ u ↦ u) ω = us ∧
      killedExteriorRecord D K C label x ω = h} = 0 := by
  have he : {ω | killedChildRecords D K C x (fun _ u ↦ u) ω = us ∧
      killedExteriorRecord D K C label x ω = h} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    obtain ⟨hu, hh⟩ := hω
    apply hn
    have hw := wordExteriorRecord_words_admissible K C hKC label x (killedPathWord D x ω)
    change ∀ pair ∈ (killedExteriorRecord D K C label x ω).1.zip
      (killedChildRecords D K C x (fun _ u ↦ u) ω),
      AdmissibleExitWord C pair.1.2.2.1 pair.1.2.2.2 pair.2 at hw
    rwa [hu, hh] at hw
  rw [he, measureReal_empty]

/-- An inadmissible internal word makes the prescribed-exit bridge product vanish. -/
theorem exteriorBridgeWordProduct_zero_of_not_admissible (C : Finset Site)
    (h : ExteriorPathRecord) (us : List PathWord)
    (hn : ¬∀ pair ∈ h.1.zip us,
      AdmissibleExitWord C pair.1.2.2.1 pair.1.2.2.2 pair.2) :
    exteriorBridgeWordProduct C h us = 0 := by
  classical
  push_neg at hn
  obtain ⟨pair, hp, hbad⟩ := hn
  exact List.prod_eq_zero (List.mem_map.mpr ⟨pair, hp,
    killed_word_bridge_zero_of_not_admissible C _ _ _ hbad⟩)

/-- The actual joint fiber vanishes unless its internal word count equals its header count. -/
theorem exterior_word_fiber_zero_wrong_length (D K C : Finset Site)
    (label : Site → Bool) (x : Site) (h : ExteriorPathRecord) (us : List PathWord)
    (hlen : us.length ≠ h.1.length) :
    pathLaw.real {ω | killedChildRecords D K C x (fun _ u ↦ u) ω = us ∧
      killedExteriorRecord D K C label x ω = h} = 0 := by
  have he : {ω | killedChildRecords D K C x (fun _ u ↦ u) ω = us ∧
      killedExteriorRecord D K C label x ω = h} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    have hh := killedExteriorRecord_length D K C label x ω
    rw [hω.1, hω.2] at hh
    exact hlen hh.symm
  rw [he, measureReal_empty]

end SRWTightness
