import SRWTightness.ExteriorRecordProductLaw
import SRWTightness.FiniteConditionalLower
import Mathlib.Data.List.GetD

open MeasureTheory
namespace SRWTightness

/-- Read each exterior slot at its fixed index; defaults only affect wrong-length words. -/
def exteriorFixedTuple {R : Type*} (h : ExteriorPathRecord) (F : ExteriorSlot → PathWord → R)
    (us : List PathWord) : Fin h.1.length → R :=
  fun i ↦ F (h.1.get i) (us.getD i.val ⟨0, Fin.elim0⟩)

/-- The fixed tuple is exactly the complete chronological record list on matching-length words. -/
theorem exterior_fixed_tuple_list {R : Type*} (h : ExteriorPathRecord)
    (F : ExteriorSlot → PathWord → R) (us : List PathWord) (hlen : us.length = h.1.length) :
    List.ofFn (exteriorFixedTuple h F us) = (h.1.zip us).map (fun p ↦ F p.1 p.2) := by
  have he : List.ofFn (fun i : Fin h.1.length ↦ us.getD i.val ⟨0, Fin.elim0⟩) = us := by
    generalize hn : h.1.length = n at hlen ⊢
    clear hn
    subst n
    simpa only [List.getD_eq_get] using List.ofFn_get us
  calc
    _ = (h.1.zip (List.ofFn (fun i : Fin h.1.length ↦ us.getD i.val ⟨0, Fin.elim0⟩))).map
        (fun p ↦ F p.1 p.2) :=
      (list_zip_ofFn_map h.1 (fun i ↦ us.getD i.val ⟨0, Fin.elim0⟩) F).symm
    _ = _ := by rw [he]

/-- On the actual exterior fiber, a fixed tuple atom equals the complete comparison list atom. -/
theorem exterior_fixed_tuple_event {R : Type*} (D K C : Finset Site) (label : Site → Bool)
    (x : Site) (h : ExteriorPathRecord) (F : ExteriorSlot → PathWord → R)
    (r : Fin h.1.length → R) :
    {ω | exteriorFixedTuple h F (killedChildRecords D K C x (fun _ u ↦ u) ω) = r ∧
      killedExteriorRecord D K C label x ω = h} =
    {ω | (h.1.zip (killedChildRecords D K C x (fun _ u ↦ u) ω)).map
      (fun p ↦ F p.1 p.2) = List.ofFn r ∧ killedExteriorRecord D K C label x ω = h} := by
  ext ω
  by_cases hh : killedExteriorRecord D K C label x ω = h
  · have hlen := killedExteriorRecord_length D K C label x ω
    rw [hh] at hlen
    have he := exterior_fixed_tuple_list h F _ hlen.symm
    simp only [Set.mem_setOf_eq, hh, and_true, ← he, List.ofFn_inj]
  · simp only [Set.mem_setOf_eq, hh, and_false]

/-- Mapping the actual conditional word measure to fixed tuples yields precisely the existing
conditional list-atom probability, without a length assumption away from the exterior fiber. -/
theorem exterior_conditional_tuple_atom {R : Type*} [MeasurableSpace R]
    [MeasurableSingletonClass R] (D K C : Finset Site) (label : Site → Bool) (x : Site)
    (h : ExteriorPathRecord) (F : ExteriorSlot → PathWord → R) (r : Fin h.1.length → R) :
    ((ProbabilityTheory.cond pathLaw {ω | killedExteriorRecord D K C label x ω = h}).map
      (fun ω ↦ exteriorFixedTuple h F (killedChildRecords D K C x (fun _ u ↦ u) ω))).real {r} =
      pathLaw.real {ω | (h.1.zip (killedChildRecords D K C x (fun _ u ↦ u) ω)).map
        (fun p ↦ F p.1 p.2) = List.ofFn r ∧ killedExteriorRecord D K C label x ω = h} /
      pathLaw.real {ω | killedExteriorRecord D K C label x ω = h} := by
  letI : MeasurableSpace ExteriorPathRecord := ⊤
  letI : MeasurableSingletonClass ExteriorPathRecord := ⟨fun _ ↦ trivial⟩
  have hH : MeasurableSet {ω | killedExteriorRecord D K C label x ω = h} :=
    (measurable_killedExteriorRecord D K C label x) (measurableSet_singleton h)
  have hf : Measurable (fun ω ↦ exteriorFixedTuple h F
      (killedChildRecords D K C x (fun _ u ↦ u) ω)) :=
    (measurable_of_countable (exteriorFixedTuple h F)).comp
      (measurable_killedChildRecords D K C x (fun _ u ↦ u))
  rw [map_measureReal_apply hf (measurableSet_singleton r), conditional_real_apply _ _ _ hH]
  change pathLaw.real {ω | exteriorFixedTuple h F
    (killedChildRecords D K C x (fun _ u ↦ u) ω) = r ∧
    killedExteriorRecord D K C label x ω = h} / _ = _
  rw [exterior_fixed_tuple_event]

end SRWTightness
