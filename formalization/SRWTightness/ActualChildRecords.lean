import SRWTightness.ChildWordShift

open MeasureTheory

namespace SRWTightness

/-- Project each complete child word to its record, preserving chronological order and multiplicity. -/
def wordChildRecords {R : Type*} (K C : Finset Site) (x : Site)
    (F : Site → PathWord → R) (w : PathWord) : List R :=
  (wordChildIntervals K C x w).map (fun q ↦
    F (x + position (wordPath w) q.1) (slicePathWord w q.1 q.2))

/-- Actual child records extracted from the parent killed SRW word. -/
noncomputable def killedChildRecords {R : Type*} (D K C : Finset Site) (x : Site)
    (F : Site → PathWord → R) (ω : Sample) : List R :=
  wordChildRecords K C x F (killedPathWord D x ω)

theorem measurable_killedChildRecords {R : Type*} [MeasurableSpace (List R)]
    (D K C : Finset Site) (x : Site) (F : Site → PathWord → R) :
    Measurable (killedChildRecords D K C x F) :=
  measurable_killed_word_record D x (wordChildRecords K C x F)

/-- Every specified ordered child record list is a measurable event. -/
theorem measurableSet_killedChildRecords_eq {R : Type*} (D K C : Finset Site) (x : Site)
    (F : Site → PathWord → R) (rs : List R) :
    MeasurableSet {ω | killedChildRecords D K C x F ω = rs} :=
  (measurable_killedPathWord D x)
    (Set.to_countable {w | wordChildRecords K C x F w = rs}).measurableSet

/-- Record entrances may be evaluated directly on the original path. -/
theorem killedChildRecords_eq_map_actual {R : Type*} (D K C : Finset Site) (x : Site)
    (F : Site → PathWord → R) (ω : Sample) :
    killedChildRecords D K C x F ω =
      (killedChildIntervals D K C x ω).map
        (fun q ↦ F (x + position ω q.1) (slicePathWord (killedPathWord D x ω) q.1 q.2)) := by
  apply List.map_congr_left
  intro q hq
  have hb := (wordChildIntervals_endpoint_le K C x (killedPathWord D x ω) q hq).1
  rw [killedPathWord_position D x ω q.1 hb]

/-- Actual projected child records renew at the first child's actual exit, retaining its killed word. -/
theorem killedChildRecords_renewal {R : Type*} (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) (x : Site) (F : Site → PathWord → R) (ω : Sample) (a b : ℕ)
    (hparent : domainExit D x ω ≠ ⊤)
    (haeq : a = domainSteps (D \ K) x ω)
    (hbeq : b = a + domainSteps C (x + position ω a) (shift a ω))
    (hentry : x + position ω a ∈ K) :
    killedChildRecords D K C x F ω =
      F (x + position ω a) (killedPathWord C (x + position ω a) (shift a ω)) ::
        killedChildRecords D K C (x + position ω b) F (shift b ω) := by
  have ha : a ≤ domainSteps D x ω := by
    rw [haeq]
    exact (subdomain_exit_bounds D (D \ K) Finset.sdiff_subset x ω hparent).2
  have hb : b ≤ domainSteps D x ω := by
    rw [hbeq]
    exact (shifted_subdomain_exit_bounds D C hCD x ω hparent a ha).2
  rw [killedChildRecords_eq_map_actual,
    killedChildIntervals_nested_renewal D K C hKC hCD x ω a b hparent haeq hbeq hentry,
    List.map_cons]
  apply congrArg₂ List.cons
  · rw [slice_killedPathWord_eq_child D C x ω a b hb hbeq]
  · rw [killedChildRecords_eq_map_actual, List.map_map]
    apply List.map_congr_left
    intro q hq
    have hqend := (wordChildIntervals_endpoint_le K C (x + position ω b)
      (killedPathWord D (x + position ω b) (shift b ω)) q hq).2
    have hc : q.2 ≤ domainSteps D x ω - b := by
      change q.2 ≤ domainSteps D (x + position ω b) (shift b ω) at hqend
      rwa [domainSteps_shift_before_exit D x ω hparent b hb] at hqend
    dsimp only [Function.comp_def]
    rw [slice_killedPathWord_shift D x ω hparent b q.1 q.2 hb hc,
      position_add, ← add_assoc]

/-- Projecting child words cannot create or remove children. -/
theorem killedChildRecords_eq_nil_iff {R : Type*} (D K C : Finset Site) (x : Site)
    (F : Site → PathWord → R) (ω : Sample) :
    killedChildRecords D K C x F ω = [] ↔ killedChildIntervals D K C x ω = [] := by
  simp [killedChildRecords, wordChildRecords, killedChildIntervals]

/-- The actual empty projected-record list has exactly the competing outer-exit mass. -/
theorem killedChildRecords_nil_competing_mass {R : Type*} (D K C : Finset Site)
    (hKC : K ⊆ C) (hCD : C ⊆ D) (x : Site) (F : Site → PathWord → R) :
    pathLaw.real {ω | killedChildRecords D K C x F ω = []} = competingExitMass D K x := by
  simp_rw [killedChildRecords_eq_nil_iff]
  exact killedChildIntervals_nil_competing_mass D K C hKC hCD x

end SRWTightness
