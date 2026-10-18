import SRWTightness.NestedSiteCounter

namespace SRWTightness

/-- A site inside every inner domain performs the same activation at all levels. -/
theorem nestedSiteCounterStep_interior
    (levels : List (Finset Site × Finset Site)) (state : NestedSiteCounter) (z : Site)
    (hlen : state.length = levels.length)
    (hz : ∀ L ∈ levels, z ∈ L.1 ∧ z ∈ L.2) :
    nestedSiteCounterStep levels state z = nestedSiteCounterActivate state := by
  have hzero (rest : NestedSiteCounter) :
      nestedSiteCounterActivate (rest.map (fun _ ↦ (false, 0))) =
        rest.map (fun _ ↦ (true, 0)) := by
    cases rest with
    | nil => rfl
    | cons h t => simp [nestedSiteCounterActivate]
  induction levels generalizing state with
  | nil =>
    have he : state = [] := List.length_eq_zero_iff.mp hlen
    subst state
    rfl
  | cons level levels ih =>
    rcases level with ⟨K, C⟩
    cases state with
    | nil => simp at hlen
    | cons head rest =>
      rcases head with ⟨active, n⟩
      have hr : rest.length = levels.length := by simpa using hlen
      have hz0 := hz (K, C) List.mem_cons_self
      have hzt : ∀ L ∈ levels, z ∈ L.1 ∧ z ∈ L.2 :=
        fun L hL ↦ hz L (List.mem_cons_of_mem _ hL)
      have hi : nestedSiteCounterInitial levels = rest.map (fun _ ↦ (false, 0)) := by
        simp only [nestedSiteCounterInitial, List.map_const', hr]
      cases active with
      | false =>
        simp only [nestedSiteCounterStep, List.headD_cons, List.tail_cons,
          Bool.false_eq_true, ↓reduceIte, if_pos hz0.1, nestedSiteCounterActivate]
        rw [ih (nestedSiteCounterInitial levels)
          (by simp [nestedSiteCounterInitial]) hzt, hi, hzero]
      | true =>
        simp only [nestedSiteCounterStep, List.headD_cons, List.tail_cons,
          ↓reduceIte, if_pos hz0.2, nestedSiteCounterActivate, ih rest hr hzt]

end SRWTightness
