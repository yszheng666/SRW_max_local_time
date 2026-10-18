import SRWTightness.NestedSiteCounter

namespace SRWTightness

/-- Activating nested scanners preserves their number of levels. -/
theorem nestedSiteCounterActivate_length (state : NestedSiteCounter) :
    (nestedSiteCounterActivate state).length = state.length := by
  induction state with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨active, n⟩
    cases active <;> simp [nestedSiteCounterActivate, ih]

/-- Processing an observation preserves the well-formed number of nested scanner levels. -/
theorem nestedSiteCounterStep_length (levels : List (Finset Site × Finset Site))
    (state : NestedSiteCounter) (z : Site) (hlen : state.length = levels.length) :
    (nestedSiteCounterStep levels state z).length = levels.length := by
  induction levels generalizing state with
  | nil => rfl
  | cons level levels ih =>
    rcases level with ⟨K, C⟩
    cases state with
    | nil => simp at hlen
    | cons head rest =>
      rcases head with ⟨active, n⟩
      have hr : rest.length = levels.length := by simpa using hlen
      have hi : (nestedSiteCounterInitial levels).length = levels.length := by
        simp [nestedSiteCounterInitial]
      cases active <;> by_cases hC : z ∈ C <;> by_cases hK : z ∈ K <;>
        simp [nestedSiteCounterStep, hC, hK, ih rest hr, ih _ hi, hi, hr]

/-- A finite run preserves the number of nested scanner levels. -/
theorem nestedSiteCounterRun_length (levels : List (Finset Site × Finset Site))
    (state : NestedSiteCounter) (sites : List Site) (hlen : state.length = levels.length) :
    (nestedSiteCounterRun levels state sites).length = levels.length := by
  induction sites generalizing state with
  | nil => exact hlen
  | cons z sites ih =>
    exact ih _ (nestedSiteCounterStep_length levels state z hlen)

end SRWTightness
