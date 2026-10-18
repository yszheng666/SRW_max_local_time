import SRWTightness.NestedWordExtraction

namespace SRWTightness

/-- Pending flags and completed totals for the successive nested excursion levels. -/
abbrev NestedSiteCounter := List (Bool × ℕ)

/-- Empty levels represent one terminal record; nonempty levels count completed children. -/
def nestedSiteCounterValue : NestedSiteCounter → ℕ
  | [] => 1
  | (_, n) :: _ => n

/-- A fresh scanner has no pending excursions and no completed children. -/
def nestedSiteCounterInitial (levels : List (Finset Site × Finset Site)) : NestedSiteCounter :=
  levels.map (fun _ ↦ (false, 0))

/-- Process one observed site, including the entrance and exit in every active child scanner. -/
def nestedSiteCounterStep : List (Finset Site × Finset Site) →
    NestedSiteCounter → Site → NestedSiteCounter
  | [], _, _ => []
  | (K, C) :: levels, state, z =>
      let head := state.headD (false, 0)
      let rest := state.tail
      if head.1 then
        let next := nestedSiteCounterStep levels rest z
        if z ∈ C then (true, head.2) :: next
        else (false, head.2 + nestedSiteCounterValue next) :: nestedSiteCounterInitial levels
      else if z ∈ K then
        (true, head.2) :: nestedSiteCounterStep levels (nestedSiteCounterInitial levels) z
      else (false, head.2) :: rest

/-- The simultaneous finite-state scan of a list of observed sites. -/
def nestedSiteCounterRun (levels : List (Finset Site × Finset Site))
    (state : NestedSiteCounter) (sites : List Site) : NestedSiteCounter :=
  sites.foldl (nestedSiteCounterStep levels) state

/-- Activating every level preserves completed totals only along already active parents. -/
def nestedSiteCounterActivate : NestedSiteCounter → NestedSiteCounter
  | [] => []
  | (active, n) :: rest =>
      (true, n) :: (if active then nestedSiteCounterActivate rest
        else rest.map (fun _ ↦ (true, 0)))

/-- Activation is idempotent, even for states with pending incomplete excursions. -/
theorem nestedSiteCounterActivate_idempotent (state : NestedSiteCounter) :
    nestedSiteCounterActivate (nestedSiteCounterActivate state) =
      nestedSiteCounterActivate state := by
  have hm (rest : NestedSiteCounter) :
      nestedSiteCounterActivate (rest.map (fun _ ↦ (true, 0))) =
        rest.map (fun _ ↦ (true, 0)) := by
    induction rest with
    | nil => rfl
    | cons h t ih => simp only [List.map_cons, nestedSiteCounterActivate, ↓reduceIte, ih]
  induction state with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨active, n⟩
    cases active <;> simp only [nestedSiteCounterActivate, Bool.false_eq_true, ↓reduceIte, ih, hm]

end SRWTightness
