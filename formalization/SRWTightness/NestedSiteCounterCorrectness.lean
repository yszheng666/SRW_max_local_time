import SRWTightness.NestedSiteCount

namespace SRWTightness

/-- The counter matches weighted excursions when its inner-level run has the stated value. -/
theorem nestedSiteCounter_weighted (K C : Finset Site)
    (levels : List (Finset Site × Finset Site)) (weight : List Site → ℕ)
    (hweight : ∀ sites, nestedSiteCounterValue
      (nestedSiteCounterRun levels (nestedSiteCounterInitial levels) sites) = weight sites)
    (sites : List Site) (pending : Option (List Site)) (n : ℕ) :
    nestedSiteCounterValue (nestedSiteCounterRun ((K, C) :: levels)
      (match pending with
      | none => (false, n) :: nestedSiteCounterInitial levels
      | some pre => (true, n) ::
          nestedSiteCounterRun levels (nestedSiteCounterInitial levels) pre) sites) =
      n + siteExcursionWeight K C weight pending sites := by
  have happ (pre : List Site) (z : Site) :
      nestedSiteCounterStep levels
        (nestedSiteCounterRun levels (nestedSiteCounterInitial levels) pre) z =
      nestedSiteCounterRun levels (nestedSiteCounterInitial levels) (pre ++ [z]) := by
    simp [nestedSiteCounterRun, List.foldl_append]
  induction sites generalizing pending n with
  | nil => cases pending <;> rfl
  | cons z sites ih =>
    cases pending with
    | none =>
      by_cases hz : z ∈ K
      · simpa only [nestedSiteCounterRun, List.foldl_cons, nestedSiteCounterStep,
          List.headD_cons, List.tail_cons, Bool.false_eq_true, ↓reduceIte,
          siteExcursionWeight, if_pos hz, List.foldl_nil] using ih (some [z]) n
      · simpa only [nestedSiteCounterRun, List.foldl_cons, nestedSiteCounterStep,
          List.headD_cons, List.tail_cons, Bool.false_eq_true, ↓reduceIte,
          siteExcursionWeight, if_neg hz] using ih none n
    | some pre =>
      change nestedSiteCounterValue (nestedSiteCounterRun ((K, C) :: levels)
        (nestedSiteCounterStep ((K, C) :: levels)
          ((true, n) :: nestedSiteCounterRun levels (nestedSiteCounterInitial levels) pre) z)
        sites) = _
      simp only [nestedSiteCounterStep, List.headD_cons, List.tail_cons, ↓reduceIte, happ]
      by_cases hz : z ∈ C
      · simpa only [if_pos hz, siteExcursionWeight] using ih (some (pre ++ [z])) n
      · simpa only [if_neg hz, siteExcursionWeight, hweight, Nat.add_assoc] using
          ih none (n + weight (pre ++ [z]))

/-- Simultaneous finite-state scanning equals recursively extracted site-word counting. -/
theorem nestedSiteCounter_correct (levels : List (Finset Site × Finset Site))
    (sites : List Site) :
    nestedSiteCounterValue
      (nestedSiteCounterRun levels (nestedSiteCounterInitial levels) sites) =
        nestedSiteCount levels sites := by
  induction levels generalizing sites with
  | nil =>
    cases sites with
    | nil => rfl
    | cons z sites =>
      have he : sites.foldl (nestedSiteCounterStep []) [] = [] := by
        induction sites with
        | nil => rfl
        | cons z sites ih => exact ih
      change nestedSiteCounterValue (sites.foldl (nestedSiteCounterStep []) []) = 1
      rw [he]
      rfl
  | cons level levels ih =>
    rcases level with ⟨K, C⟩
    simpa only [nestedSiteCounterInitial, List.map_cons, nestedSiteCount, Nat.zero_add] using
      nestedSiteCounter_weighted K C levels (nestedSiteCount levels) ih sites none 0

end SRWTightness
