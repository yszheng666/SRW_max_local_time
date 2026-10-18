import SRWTightness.ActualRecordLeaves
import SRWTightness.SourceTerminalVisits

namespace SRWTightness

/-- Source entrance domains indexed backwards from the terminal generation. -/
noncomputable def sourceTreeEntrance (m r : ℝ) (ℓ : ℕ) (b : Site) (n : ℕ) : Finset Site :=
  sourceEntranceDomain m r ℓ b (ℓ - (n + 1))

/-- Source exit domains indexed backwards from the terminal generation. -/
noncomputable def sourceTreeExit (m r : ℝ) (ℓ : ℕ) (b : Site) (n : ℕ) : Finset Site :=
  sourceExitDomain m r ℓ b (ℓ - (n + 1))

/-- Reversing the finite tree's domain indices gives exactly the original source levels. -/
theorem source_tree_levels (m r : ℝ) (ℓ : ℕ) (b : Site) (n k : ℕ) (hn : k + n = ℓ) :
    actualRecordLevels (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b) n =
      sourceExcursionLevels m r ℓ b k n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have hk : ℓ - (n + 1) = k := by omega
    simp only [actualRecordLevels, sourceTreeEntrance, sourceTreeExit, hk,
      sourceExcursionLevels]
    rw [ih (k + 1) (by omega)]

/-- The actual source tree has precisely the ordered projected terminal records of the manuscript. -/
theorem source_record_tree_leaves {M : Type*} (m r : ℝ) (ℓ k : ℕ) (hk : k ≤ ℓ)
    (b : Site) (D : Finset Site) (x : Site) (F : Site → PathWord → M) (ω : Sample) :
    finiteRecordLeaves (ℓ - k)
      (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        F (ℓ - k) x (killedPathWord D x ω)) =
      (sourceTerminalRecords m r ℓ k b D x ω).map (fun q ↦ F q.1 q.2) := by
  rw [actualFiniteWordRecord_leaves, source_tree_levels m r ℓ b (ℓ - k) k (by omega)]
  rfl

/-- Summing the actual source tree's terminal visit observations recovers every original visit. -/
theorem source_record_tree_visit_sum (m r : ℝ) (ℓ k : ℕ) (hk : k < ℓ)
    (b : Site) (D K : Finset Site) (x : Site) (hr : 0 ≤ r)
    (hm : sourceRecordBuffer r + 2 ≤ m)
    (hK : K ⊆ translateFinset b (diskFinset (m - sourceRecordBuffer r - 2)))
    (hroot : sourceExitDomain m r ℓ b k ⊆ D)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (y : Site) (hy : y ∈ K) :
    (finiteRecordLeaves (ℓ - k)
      (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        (fun z w ↦ localTime (wordPath w) w.length (y - z)) (ℓ - k) x
        (killedPathWord D x ω))).sum = domainLocalTime D x y ω := by
  rw [source_record_tree_leaves m r ℓ k hk.le]
  exact (source_terminal_visit_identity m r ℓ k hk b D K x hr hm hK hroot ω hfin y hy).symm

end SRWTightness
