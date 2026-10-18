import SRWTightness.PathWordSlice
import SRWTightness.ChildIntervalInterior
import SRWTightness.ChildIntervalOrder
import SRWTightness.ExternalStoppedWordMass

namespace SRWTightness

/-- Every emitted finite child slice is a genuine first-exit word from its child domain. -/
theorem wordChildIntervals_slice_admissible (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (w : PathWord) (q : ℕ × ℕ) (hq : q ∈ wordChildIntervals K C x w) :
    AdmissibleExitWord C (x + position (wordPath w) q.1)
      (x + position (wordPath w) q.2) (slicePathWord w q.1 q.2) := by
  have hlt : q.1 < q.2 := scanChildIntervals_start_lt_end K C x (wordPath w) _
    List.pairwise_lt_range none (by intro a h; cases h) q hq
  have hp (i : ℕ) (hi : i ≤ q.2 - q.1) :
      (x + position (wordPath w) q.1) +
        position (wordPath (slicePathWord w q.1 q.2)) i =
          x + position (wordPath w) (q.1 + i) := by
    rw [slicePathWord_position w q.1 q.2 i hi, add_assoc, ← position_add]
  refine ⟨?_, ?_, (wordChildIntervals_endpoints K C x w q hq).2⟩
  · intro i hi
    change i < q.2 - q.1 at hi
    rw [hp i hi.le]
    exact wordChildIntervals_interior K C hKC x w q hq _ (by omega) (by omega)
  · change (x + position (wordPath w) q.1) +
      position (wordPath (slicePathWord w q.1 q.2)) (q.2 - q.1) = _
    rw [hp _ le_rfl, Nat.add_sub_of_le hlt.le]

end SRWTightness
