import SRWTightness.SiteListWord
import Mathlib.Data.List.Chain

namespace SRWTightness

/-- Consecutive actual positions in a deterministic time interval. -/
def siteRange (x : Site) (ω : Sample) (a n : ℕ) : List Site :=
  (List.range' a n).map (fun i ↦ x + position ω i)

/-- Inspecting a nonempty interval starts at its first position. -/
theorem site_range_cons (x : Site) (ω : Sample) (a n : ℕ) :
    siteRange x ω a (n + 1) = (x + position ω a) :: siteRange x ω (a + 1) n := by
  simp [siteRange, List.range'_succ]

/-- Appending the next position extends the actual site interval by one. -/
theorem site_range_snoc (x : Site) (ω : Sample) (a n : ℕ) :
    siteRange x ω a (n + 1) = siteRange x ω a n ++ [x + position ω (a + n)] := by
  simp [siteRange, List.range'_1_concat]

/-- The range and finite-function presentations of consecutive sites agree. -/
theorem site_range_eq_ofFn (x : Site) (ω : Sample) (a n : ℕ) :
    siteRange x ω a n = List.ofFn (fun i : Fin n ↦ x + position ω (a + i.val)) := by
  apply List.ext_getElem
  · simp [siteRange]
  · intro i hi hj
    simp [siteRange]

/-- Every two successive sites in the actual interval are joined by the actual SRW step. -/
theorem site_range_is_chain (x : Site) (ω : Sample) (a n : ℕ) :
    List.IsChain (fun p z ↦ ∃ d : Direction, p + step d = z) (siteRange x ω a n) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  refine ⟨ω (a + i), ?_⟩
  simp only [siteRange, List.getElem_map, List.getElem_range', Nat.one_mul]
  rw [← Nat.add_assoc]
  change (x + position ω (a + i)) + step (ω (a + i)) =
    x + (position ω (a + i) + step (ω (a + i)))
  exact add_assoc _ _ _

/-- Decoding the sites of a finite segment gives its actual direction word. -/
theorem site_list_word_range (x : Site) (ω : Sample) (a n : ℕ) :
    siteListWord (siteRange x ω a (n + 1)) =
      (⟨n, fun k ↦ ω (a + k.val)⟩ : PathWord) := by
  rw [site_range_eq_ofFn]
  exact site_list_word_actual_segment x ω a n

end SRWTightness
