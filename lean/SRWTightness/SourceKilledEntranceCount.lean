import SRWTightness.SourceTraversalEntranceCount
import SRWTightness.ChildCompletionWitness

open MeasureTheory

namespace SRWTightness

/-- Inward entrance times strictly before the actual killed walk's exit. -/
noncomputable def killedChildEntranceTimes (D K C : Finset Site) (x : Site)
    (ω : Sample) : List ℕ :=
  scanChildEntrances K C x ω none (List.range (domainSteps D x ω))

/-- A final position outside the outer set creates no additional entrance. -/
theorem scanChildEntrances_append_outside (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (ts : List ℕ) (e : ℕ) (he : x + position ω e ∉ C)
    (s : Option ℕ) :
    scanChildEntrances K C x ω s (ts ++ [e]) = scanChildEntrances K C x ω s ts := by
  have heK : x + position ω e ∉ K := fun h ↦ he (hKC h)
  induction ts generalizing s with
  | nil => cases s <;> simp [scanChildEntrances, heK, he]
  | cons i ts ih =>
    cases s with
    | none =>
      by_cases hi : x + position ω i ∈ K
      · simp only [List.cons_append, scanChildEntrances, if_pos hi, ih]
      · simp only [List.cons_append, scanChildEntrances, if_neg hi, ih]
    | some a =>
      by_cases hi : x + position ω i ∈ C
      · simp only [List.cons_append, scanChildEntrances, not_false_eq_true, hi, if_false, ih]
      · simp only [List.cons_append, scanChildEntrances, hi, not_false_eq_true, if_true, ih]

/-- An entrance scan depends only on the positions at its inspected times. -/
theorem scanChildEntrances_congr (K C : Finset Site) (x : Site) (ω ω' : Sample)
    (ts : List ℕ) (s : Option ℕ)
    (hpos : ∀ i ∈ ts, position ω i = position ω' i) :
    scanChildEntrances K C x ω s ts = scanChildEntrances K C x ω' s ts := by
  revert s hpos
  induction ts with
  | nil => intro s hpos; rfl
  | cons i ts ih =>
    intro s hpos
    have hi := hpos i List.mem_cons_self
    have ht : ∀ j ∈ ts, position ω j = position ω' j :=
      fun j hj ↦ hpos j (List.mem_cons_of_mem _ hj)
    cases s <;> simp only [scanChildEntrances, hi] <;>
      split_ifs <;> simp only [ih _ ht]

/-- The finite killed word records exactly all entrances before exit when the outer set is nested. -/
theorem wordChildEntranceTimes_killed_eq (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    wordChildEntranceTimes K C x (killedPathWord D x ω) =
      killedChildEntranceTimes D K C x ω := by
  have he := killedPathWord_endpoint_outside_child D C hCD x ω hfin
  unfold wordChildEntranceTimes
  rw [List.range_succ, scanChildEntrances_append_outside K C hKC x
    (wordPath (killedPathWord D x ω)) _ _ he none]
  unfold killedChildEntranceTimes
  apply scanChildEntrances_congr
  intro i hi
  exact killedPathWord_position D x ω i (List.mem_range.mp hi).le

/-- Every inward entrance before killed exit has its completed interval in the finite extractor. -/
theorem killedChildIntervals_length_eq_entrances (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    (killedChildIntervals D K C x ω).length =
      (killedChildEntranceTimes D K C x ω).length := by
  unfold killedChildIntervals
  rw [wordChildIntervals_length_eq_entrances K C hKC x _
    (killedPathWord_endpoint_outside_child D C hCD x ω hfin),
    wordChildEntranceTimes_killed_eq D K C hKC hCD x ω hfin]

/-- The complete-count and full entrance-count conventions agree almost surely in nested domains. -/
theorem killedChildIntervals_length_eq_entrances_ae (D K C : Finset Site)
    (hKC : K ⊆ C) (hCD : C ⊆ D) (x : Site) :
    ∀ᵐ ω ∂pathLaw, (killedChildIntervals D K C x ω).length =
      (killedChildEntranceTimes D K C x ω).length := by
  filter_upwards [domainExit_ne_top_ae D x] with ω hfin
  exact killedChildIntervals_length_eq_entrances D K C hKC hCD x ω hfin

end SRWTightness
