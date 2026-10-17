import SRWTightness.SourceTraversalStopping
import SRWTightness.SourceTraversalEntranceCount

namespace SRWTightness

/-- A finite list contains successive inward hits up to a strict observation cutoff. -/
def SourceTraversalListSpec (K C : Finset Site) (x : Site) (ω : Sample) (limit : ℕ)
    (start : WithTop ℕ) : List ℕ → Prop
  | [] => ¬ sourceFirstHit (fun n ↦ x + position ω n ∈ K) start < limit
  | a :: as => sourceFirstHit (fun n ↦ x + position ω n ∈ K) start = a ∧
      a < limit ∧ SourceTraversalListSpec K C x ω limit
        (sourceFirstHit (fun n ↦ x + position ω n ∉ C) a) as

/-- Only the first inward hit, rather than the preceding search interval, affects the list spec. -/
theorem sourceTraversalListSpec_congr (K C : Finset Site) (x : Site) (ω : Sample)
    (limit : ℕ) (s t : WithTop ℕ) (ts : List ℕ)
    (h : sourceFirstHit (fun n ↦ x + position ω n ∈ K) s =
      sourceFirstHit (fun n ↦ x + position ω n ∈ K) t) :
    SourceTraversalListSpec K C x ω limit s ts ↔
      SourceTraversalListSpec K C x ω limit t ts := by
  cases ts <;> simp only [SourceTraversalListSpec, h]

/-- A chronological scan obeys the unbounded first-hit recursion in either scanner state. -/
theorem scanChildEntrances_range_spec (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (start n : ℕ) :
    SourceTraversalListSpec K C x ω (start + n) start
        (scanChildEntrances K C x ω none (List.range' start n)) ∧
      ∀ a, SourceTraversalListSpec K C x ω (start + n)
        (sourceFirstHit (fun i ↦ x + position ω i ∉ C) start)
        (scanChildEntrances K C x ω (some a) (List.range' start n)) := by
  induction n generalizing start with
  | zero =>
    constructor
    · simpa [SourceTraversalListSpec, scanChildEntrances] using
        not_lt_of_ge (sourceFirstHit_start_le (fun i ↦ x + position ω i ∈ K) start)
    · intro a
      simpa [SourceTraversalListSpec, scanChildEntrances] using
        not_lt_of_ge ((sourceFirstHit_start_le (fun i ↦ x + position ω i ∉ C) start).trans
          (sourceFirstHit_start_le (fun i ↦ x + position ω i ∈ K)
            (sourceFirstHit (fun i ↦ x + position ω i ∉ C) start)))
  | succ n ih =>
    have h := ih (start + 1)
    have he : start + 1 + n = start + (n + 1) := by omega
    rw [he] at h
    constructor
    · by_cases hk : x + position ω start ∈ K
      · rw [List.range'_succ, scanChildEntrances, if_pos hk]
        refine ⟨sourceFirstHit_eq_of_mem _ start hk, by omega, ?_⟩
        rw [sourceFirstHit_succ_of_not_mem (fun i ↦ x + position ω i ∉ C) start
          (by simpa using hKC hk)]
        exact h.2 start
      · rw [List.range'_succ, scanChildEntrances, if_neg hk]
        exact (sourceTraversalListSpec_congr K C x ω _ start (↑(start + 1)) _
          (sourceFirstHit_succ_of_not_mem _ start hk)).mpr h.1
    · intro a
      by_cases hc : x + position ω start ∈ C
      · simp only [List.range'_succ, scanChildEntrances, hc, not_true_eq_false, if_false]
        rw [sourceFirstHit_succ_of_not_mem (fun i ↦ x + position ω i ∉ C) start
          (by simpa using hc)]
        exact h.2 a
      · simp only [List.range'_succ, scanChildEntrances, hc, not_false_eq_true, if_true]
        rw [sourceFirstHit_eq_of_mem (fun i ↦ x + position ω i ∉ C) start hc]
        exact (sourceTraversalListSpec_congr K C x ω _ start (↑(start + 1)) _
          (sourceFirstHit_succ_of_not_mem _ start (fun hk ↦ hc (hKC hk)))).mpr h.1

/-- The strict cutoff holds precisely for indices within a list satisfying the
stopping recursion. -/
theorem sourceTraversalListSpec_cutoff (K C : Finset Site) (x : Site) (ω : Sample)
    (limit : ℕ) (ts : List ℕ) (start : WithTop ℕ)
    (hs : SourceTraversalListSpec K C x ω limit start ts) (i : ℕ) :
    sourceTraversalSigma K C x ω start i < limit ↔ i < ts.length := by
  induction ts generalizing start i with
  | nil =>
    have hn : ¬ sourceTraversalSigma K C x ω start i < limit := by
      exact not_lt_of_ge ((not_lt.mp hs).trans
        (sourceTraversalSigma_first_le K C x ω i start))
    simp [hn]
  | cons a as ih =>
    obtain ⟨ha, halt, ht⟩ := hs
    cases i with
    | zero => simp [sourceTraversalSigma, ha, halt]
    | succ i =>
      simp only [sourceTraversalSigma, ha, List.length_cons, Nat.succ_lt_succ_iff]
      exact ih _ ht i

end SRWTightness
