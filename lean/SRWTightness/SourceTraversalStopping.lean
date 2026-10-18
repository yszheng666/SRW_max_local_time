import SRWTightness.SetHitting

open MeasureTheory

namespace SRWTightness

/-- The first natural time satisfying a predicate after an extended starting time. -/
noncomputable def sourceFirstHit (P : ℕ → Prop) (start : WithTop ℕ) : WithTop ℕ :=
  if h : start = ⊤ then ⊤ else
    hittingAfter (fun n (_ : Unit) ↦ n) {n | P n} (start.untop h) ()

/-- Starting at infinity cannot produce a finite hitting time. -/
theorem sourceFirstHit_top (P : ℕ → Prop) : sourceFirstHit P ⊤ = ⊤ := by
  simp [sourceFirstHit]

/-- At a finite starting time the definition is the usual unbounded hitting infimum. -/
theorem sourceFirstHit_coe (P : ℕ → Prop) (start : ℕ) :
    sourceFirstHit P start = hittingAfter (fun n (_ : Unit) ↦ n) {n | P n} start () := by
  rfl

/-- A finite upper bound is equivalent to a witness between the start and that bound. -/
theorem sourceFirstHit_le_iff (P : ℕ → Prop) (start : WithTop ℕ) (n : ℕ) :
    sourceFirstHit P start ≤ n ↔ ∃ j : ℕ, start ≤ j ∧ j ≤ n ∧ P j := by
  by_cases hs : start = ⊤
  · subst start
    simp [sourceFirstHit_top]
  · lift start to ℕ using hs with a
    simpa [sourceFirstHit_coe, Set.mem_Icc, WithTop.coe_le_coe, and_assoc] using
      (hittingAfter_le_iff (u := fun n (_ : Unit) ↦ n) (s := {n | P n})
        (n := a) (i := n) (ω := ()))

/-- A hitting time never precedes its extended starting time. -/
theorem sourceFirstHit_start_le (P : ℕ → Prop) (start : WithTop ℕ) :
    start ≤ sourceFirstHit P start := by
  by_cases hs : start = ⊤
  · subst start
    simp [sourceFirstHit_top]
  · lift start to ℕ using hs with a
    simpa [sourceFirstHit_coe] using
      (le_hittingAfter (u := fun n (_ : Unit) ↦ n) (s := {n | P n}) (n := a) ())

/-- Delaying the starting time can only delay the first hit. -/
theorem sourceFirstHit_mono (P : ℕ → Prop) {s t : WithTop ℕ} (hst : s ≤ t) :
    sourceFirstHit P s ≤ sourceFirstHit P t := by
  by_cases ht : sourceFirstHit P t = ⊤
  · simp [ht]
  · lift sourceFirstHit P t to ℕ using ht with n hn
    obtain ⟨j, htj, hjn, hpj⟩ :=
      (sourceFirstHit_le_iff P t n).mp hn.ge
    exact (sourceFirstHit_le_iff P s n).mpr ⟨j, hst.trans htj, hjn, hpj⟩

/-- If the predicate holds at the starting time, the first hit is immediate. -/
theorem sourceFirstHit_eq_of_mem (P : ℕ → Prop) (n : ℕ) (hn : P n) :
    sourceFirstHit P n = n := by
  apply le_antisymm
  · exact (sourceFirstHit_le_iff P n n).mpr ⟨n, le_rfl, le_rfl, hn⟩
  · exact sourceFirstHit_start_le P n

/-- A time at which the predicate fails may be removed from the search interval. -/
theorem sourceFirstHit_succ_of_not_mem (P : ℕ → Prop) (n : ℕ) (hn : ¬ P n) :
    sourceFirstHit P n = sourceFirstHit P (↑(n + 1)) := by
  apply le_antisymm
  · exact sourceFirstHit_mono P (WithTop.coe_le_coe.mpr (Nat.le_succ n))
  · by_cases ht : sourceFirstHit P n = ⊤
    · simp [ht]
    · lift sourceFirstHit P n to ℕ using ht with k hk
      obtain ⟨j, hnj, hjk, hpj⟩ :=
        (sourceFirstHit_le_iff P n k).mp hk.ge
      have hnj' : n ≤ j := WithTop.coe_le_coe.mp hnj
      have hne : j ≠ n := fun he ↦ hn (he ▸ hpj)
      have hnext : n + 1 ≤ j := by omega
      exact (sourceFirstHit_le_iff P (↑(n + 1)) k).mpr
        ⟨j, by exact_mod_cast hnext, hjk, hpj⟩

/-- Source inward entrances, indexed from zero, with all empty infima retained as infinity. -/
noncomputable def sourceTraversalSigma (K C : Finset Site) (x : Site) (ω : Sample)
    (start : WithTop ℕ) : ℕ → WithTop ℕ
  | 0 => sourceFirstHit (fun n ↦ x + position ω n ∈ K) start
  | i + 1 => sourceTraversalSigma K C x ω
      (sourceFirstHit (fun n ↦ x + position ω n ∉ C)
        (sourceFirstHit (fun n ↦ x + position ω n ∈ K) start)) i

/-- Each source entrance is no earlier than the first entrance of the same recursion. -/
theorem sourceTraversalSigma_first_le (K C : Finset Site) (x : Site) (ω : Sample)
    (i : ℕ) (start : WithTop ℕ) :
    sourceFirstHit (fun n ↦ x + position ω n ∈ K) start ≤
      sourceTraversalSigma K C x ω start i := by
  induction i generalizing start with
  | zero => rfl
  | succ i ih =>
    exact le_trans (sourceFirstHit_start_le _ _) <|
      le_trans (sourceFirstHit_start_le _ _) (ih _)

/-- The first hit is exactly the extended infimum of all eligible natural times. -/
theorem sourceFirstHit_eq_sInf (P : ℕ → Prop) (start : WithTop ℕ) :
    sourceFirstHit P start = sInf ((fun n : ℕ ↦ (n : WithTop ℕ)) ''
      {n | start ≤ n ∧ P n}) := by
  apply le_antisymm
  · apply le_sInf
    rintro t ⟨n, ⟨hstart, hp⟩, rfl⟩
    exact (sourceFirstHit_le_iff P start n).mpr ⟨n, hstart, le_rfl, hp⟩
  · by_cases ht : sourceFirstHit P start = ⊤
    · simp [ht]
    · lift sourceFirstHit P start to ℕ using ht with n hn
      obtain ⟨j, hstart, hjn, hp⟩ := (sourceFirstHit_le_iff P start n).mp hn.ge
      have hmem : (j : WithTop ℕ) ∈ ((fun n : ℕ ↦ (n : WithTop ℕ)) ''
          {n | start ≤ n ∧ P n}) := ⟨j, ⟨hstart, hp⟩, rfl⟩
      exact (sInf_le hmem).trans (WithTop.coe_le_coe.mpr hjn)

/-- An empty set of eligible natural times gives an infinite first hit. -/
theorem sourceFirstHit_eq_top_iff (P : ℕ → Prop) (start : WithTop ℕ) :
    sourceFirstHit P start = ⊤ ↔ ∀ n : ℕ, start ≤ n → ¬ P n := by
  by_cases hs : start = ⊤
  · subst start
    simp [sourceFirstHit_top]
  · lift start to ℕ using hs with a
    simpa [sourceFirstHit_coe, WithTop.coe_le_coe] using
      (hittingAfter_eq_top_iff (u := fun n (_ : Unit) ↦ n) (s := {n | P n})
        (n := a) (ω := ()))

/-- The outer-shell visit following each source inward entrance. -/
noncomputable def sourceTraversalEta (K C : Finset Site) (x : Site) (ω : Sample)
    (start : WithTop ℕ) (i : ℕ) : WithTop ℕ :=
  sourceFirstHit (fun n ↦ x + position ω n ∉ C) (sourceTraversalSigma K C x ω start i)

/-- The recursive entrance definition is the usual next inward hit after the previous outer exit. -/
theorem sourceTraversalSigma_succ (K C : Finset Site) (x : Site) (ω : Sample)
    (i : ℕ) (start : WithTop ℕ) :
    sourceTraversalSigma K C x ω start (i + 1) =
      sourceFirstHit (fun n ↦ x + position ω n ∈ K)
        (sourceTraversalEta K C x ω start i) := by
  induction i generalizing start with
  | zero => rfl
  | succ i ih => exact ih _

/-- The complete source sigma/eta recursion, including the initial inward search from time zero. -/
theorem source_traversal_stopping (K C : Finset Site) (x : Site) (ω : Sample) :
    sourceTraversalSigma K C x ω 0 0 = sourceFirstHit (fun n ↦ x + position ω n ∈ K) 0 ∧
      ∀ i, sourceTraversalEta K C x ω 0 i =
        sourceFirstHit (fun n ↦ x + position ω n ∉ C)
          (sourceTraversalSigma K C x ω 0 i) ∧
        sourceTraversalSigma K C x ω 0 (i + 1) =
          sourceFirstHit (fun n ↦ x + position ω n ∈ K) (sourceTraversalEta K C x ω 0 i) := by
  exact ⟨rfl, fun i ↦ ⟨rfl, sourceTraversalSigma_succ K C x ω i 0⟩⟩

/-- A walk beginning in the inner set has its first inward entrance at time zero. -/
theorem sourceTraversalSigma_zero_of_start_mem (K C : Finset Site) (x : Site) (ω : Sample)
    (hx : x + position ω 0 ∈ K) : sourceTraversalSigma K C x ω 0 0 = 0 := by
  exact sourceFirstHit_eq_of_mem _ 0 hx

end SRWTightness
