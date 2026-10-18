import SRWTightness.Targets

namespace SRWTightness

/-- The finite visited-range maximum is attained at a lattice site, including the empty time interval. -/
theorem maxLocalTime_attained (ω : Sample) (n : ℕ) :
    ∃ x : Site, localTime ω n x = maxLocalTime ω n := by
  cases n with
  | zero => exact ⟨0, by simp [maxLocalTime, visited]⟩
  | succ n =>
    have hne : (visited ω (n + 1)).Nonempty := by
      refine ⟨position ω 0, Finset.mem_image.mpr ⟨0, ?_, rfl⟩⟩
      exact Finset.mem_range.mpr (Nat.zero_lt_succ n)
    obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup
      (visited ω (n + 1)) hne (localTime ω (n + 1))
    exact ⟨x, hx.symm⟩

/-- The implementation is the unrestricted maximum over all of Z², not only an upper bound. -/
theorem maxLocalTime_isGreatest (ω : Sample) (n : ℕ) :
    IsGreatest (Set.range (localTime ω n)) (maxLocalTime ω n) := by
  refine ⟨maxLocalTime_attained ω n, ?_⟩
  rintro y ⟨x, rfl⟩
  exact localTime_le_max ω n x

/-- High unrestricted maximum and existence of a high lattice site are exactly equivalent. -/
theorem maxLocalTime_threshold_iff (ω : Sample) (n k : ℕ) :
    k ≤ maxLocalTime ω n ↔ ∃ x : Site, k ≤ localTime ω n x := by
  constructor
  · intro hk
    obtain ⟨x, hx⟩ := maxLocalTime_attained ω n
    exact ⟨x, by simpa only [hx] using hk⟩
  · rintro ⟨x, hx⟩
    exact hx.trans (localTime_le_max ω n x)

/-- Source (1.1), with the half-open occupation sum, unrestricted maximum and exact centering. -/
theorem source_time_observables (ω : Sample) (n : ℕ) :
    (∀ x : Site, localTime ω n x =
      ∑ k ∈ Finset.range n, if position ω k = x then 1 else 0) ∧
    IsGreatest (Set.range (localTime ω n)) (maxLocalTime ω n) ∧
    timeCenter n = (Real.log n - Real.log (Real.log n)) / Real.sqrt Real.pi :=
  ⟨fun _ ↦ rfl, maxLocalTime_isGreatest ω n, rfl⟩

end SRWTightness
