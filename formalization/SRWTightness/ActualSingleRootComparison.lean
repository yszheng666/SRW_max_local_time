import SRWTightness.ActualRecordKernel
import SRWTightness.SupportedSingleRootComparison
import SRWTightness.CompetingEntranceLaw

open MeasureTheory

namespace SRWTightness

/-- The actual exactly-one-root event retains its first entrance and exit-dependent nonreturn. -/
theorem actual_single_root_comparison {M : Type*}
    (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (F : Site → PathWord → M) (B : Set Site) (hBK : B ⊆ (K : Set Site))
    (x : Site) (hUx : ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (r : M) (c₁ c₂ η Q : ℝ) (hc₂ : 0 ≤ c₂) (hQ : 0 ≤ Q)
    (hI : c₁ ≤ setHitProbability D K x)
    (hq : ∀ y ∈ domainExitBoundary C, c₂ ≤ competingExitMass D K y)
    (hF : ∀ z ∈ B,
      Real.exp (-η) * Q ≤ pathLaw.real {ω | F z (killedPathWord C z ω) = r} ∧
      pathLaw.real {ω | F z (killedPathWord C z ω) = r} ≤ Real.exp η * Q) :
    c₁ * c₂ * Real.exp (-η) * Q ≤
      pathLaw.real {ω | (killedChildIntervals D K C x ω).length = 1 ∧
        killedChildRecords D K C x F ω = [r]} ∧
      pathLaw.real {ω | (killedChildIntervals D K C x ω).length = 1 ∧
        killedChildRecords D K C x F ω = [r]} ≤ Real.exp η * Q := by
  have hk := actual_ordered_record_kernel_with_count D K C hKC hCD F [r] x
  simp only [List.length_singleton] at hk
  rw [hk]
  change c₁ * c₂ * Real.exp (-η) * Q ≤
    singleRootRecordWeight (competingEntranceLaw D K x)
      (fun z ↦ recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r)
      (competingExitMass D K) ∧ _
  apply supported_single_root_record_comparison (competingEntranceLaw D K x)
    (fun z ↦ recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r)
    (fun _ ↦ inferInstance) B (domainExitBoundary C) hUx ?_
    (competingExitMass D K) c₁ c₂ η Q hc₂ hQ ?_ ?_ ?_
  · intro z hz
    exact recordExitSlice_supported C z (hKC (hBK hz))
      (fun ω ↦ F z (killedPathWord C z ω)) r
  · constructor
    · rw [competingEntranceLaw_mass D K (hKC.trans hCD)]
      exact hI
    · have hh := competing_entrance_exit_mass D K x
      have hnon : 0 ≤ competingExitMass D K x := measureReal_nonneg
      linarith
  · intro y hy
    refine ⟨hq y hy, ?_⟩
    have hh := competing_entrance_exit_mass D K y
    have hnon : 0 ≤ (competingEntranceLaw D K y).real Set.univ := measureReal_nonneg
    linarith
  · intro z hz
    rw [recordExitSlice_mass]
    exact hF z hz

end SRWTightness
