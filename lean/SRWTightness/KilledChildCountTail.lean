import SRWTightness.KilledChildCountRenewal
import SRWTightness.SupportedRecordComparison

open MeasureTheory

namespace SRWTightness

/-- The actual count tail retains the first entrance mass and pays one return factor thereafter. -/
theorem killedChildIntervals_count_tail (D K C : Finset Site)
    (hKC : K ⊆ C) (hCD : C ⊆ D) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hreturn : ∀ ξ ∈ domainExitBoundary C, setHitProbability D K ξ ≤ ρ) :
    ∀ (n : ℕ) (x : Site),
      pathLaw.real {ω | n + 1 ≤ (killedChildIntervals D K C x ω).length} ≤
        setHitProbability D K x * ρ ^ n := by
  have hKD : K ⊆ D := fun _ hz ↦ hCD (hKC hz)
  intro n
  induction n with
  | zero =>
    intro x
    rw [killedChildIntervals_length_ge_entrance D K C hKC hCD x 0]
    have hb := integral_bounds_on_support (competingEntranceLaw D K x) (K : Set Site)
      (competingEntranceLaw_supported D K x)
      (fun z ↦ pathLaw.real {ω | 0 + 1 ≤ (killedChildIntervals D K C z ω).length})
      0 1 (by norm_num) (fun _ _ ↦ ⟨measureReal_nonneg, measureReal_le_one⟩)
    simpa only [one_mul, competingEntranceLaw_mass D K hKD x, pow_zero, mul_one] using hb.2
  | succ n ih =>
    intro x
    rw [killedChildIntervals_length_ge_entrance D K C hKC hCD x (n + 1)]
    have hzbound : ∀ z ∈ K,
        pathLaw.real {ω | n + 1 + 1 ≤ (killedChildIntervals D K C z ω).length} ≤
          ρ ^ (n + 1) := by
      intro z hz
      rw [killedChildIntervals_length_ge_inside D K C hKC hCD z hz (n + 1)]
      have hf : ∀ ξ ∈ domainExitBoundary C,
          0 ≤ pathLaw.real {ω | n + 1 ≤ (killedChildIntervals D K C ξ ω).length} ∧
            pathLaw.real {ω | n + 1 ≤ (killedChildIntervals D K C ξ ω).length} ≤
              ρ ^ (n + 1) := by
        intro ξ hξ
        refine ⟨measureReal_nonneg, (ih ξ).trans ?_⟩
        calc
          _ ≤ ρ * ρ ^ n := mul_le_mul_of_nonneg_right (hreturn ξ hξ) (pow_nonneg hρ n)
          _ = _ := by rw [pow_succ]; ring
      have hb := integral_bounds_on_support (recordExitSlice C z (fun _ ↦ ()) ())
        (domainExitBoundary C) (recordExitSlice_supported C z (hKC hz) (fun _ ↦ ()) ())
        _ 0 (ρ ^ (n + 1)) (by norm_num) hf
      simpa only [recordExitSlice_mass, Set.setOf_true, probReal_univ, mul_one] using hb.2
    have hb := integral_bounds_on_support (competingEntranceLaw D K x) (K : Set Site)
      (competingEntranceLaw_supported D K x) _ 0 (ρ ^ (n + 1)) (by norm_num)
      (fun z hz ↦ ⟨measureReal_nonneg, hzbound z hz⟩)
    simpa only [competingEntranceLaw_mass D K hKD x, mul_comm] using hb.2

end SRWTightness
