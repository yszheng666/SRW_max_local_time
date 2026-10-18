import SRWTightness.SourceDiskObservables

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Literal stopped occupation over every time strictly before exit, retaining infinity on exceptional paths. -/
noncomputable def sourceStoppedLocalTime (R : ℝ) (ω : Sample) (x : Site) : ℝ≥0∞ :=
  ∑' k : ℕ, if (k : WithTop ℕ) < exitTime R ω ∧ position ω k = x then 1 else 0

/-- Literal unrestricted stopped maximum, with the extended nonnegative value retained. -/
noncomputable def sourceStoppedMaximum (R : ℝ) (ω : Sample) : ℝ≥0∞ :=
  ⨆ x : Site, sourceStoppedLocalTime R ω x

/-- On every finite-exit path the infinite stopped sum is exactly the implemented finite occupation. -/
theorem sourceStoppedLocalTime_eq_of_finite (R : ℝ) (ω : Sample)
    (hfin : exitTime R ω ≠ ⊤) (x : Site) :
    sourceStoppedLocalTime R ω x = (localTime ω (exitSteps R ω) x : ℝ≥0∞) := by
  classical
  unfold sourceStoppedLocalTime
  have hcond (k : ℕ) : (k : WithTop ℕ) < exitTime R ω ↔ k < exitSteps R ω := by
    constructor
    · intro hk
      rw [← coe_exitSteps R ω hfin] at hk
      exact WithTop.coe_lt_coe.mp hk
    · intro hk
      rw [← coe_exitSteps R ω hfin]
      exact WithTop.coe_lt_coe.mpr hk
  simp_rw [hcond]
  rw [tsum_eq_sum (f := fun k : ℕ ↦
    if k < exitSteps R ω ∧ position ω k = x then (1 : ℝ≥0∞) else 0)
    (s := Finset.range (exitSteps R ω)) (fun k hk ↦ by
    have hh : ¬ k < exitSteps R ω := by simpa only [Finset.mem_range] using hk
    simp only [hh, false_and, if_false])]
  unfold localTime
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hh := Finset.mem_range.mp hk
  by_cases he : position ω k = x <;> simp [hh, he]

/-- On finite-exit paths the extended unrestricted supremum equals the actual finite disk maximum. -/
theorem sourceStoppedMaximum_eq_of_finite (R : ℝ) (ω : Sample)
    (hfin : exitTime R ω ≠ ⊤) :
    sourceStoppedMaximum R ω = (diskMax R ω : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    rw [sourceStoppedLocalTime_eq_of_finite R ω hfin x]
    exact_mod_cast localTime_le_max ω (exitSteps R ω) x
  · obtain ⟨x, hx⟩ := maxLocalTime_attained ω (exitSteps R ω)
    calc
      (diskMax R ω : ℝ≥0∞) = sourceStoppedLocalTime R ω x := by
        rw [sourceStoppedLocalTime_eq_of_finite R ω hfin x, hx]
        rfl
      _ ≤ sourceStoppedMaximum R ω := le_iSup (sourceStoppedLocalTime R ω) x

/-- The literal source stopped sums and unrestricted maximum agree almost surely with the finite implementation. -/
theorem source_stopped_observables_ae (R : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ ω ∂pathLaw,
      (∀ x : Site, sourceStoppedLocalTime R ω x = (localTime ω (exitSteps R ω) x : ℝ≥0∞)) ∧
      sourceStoppedMaximum R ω = (diskMax R ω : ℝ≥0∞) := by
  filter_upwards [exitTime_ne_top_ae hR] with ω hfin
  exact ⟨sourceStoppedLocalTime_eq_of_finite R ω hfin,
    sourceStoppedMaximum_eq_of_finite R ω hfin⟩

end SRWTightness
