import SRWTightness.Law
import SRWTightness.Geometry
import Mathlib.Probability.Process.HittingTime

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The disk is open; only positive radii are used in the main results. -/
def disk (R : ℝ) : Set Site := {x | normSq x < R ^ 2}

/-- First exit, with infinity retained on paths which never exit. -/
noncomputable def exitTime (R : ℝ) : Sample → WithTop ℕ :=
  hittingAfter (fun n ω ↦ position ω n) (disk R)ᶜ 0

theorem exitTime_le_iff (R : ℝ) (ω : Sample) (n : ℕ) :
    exitTime R ω ≤ n ↔ ∃ k ≤ n, R ^ 2 ≤ normSq (position ω k) := by
  simpa [exitTime, disk] using
    (hittingAfter_le_iff (u := fun k ω ↦ position ω k) (s := (disk R)ᶜ)
      (n := 0) (i := n) (ω := ω))

theorem before_exit_mem (R : ℝ) (ω : Sample) (n : ℕ)
    (h : (n : WithTop ℕ) < exitTime R ω) : position ω n ∈ disk R := by
  by_contra hn
  have he : exitTime R ω ≤ n :=
    (exitTime_le_iff R ω n).mpr ⟨n, le_rfl, by simpa [disk] using hn⟩
  exact (not_le_of_gt h) he

/-- Once exit is finite, its half-open maximum is the ordinary finite-time maximum. -/
noncomputable def diskMax (R : ℝ) (ω : Sample) : ℕ :=
  maxLocalTime ω ((exitTime R ω).untopD 0)

/-- No probability assumption is used in the pathwise comparison. -/
theorem max_time_sandwich (ω : Sample) (n t₁ t₂ : ℕ)
    (h₁ : t₁ ≤ n) (h₂ : n ≤ t₂) :
    maxLocalTime ω t₁ ≤ maxLocalTime ω n ∧
      maxLocalTime ω n ≤ maxLocalTime ω t₂ :=
  ⟨maxLocalTime_mono ω h₁, maxLocalTime_mono ω h₂⟩

end SRWTightness
