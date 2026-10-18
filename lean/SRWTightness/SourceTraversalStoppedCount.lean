import SRWTightness.SourceTraversalScanSpec
import SRWTightness.SourceKilledEntranceCount

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The literal infinite entrance-indicator sum, retaining the actual extended exit time. -/
noncomputable def sourceTraversalStoppedCount (D K C : Finset Site) (x : Site)
    (ω : Sample) : ℝ≥0∞ :=
  ∑' i : ℕ, if sourceTraversalSigma K C x ω 0 i < domainExit D x ω then 1 else 0

/-- Before a finite exit, the source stopping sequence has exactly the scanner's
entrance indices. -/
theorem sourceTraversalSigma_lt_exit_iff (D K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (i : ℕ) :
    sourceTraversalSigma K C x ω 0 i < domainExit D x ω ↔
      i < (killedChildEntranceTimes D K C x ω).length := by
  rw [← coe_domainSteps D x ω hfin]
  have hs := (scanChildEntrances_range_spec K C hKC x ω 0 (domainSteps D x ω)).1
  have hc := sourceTraversalListSpec_cutoff K C x ω _ _ _ hs i
  simpa [killedChildEntranceTimes, List.range_eq_range'] using hc

/-- The infinite source indicator sum equals the full finite pre-exit entrance count. -/
theorem sourceTraversalStoppedCount_eq_entrances (D K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    sourceTraversalStoppedCount D K C x ω =
      ((killedChildEntranceTimes D K C x ω).length : ℝ≥0∞) := by
  unfold sourceTraversalStoppedCount
  simp_rw [sourceTraversalSigma_lt_exit_iff D K C hKC x ω hfin]
  rw [tsum_eq_sum
    (f := fun i : ℕ ↦ if i < (killedChildEntranceTimes D K C x ω).length
      then (1 : ℝ≥0∞) else 0)
    (s := Finset.range (killedChildEntranceTimes D K C x ω).length)
    (fun i hi ↦ by simp only [Finset.mem_range] at hi; simp [hi])]
  calc
    _ = ∑ _i ∈ Finset.range (killedChildEntranceTimes D K C x ω).length,
        (1 : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact if_pos (Finset.mem_range.mp hi)
    _ = _ := by simp

/-- Complete child intervals equal the source's literal stopping-time count in nested domains. -/
theorem sourceTraversalStoppedCount_eq_complete (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    sourceTraversalStoppedCount D K C x ω =
      ((killedChildIntervals D K C x ω).length : ℝ≥0∞) := by
  rw [sourceTraversalStoppedCount_eq_entrances D K C hKC x ω hfin,
    killedChildIntervals_length_eq_entrances D K C hKC hCD x ω hfin]

/-- The source stopping-time count agrees almost surely with the complete finite extractor. -/
theorem sourceTraversalStoppedCount_eq_complete_ae (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) (x : Site) :
    ∀ᵐ ω ∂pathLaw, sourceTraversalStoppedCount D K C x ω =
      ((killedChildIntervals D K C x ω).length : ℝ≥0∞) := by
  filter_upwards [domainExit_ne_top_ae D x] with ω hfin
  exact sourceTraversalStoppedCount_eq_complete D K C hKC hCD x ω hfin

end SRWTightness
