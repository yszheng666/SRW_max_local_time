import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped ENNReal

namespace SRWTightness

/-- Distinct completion times convert a finite reward list into a nonnegative time series. -/
theorem completion_list_sum_eq_tsum (ts : List ℕ) (ht : ts.Nodup) (f : ℕ → ℝ≥0∞) :
    (ts.map f).sum = ∑' n, if n ∈ ts then f n else 0 := by
  classical
  rw [← List.sum_toFinset f ht]
  rw [sum_eq_tsum_indicator]
  simp only [Set.indicator_apply, Finset.mem_coe, List.mem_toFinset]

end SRWTightness
