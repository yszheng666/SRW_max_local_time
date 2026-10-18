import SRWTightness.StoppedUniformTimeGrid
import SRWTightness.DyadicTimeApproximation

open Filter
open scoped Topology
namespace SRWTightness

/-- The dyadic uniform grid approximates every point of a nondegenerate closed interval. -/
theorem stoppedUniformTimeGrid_dyadic_tendsto (a b t : ℝ) (hab : a < b)
    (ht : t ∈ Set.Icc a b) :
    Tendsto (fun n ↦ stoppedUniformTimeGrid a b (2 ^ n)
      (dyadicTimeIndex n ((t - a) / (b - a)))) atTop (nhds t) := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hu0 : 0 ≤ (t - a) / (b - a) := div_nonneg (sub_nonneg.mpr ht.1) hgap.le
  have hu1 : (t - a) / (b - a) ≤ 1 := (div_le_one hgap).mpr (by linarith [ht.2])
  have he (n : ℕ) : stoppedUniformTimeGrid a b (2 ^ n)
      (dyadicTimeIndex n ((t - a) / (b - a))) =
      a + (b - a) * dyadicTime n ((t - a) / (b - a)) := by
    rw [stoppedUniformTimeGrid_of_le _ _ _ _ (dyadicTimeIndex_le n _ hu1)]
    unfold dyadicTime
    push_cast
    ring
  simp_rw [he]
  have hlim : Tendsto (fun n ↦ a + (b - a) * dyadicTime n ((t - a) / (b - a)))
      atTop (nhds (a + (b - a) * ((t - a) / (b - a)))) :=
    tendsto_const_nhds.add
      (tendsto_const_nhds.mul (dyadicTime_tendsto ((t - a) / (b - a)) hu0))
  convert hlim using 1 <;> try rfl
  field_simp
  <;> ring

end SRWTightness
