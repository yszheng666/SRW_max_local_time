import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

namespace SRWTightness

/-- A finite set of integers above an origin is bounded by its nonnegative summable ray. -/
theorem integer_ray_finite_sum (f : ℤ → ℝ) (a : ℤ) (I : Finset ℤ)
    (hI : ∀ z ∈ I, a ≤ z) (hf : ∀ n : ℕ, 0 ≤ f (a + n))
    (hs : Summable (fun n : ℕ ↦ f (a + n))) :
    (∑ z ∈ I, f z) ≤ ∑' n : ℕ, f (a + n) := by
  classical
  let index := fun z : ℤ ↦ (z - a).toNat
  have he (z : ℤ) (hz : z ∈ I) : a + (index z : ℤ) = z := by
    dsimp [index]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr (hI z hz))]
    ring
  have hi : Set.InjOn index I := by
    intro z hz w hw hzw
    have hz' := he z hz
    have hw' := he w hw
    rw [hzw] at hz'
    exact hz'.symm.trans hw'
  calc
    _ = ∑ n ∈ I.image index, f (a + n) := by
      rw [Finset.sum_image hi]
      exact Finset.sum_congr rfl (fun z hz ↦ congrArg f (he z hz).symm)
    _ ≤ _ := hs.sum_le_tsum _ (fun n _ ↦ hf n)

end SRWTightness
