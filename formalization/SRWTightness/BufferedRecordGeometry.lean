import SRWTightness.BufferedAnnulusGeometry
import SRWTightness.RecordRadialSupport

namespace SRWTightness

/-- Buffered middle starts are strictly inside the parent and outside the inner target. -/
theorem buffered_middle_mem_annulus (ρ H : ℝ) (hH : 1 ≤ H) (hρ : 8 * H ≤ ρ)
    (b x : Site) (hx : |Real.sqrt (normSq (x - b)) - Real.exp 1 * ρ| ≤ 2 * H) :
    x ∈ translateFinset b (diskFinset (Real.exp 2 * ρ + H)) \
      translateFinset b (diskFinset (ρ - H)) := by
  have hg := buffered_middle_annulus_geometry ρ H hH hρ (x - b) hx
  have hρ0 : 0 < ρ := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have hegap : Real.exp 1 + 1 ≤ Real.exp 2 := by rw [he2]; nlinarith
  have hout : Real.exp 1 * ρ + ρ ≤ Real.exp 2 * ρ := by
    nlinarith [mul_le_mul_of_nonneg_right hegap hρ0.le]
  have hu : Real.sqrt (normSq (x - b)) < Real.exp 2 * ρ + H := by
    have hh := (abs_le.mp hx).2
    linarith
  have hs := Real.sq_sqrt (normSq_nonneg (x - b))
  have hs0 := Real.sqrt_nonneg (normSq (x - b))
  apply Finset.mem_sdiff.mpr
  constructor
  · simp only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq]
    nlinarith
  · simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq, not_lt]
      using hg.2.2.1

end SRWTightness
