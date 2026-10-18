import SRWTightness.CapacityInverseFlatness
import SRWTightness.SourceTerminalGreenFlatness
import SRWTightness.DiskCapacityLogBound

namespace SRWTightness

/-- Buffered annulus capacity with a uniform inverse-radius error. -/
theorem buffered_annulus_capacity (hinput : PotentialKernelAsymptoticInput) :
    ∃ L T : ℝ, 0 ≤ L ∧ 8 ≤ T ∧ ∀ m H : ℝ,
      T ≤ m → 0 ≤ H → H ≤ m / 2 → ∀ b : Site,
      ∃ δ : ℝ, |δ| ≤ L / m ∧
        capacity (translateFinset b (diskFinset (Real.exp 1 * m + H)))
          (translateFinset b (diskFinset (m - H))) =
        ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)) + δ)⁻¹ := by
  obtain ⟨L, T, hL, hT, hg⟩ := source_terminal_green_flatness hinput
  refine ⟨L, T, hL, hT, ?_⟩
  intro m H hm hH hHm b
  rw [capacity_translate]
  have hr : 4 ≤ m - H := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hm0 : 0 ≤ m := by linarith
  have hKD := diskFinset_mono (m - H) (Real.exp 1 * m + H)
    (by linarith) (by nlinarith)
  apply capacity_eq_inverse_with_error _ _ hKD 0
    (zero_mem_diskFinset _ (by linarith))
  intro x hx hcharge
  have hlo := disk_equilibrium_support_lower _ (m - H) (by linarith) hKD x hcharge
  have hhi := (mem_diskFinset (m - H) x).mp hx
  change normSq x < (m - H) ^ 2 at hhi
  have hs := Real.sq_sqrt (normSq_nonneg x)
  have hn := Real.sqrt_nonneg (normSq x)
  have hxrad : m - H - 1 ≤ Real.sqrt (normSq (x - 0)) ∧
      Real.sqrt (normSq (x - 0)) ≤ m - H + 1 := by
    simp only [sub_zero]
    constructor <;> nlinarith
  have hy : Real.sqrt (normSq ((0 : Site) - 0)) ≤ 3 * (0 : ℝ) / 2 + 1 := by
    simp [normSq]
  have hh := hg m H 0 hm hH hHm le_rfl (by linarith) 0 x 0 hxrad hy
  simpa [translateFinset] using hh

end SRWTightness
