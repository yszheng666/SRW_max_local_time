import SRWTightness.DiskGreenEnergyBounds
import SRWTightness.EquilibriumBoundarySupport

open Finset

namespace SRWTightness

theorem diskFinset_mono (a R : ℝ) (ha : 0 ≤ a) (haR : a ≤ R) : diskFinset a ⊆ diskFinset R := by
  intro x hx
  rw [mem_diskFinset] at hx ⊢
  change normSq x < R ^ 2
  have hx' : normSq x < a ^ 2 := hx
  nlinarith

theorem zero_mem_diskFinset (a : ℝ) (ha : 0 < a) : (0 : Site) ∈ diskFinset a := by
  rw [mem_diskFinset]
  change normSq 0 < a ^ 2
  simp only [normSq, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, zero_pow (by omega : 2 ≠ 0), zero_add]
  positivity

theorem capacity_inverse_disk_log_bound (R a : ℝ) (ha : 1 ≤ a) (hRa : 2 * a ≤ R) :
    |1 / capacity (diskFinset R) (diskFinset a) - (2 / Real.pi) * Real.log (R / a)| ≤
      diskGreenEnergyConstant := by
  have hKD := diskFinset_mono a R (by linarith) (by linarith)
  have hz := zero_mem_diskFinset a (by linarith)
  have hne : (diskFinset a).Nonempty := ⟨0, hz⟩
  have hsum : (∑ x ∈ diskFinset a, equilibriumWeight (diskFinset R) (diskFinset a) x * diskGreen R 0 x) =
      1 / capacity (diskFinset R) (diskFinset a) := by
    calc
      _ = ∑ x ∈ diskFinset a, equilibriumWeight (diskFinset R) (diskFinset a) x * killedGreen (diskFinset R) x 0 := by
        apply sum_congr rfl
        intro x hx
        rw [diskGreen, killedGreen_symm _ 0 x (hKD hz) (hKD hx)]
      _ = _ := equilibriumWeight_green _ _ hKD 0 hz
  have hl : (∑ x ∈ diskFinset a, equilibriumWeight (diskFinset R) (diskFinset a) x *
      ((2 / Real.pi) * Real.log (R / a) - diskGreenEnergyConstant)) ≤
      ∑ x ∈ diskFinset a, equilibriumWeight (diskFinset R) (diskFinset a) x * diskGreen R 0 x := by
    apply sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left (diskGreen_inner_lower R a ha hRa x ((mem_diskFinset a x).mp hx))
      (equilibriumWeight_nonneg _ _ _)
  have hu : (∑ x ∈ diskFinset a, equilibriumWeight (diskFinset R) (diskFinset a) x * diskGreen R 0 x) ≤
      ∑ x ∈ diskFinset a, equilibriumWeight (diskFinset R) (diskFinset a) x *
        ((2 / Real.pi) * Real.log (R / a) + diskGreenEnergyConstant) := by
    apply sum_le_sum
    intro x hx
    by_cases he : equilibriumMeasure (diskFinset R) (diskFinset a) x = 0
    · simp [equilibriumWeight, he]
    · apply mul_le_mul_of_nonneg_left _ (equilibriumWeight_nonneg _ _ _)
      by_cases ha2 : 2 ≤ a
      · exact diskGreen_inner_shell_upper R a ha2 hRa x ((mem_diskFinset a x).mp hx)
          (disk_equilibrium_support_lower _ a ha2 hKD x he)
      · apply diskGreen_inner_radius_upper R a ha hRa x ((mem_diskFinset a x).mp hx)
        have hh := le_max_right (Real.sqrt (normSq x)) (1 : ℝ)
        linarith
  rw [← sum_mul, equilibriumWeight_sum _ _ hKD hne, one_mul, hsum] at hl
  rw [← sum_mul, equilibriumWeight_sum _ _ hKD hne, one_mul, hsum] at hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SRWTightness
