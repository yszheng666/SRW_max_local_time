import SRWTightness.TranslatedDiskGeometry
import SRWTightness.DiskGreenEnergyBounds
import SRWTightness.GreenDomainDecomposition

namespace SRWTightness

theorem diskGreen_origin_log_bound (R : ℝ) (hR : 2 ≤ R) :
    |diskGreen R 0 0 - (2 / Real.pi) * Real.log R| ≤ diskGreenEnergyConstant := by
  have hz : (0 : Site) ∈ disk 1 := by norm_num [disk, normSq]
  have hl := diskGreen_inner_lower R 1 le_rfl (by linarith) 0 hz
  have hu := diskGreen_inner_radius_upper R 1 le_rfl (by linarith) 0 hz (by norm_num [normSq])
  simp only [div_one] at hl hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem diskGreen_diagonal_upper (R : ℝ) (hR : 1 ≤ R) (x : Site) (hx : x ∈ disk R) :
    diskGreen R x x ≤ (2 / Real.pi) * Real.log R +
      (diskGreenEnergyConstant + (2 / Real.pi) * Real.log 2) := by
  have hsub := disk_subset_translated_outer R (by linarith) x (show normSq x ≤ R ^ 2 from (show normSq x < R ^ 2 from hx).le)
  have hm := killedGreen_mono_domain _ _ hsub x x
  have he := killedGreen_translate x (diskFinset (2 * R)) 0 0
  simp only [add_zero] at he
  rw [he] at hm
  have hu := (abs_le.mp (diskGreen_origin_log_bound (2 * R) (by linarith))).2
  have hlog : Real.log (2 * R) = Real.log 2 + Real.log R :=
    Real.log_mul (by norm_num) (by linarith : R ≠ 0)
  rw [hlog] at hu
  change diskGreen R x x ≤ diskGreen (2 * R) 0 0 at hm
  linarith

theorem diskGreen_diagonal_interior_log_bound (R : ℝ) (hR : 4 ≤ R) (x : Site)
    (hx : normSq x ≤ (R / 2) ^ 2) :
    |diskGreen R x x - (2 / Real.pi) * Real.log R| ≤
      diskGreenEnergyConstant + (2 / Real.pi) * Real.log 2 := by
  have hsub := translated_inner_disk_subset R (by linarith) x hx
  have hm := killedGreen_mono_domain _ _ hsub x x
  have he := killedGreen_translate x (diskFinset (R / 2)) 0 0
  simp only [add_zero] at he
  rw [he] at hm
  have hl := (abs_le.mp (diskGreen_origin_log_bound (R / 2) (by linarith))).1
  have hlog : Real.log (R / 2) = Real.log R - Real.log 2 :=
    Real.log_div (by linarith : R ≠ 0) (by norm_num)
  rw [hlog] at hl
  have hxin : x ∈ disk R := by change normSq x < R ^ 2; nlinarith
  have hu := diskGreen_diagonal_upper R (by linarith) x hxin
  change diskGreen (R / 2) 0 0 ≤ diskGreen R x x at hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SRWTightness
