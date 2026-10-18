import SRWTightness.EquilibriumEnergyOrder
import SRWTightness.CapacityEnergyParameters

namespace SRWTightness

/-- Actual capacity energies at two radii differ from their log-ratio by a uniform constant. -/
theorem disk_equilibriumEnergy_spacing (R a b α : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (hRb : 2 * b ≤ R) :
    |equilibriumEnergyTime (diskFinset R) (diskFinset a) α (2 / Real.pi) -
      equilibriumEnergyTime (diskFinset R) (diskFinset b) α (2 / Real.pi) - Real.log (b / a)| ≤
        2 * (diskGreenEnergyConstant / (2 / Real.pi)) := by
  have hR : 0 < R := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have h₁ := capacity_energy_radius_bound R a ha (by linarith)
  have h₂ := capacity_energy_radius_bound R b (ha.trans hab) hRb
  have he : equilibriumEnergyTime (diskFinset R) (diskFinset a) α (2 / Real.pi) -
      equilibriumEnergyTime (diskFinset R) (diskFinset b) α (2 / Real.pi) - Real.log (b / a) =
      (1 / ((2 / Real.pi) * capacity (diskFinset R) (diskFinset a)) - Real.log (R / a)) -
      (1 / ((2 / Real.pi) * capacity (diskFinset R) (diskFinset b)) - Real.log (R / b)) := by
    unfold equilibriumEnergyTime
    rw [Real.log_div hb0.ne' ha0.ne', Real.log_div hR.ne' ha0.ne', Real.log_div hR.ne' hb0.ne']
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

theorem disk_equilibriumEnergy_geometric_spacing (R a B α : ℝ) (ha : 1 ≤ a) (hB : 1 ≤ B)
    (hR : 2 * (B * a) ≤ R) :
    |equilibriumEnergyTime (diskFinset R) (diskFinset a) α (2 / Real.pi) -
      equilibriumEnergyTime (diskFinset R) (diskFinset (B * a)) α (2 / Real.pi) - Real.log B| ≤
        2 * (diskGreenEnergyConstant / (2 / Real.pi)) := by
  have hab : a ≤ B * a := by nlinarith
  have hh := disk_equilibriumEnergy_spacing R a (B * a) α ha hab hR
  have he : B * a / a = B := mul_div_cancel_right₀ B (by linarith : a ≠ 0)
  rwa [he] at hh

/-- A single fixed geometric ratio gives uniform positive energy gaps, independently of the killing radius. -/
theorem exists_uniform_equilibriumEnergy_spacing : ∃ B C : ℝ, 4 < B ∧ 0 < C ∧
    ∀ R a α : ℝ, 1 ≤ a → 2 * (B * a) ≤ R →
      1 ≤ equilibriumEnergyTime (diskFinset R) (diskFinset a) α (2 / Real.pi) -
        equilibriumEnergyTime (diskFinset R) (diskFinset (B * a)) α (2 / Real.pi) ∧
      equilibriumEnergyTime (diskFinset R) (diskFinset a) α (2 / Real.pi) -
        equilibriumEnergyTime (diskFinset R) (diskFinset (B * a)) α (2 / Real.pi) ≤ C := by
  let E := diskGreenEnergyConstant / (2 / Real.pi)
  have hE : 0 < E := div_pos diskGreenEnergyConstant_pos (by positivity)
  let B := Real.exp (2 * E + 4)
  have hB : 4 < B := by have := Real.add_one_le_exp (2 * E + 4); dsimp [B]; linarith
  refine ⟨B, 4 * E + 4, hB, by positivity, ?_⟩
  intro R a α ha hR
  have hh := disk_equilibriumEnergy_geometric_spacing R a B α ha (by linarith) hR
  have hlog : Real.log B = 2 * E + 4 := Real.log_exp _
  rw [hlog] at hh
  change |_ - (2 * E + 4)| ≤ 2 * E at hh
  obtain ⟨hl, hu⟩ := abs_le.mp hh
  constructor <;> linarith

end SRWTightness
