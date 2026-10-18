import SRWTightness.PairMarkCovariance
import SRWTightness.CapacityEnergyParameters
import SRWTightness.EquilibriumEnergyOrder

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The off-diagonal residual covariance is uniformly bounded at a separation-scale average. -/
theorem pair_residual_cross_bound (b : Site) (R a L : ℝ) (M : Finset Site)
    (hMD : M ⊆ translateFinset b (diskFinset R)) (z y : M) (hz : (z : Site) = b)
    (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ a)
    (hhi : a ≤ L * Real.sqrt (normSq ((y : Site) - b))) (hRa : 2 * a ≤ R)
    (α u : ℝ) (hα : 0 < α) (hu : 0 < u)
    (hcap : α * capacity (translateFinset b (diskFinset R)) M ≤ 1)
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    |covariance (normalizedMarkSum M k α (2 / Real.pi) u z)
      (normalizedMarkSum M k α (2 / Real.pi) u y)
      (markProductLaw (translateFinset b (diskFinset R)) M α k) -
      equilibriumEnergyTime (translateFinset b (diskFinset R))
        (translateFinset b (diskFinset a)) α (2 / Real.pi)| ≤
        2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 + Real.log L := by
  let ρ := Real.sqrt (normSq ((y : Site) - b))
  have hρ0 : 0 < ρ := by dsimp [ρ]; linarith
  have ha0 : 0 < a := by linarith
  have hR0 : 0 < R := by linarith
  have hL : 0 < L := by nlinarith
  have hc := pair_mark_covariance_log_distance b R M hMD z y hz hρ (by linarith)
    α u hα hu hcap k hk
  have he := capacity_energy_translated_bound b R a (by linarith) hRa
  have hl := Real.log_le_log hρ0 (show ρ ≤ a by dsimp [ρ]; linarith)
  have hh := Real.log_le_log ha0 hhi
  rw [Real.log_mul hL.ne' hρ0.ne'] at hh
  rw [Real.log_div hR0.ne' hρ0.ne'] at hc
  rw [Real.log_div hR0.ne' ha0.ne'] at he
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  obtain ⟨he1, he2⟩ := abs_le.mp he
  unfold equilibriumEnergyTime
  apply abs_le.mpr
  constructor <;> linarith

end SRWTightness
