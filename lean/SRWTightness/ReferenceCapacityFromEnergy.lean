import SRWTightness.EquilibriumEnergyOrder

namespace SRWTightness

/-- A positive observation time and alpha<=2g make the actual reference-mark mass admissible. -/
theorem reference_capacity_le_one_of_energy (D K : Finset Site) (hKD : K ⊆ D)
    (hne : K.Nonempty) (α g : ℝ) (hg : 0 < g) (hα : α ≤ 2 * g)
    (hE : 1 ≤ equilibriumEnergyTime D K α g) : α * capacity D K ≤ 1 := by
  have hc := capacity_pos D K hKD hne
  have he : 1 + α / (2 * g) ≤ 1 / (g * capacity D K) := by
    unfold equilibriumEnergyTime at hE
    linarith
  have hh := (le_div_iff₀ (mul_pos hg hc)).mp he
  have hform : (1 + α / (2 * g)) * (g * capacity D K) =
      g * capacity D K + α * capacity D K / 2 := by
    field_simp
    <;> ring
  rw [hform] at hh
  have hαc := mul_le_mul_of_nonneg_right hα hc.le
  nlinarith

end SRWTightness
