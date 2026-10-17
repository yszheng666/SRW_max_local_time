import SRWTightness.EquilibriumSiteCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- An interior site has no boundary correction in its covariance with an equilibrium average. -/
theorem normalizedEquilibriumAverage_interior_covariance
    (D M : Finset Site) (b : Site) (a : ℝ) (ha : 2 ≤ a)
    (hKM : translateFinset b (diskFinset a) ⊆ M) (hMD : M ⊆ D)
    (z : M) (hz : Real.sqrt (normSq ((z : Site) - b)) < a - 1)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D M ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    covariance (normalizedMarkSum M k α g u z)
      (normalizedEquilibriumAverage D M (translateFinset b (diskFinset a)) k α g u)
      (markProductLaw D M α k) =
        1 / (g * capacity D (translateFinset b (diskFinset a))) - α / (2 * g) := by
  have hs := Real.sq_sqrt (normSq_nonneg ((z : Site) - b))
  have hn := Real.sqrt_nonneg (normSq ((z : Site) - b))
  have hi : normSq ((z : Site) - b) < (a - 1) ^ 2 := by nlinarith
  have hmem : (z : Site) ∈ translateFinset b (diskFinset a) := by
    rw [mem_translateFinset_iff, mem_diskFinset]
    change normSq ((z : Site) - b) < a ^ 2
    nlinarith
  have he := translated_disk_equilibrium_inner_zero D b a ha (hKM.trans hMD) z hi
  have hw : equilibriumWeight D (translateFinset b (diskFinset a)) z = 0 := by
    simp only [equilibriumWeight, he, zero_div]
  rw [normalizedEquilibriumAverage_coordinate_covariance D M _ hKM hMD z hmem
    α g u hα hg hu hcap k hk, hw, zero_div, sub_zero]

/-- The four-distance separation used for late pairs places the second site strictly inside the average. -/
theorem late_pair_interior_margin (ρ a : ℝ) (hρ : 1 ≤ ρ) (ha : 4 * ρ ≤ a) :
    2 ≤ a ∧ ρ < a - 1 := by
  constructor <;> linarith

end SRWTightness
