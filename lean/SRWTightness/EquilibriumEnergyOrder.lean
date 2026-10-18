import SRWTightness.EquilibriumSiteCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

noncomputable def equilibriumEnergyTime (D K : Finset Site) (α g : ℝ) : ℝ :=
  1 / (g * capacity D K) - α / (2 * g)

noncomputable def equilibriumDiscreteError (D K : Finset Site) (g : ℝ) : ℝ :=
  (∑ x ∈ K, equilibriumWeight D K x ^ 2) / (2 * g)

noncomputable def pointEnergyTime (D : Finset Site) (z : Site) (α g : ℝ) : ℝ :=
  killedGreen D z z / g - (1 + α) / (2 * g)

theorem equilibriumDiscreteError_nonneg (D K : Finset Site) (g : ℝ) (hg : 0 ≤ g) :
    0 ≤ equilibriumDiscreteError D K g := by
  unfold equilibriumDiscreteError
  apply div_nonneg (Finset.sum_nonneg (fun x _ ↦ sq_nonneg _))
  positivity

theorem normalizedEquilibriumAverage_memLp_two (D A K : Finset Site) (α g u : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1) (k : ℕ) :
    MemLp (normalizedEquilibriumAverage D A K k α g u) 2 (markProductLaw D A α k) := by
  unfold normalizedEquilibriumAverage normalizedWeightedSum
  exact memLp_finsetSum Finset.univ (fun z _ ↦
    (normalizedMarkSum_memLp_two D A α g u hα hcap k z).const_mul (equilibriumWeight D K z))

theorem covariance_self_nonneg_real {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) :
    0 ≤ covariance X X μ :=
  integral_nonneg (fun ω ↦ mul_self_nonneg _)

/-- The site time lies above every average time, with the discrete error still retained. -/
theorem equilibriumEnergyTime_add_error_le_point (D A K : Finset Site)
    (hKA : K ⊆ A) (hAD : A ⊆ D) (z : A) (hz : (z : Site) ∈ K)
    (hzero : equilibriumWeight D K z = 0)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D A ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    equilibriumEnergyTime D K α g + equilibriumDiscreteError D K g ≤ pointEnergyTime D z α g := by
  letI := markProductLaw_isProbabilityMeasure D A α hα.le hcap k
  let F := normalizedMarkSum A k α g u z
  let S := normalizedEquilibriumAverage D A K k α g u
  have hF := normalizedMarkSum_memLp_two D A α g u hα.le hcap k z
  have hS := normalizedEquilibriumAverage_memLp_two D A K α g u hα.le hcap k
  have hFF : covariance F F (markProductLaw D A α k) = pointEnergyTime D z α g := by
    dsimp [F, pointEnergyTime]
    rw [normalizedMarkSum_covariance D A hAD α g u hα hg hu hcap k hk]
    simp only [ite_true]
    ring
  have hFS : covariance F S (markProductLaw D A α k) = equilibriumEnergyTime D K α g := by
    dsimp [F, S, equilibriumEnergyTime]
    rw [normalizedEquilibriumAverage_coordinate_covariance D A K hKA hAD z hz α g u hα hg hu hcap k hk,
      hzero, zero_div, sub_zero]
  have hSS : covariance S S (markProductLaw D A α k) =
      equilibriumEnergyTime D K α g - equilibriumDiscreteError D K g :=
    normalizedEquilibriumAverage_covariance_self D A K hKA hAD ⟨z, hz⟩ α g u hα hg hu hcap k hk
  have hn := covariance_self_nonneg_real (markProductLaw D A α k) (F - S)
  rw [covariance_sub_sub hF hS hF hS, hFF, hFS, covariance_comm S F, hFS, hSS] at hn
  linarith

theorem equilibriumEnergyTime_le_point (D A K : Finset Site)
    (hKA : K ⊆ A) (hAD : A ⊆ D) (z : A) (hz : (z : Site) ∈ K)
    (hzero : equilibriumWeight D K z = 0)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D A ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    equilibriumEnergyTime D K α g ≤ pointEnergyTime D z α g := by
  have hh := equilibriumEnergyTime_add_error_le_point D A K hKA hAD z hz hzero α g u hα hg hu hcap k hk
  linarith [equilibriumDiscreteError_nonneg D K g hg.le]

end SRWTightness
