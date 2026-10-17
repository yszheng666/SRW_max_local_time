import SRWTightness.SourceObservationCovariance
import SRWTightness.GaussianDiskFixedParameters
import SRWTightness.SmallDiagonalCovariancePositive

open Matrix MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The fixed geometric source parameters give a uniform one-eighth covariance lower bound. -/
theorem disk_fixed_covariance_lower (b : Site) (R A α : ℝ) (n : ℕ) (hn : 0 < n)
    (hA : diskPointGaussianMinimumRadius ≤ A) (hα : α ≤ 2 * (2 / Real.pi))
    (hR : diskEnergyOuterRatio * (A * diskEnergyGapRatio ^ (n - 1)) ≤ R)
    (x : Fin (n + 1) → ℝ) :
    (1 / 8 : ℝ) * (∑ i, x i ^ 2) ≤
      x ⬝ᵥ ((brownianTimeMatrix (geometricDiskPointTime R A diskEnergyGapRatio α n) (n + 1) -
        Matrix.diagonal (geometricDiskPointError b A R diskEnergyGapRatio (2 / Real.pi) n)) *ᵥ x) := by
  obtain ⟨ha, hq, hsep, houter, htime, _⟩ := diskGaussianParameterChoice A R α n
    (diskPointGaussianMinimumRadius_ge_base.trans hA) hα hR
  have hp : 1 ≤ diskEnergyGapRatio ^ (n - 1) := one_le_pow₀ (by linarith)
  have harad : 1 ≤ A * diskEnergyGapRatio ^ (n - 1) := by nlinarith
  have hfirst := equilibriumEnergyTime_disk_ge_one R _ α harad houter htime
  have hgap := geometricDiskPointTime_gaps R A diskEnergyGapRatio α n hn
    (by linarith) (by linarith) diskEnergyGapRatio_log_lower
    (fun i hi ↦ hsep ⟨i, hi⟩) hfirst (diskPointGaussianMinimumRadius_log_gap A hA)
  let T := geometricDiskPointTime R A diskEnergyGapRatio α n
  let K := brownianTimeMatrix T (n + 1)
  let e := geometricDiskPointError b A R diskEnergyGapRatio (2 / Real.pi) n
  have hlo (v : Fin (n + 1) → ℝ) :
      (1 / 4 : ℝ) * (∑ i, v i ^ 2) ≤ v ⬝ᵥ (K *ᵥ v) := by
    have hh := brownianTimeMatrix_quadratic_lower T
      (geometricDiskPointTime_zero R A diskEnergyGapRatio α n) (n + 1) 1
      (by norm_num) hgap v
    simpa only [K, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hh
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have he (i : Fin (n + 1)) : 0 ≤ e i :=
    geometricDiskPointError_nonneg b A R diskEnergyGapRatio _ hg.le n i
  have hsum : (∑ i, e i) ≤ (diskEquilibriumWeightConstant / A) / (2 / Real.pi) := by
    dsimp [e]
    rw [geometricDiskPointError_sum]
    exact equilibriumDiscreteError_geometric_sum_upper b A R diskEnergyGapRatio _
      ha hq hg hsep
  have hs : (∑ i, e i) ≤ (1 / 4 : ℝ) / 2 := by
    apply hsum.trans
    apply (div_le_iff₀ hg).mpr
    have hh := diskPointGaussianMinimumRadius_small_error A hA
    nlinarith
  have hesmall (i : Fin (n + 1)) : e i ≤ (1 / 4 : ℝ) / 2 :=
    (Finset.single_le_sum (fun j _ ↦ he j) (Finset.mem_univ i)).trans hs
  convert smallDiagonal_covariance_lower K (1 / 4) hlo e hesmall x using 1 <;> norm_num

/-- The actual reference-mark observation covariance satisfies the required uniform spectral gap. -/
theorem source_observation_covariance_lower (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t) :
    ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      let R := Real.exp 1 * sourceLowerRadius t + 14
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
      ∃ z : M, (z : Site) = b ∧ ∀ (k : ℕ) (u : ℝ), 0 < u → u ^ 2 / 2 = (k : ℝ) →
        let F := fun i : Fin ((I + 1) + 1) ↦
          normalizedObservation (translateFinset b (diskFinset R)) M
            (geometricDiskFamily b A diskEnergyGapRatio (I + 1)) z k α (2 / Real.pi) u
            (diskObservationIndex (I + 1) i)
        ∀ x : Fin ((I + 1) + 1) → ℝ,
          (1 / 8 : ℝ) * (∑ i, x i ^ 2) ≤
            x ⬝ᵥ ((Matrix.of fun i j ↦ covariance (F i) (F j)
              (markProductLaw (translateFinset b (diskFinset R)) M α k)) *ᵥ x) := by
  obtain ⟨I, hI, z, hz, hcov⟩ := source_observation_covariance b t A hA ht
  obtain ⟨J, hJ, hα, hR⟩ := source_gaussian_parameters t A hA ht
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  refine ⟨I, hI, z, hz, ?_⟩
  intro k u hu hk
  dsimp only
  intro x
  simp_rw [hcov k u hu hk]
  exact disk_fixed_covariance_lower b _ A _ (I + 1) (by omega) hA hα (by simpa using hR) x

end SRWTightness
