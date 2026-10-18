import SRWTightness.GeometricDiskPointTimes
import SRWTightness.GeometricDiskErrorSum
import SRWTightness.GaussianSmallDiagonalComparison

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

/-- Comparison for all disk averages together with the center point, including auxiliary variables
and the conditional-moment lower bound. The event-specific moment remains an explicit hypothesis. -/
theorem gaussian_disk_point_comparison {n : ℕ} {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsFiniteMeasure ν] (b : Site) (R A q α : ℝ) (hn : 0 < n)
    (hA : 4 ≤ A) (hq : 2 ≤ q)
    (hlog : 1 + 2 * (diskGreenEnergyConstant / (2 / Real.pi)) ≤ Real.log q)
    (hsep : ∀ i : Fin n, 2 * (A * q ^ i.val) ≤ R)
    (hfirst : 1 ≤ equilibriumEnergyTime (diskFinset R)
      (diskFinset (A * q ^ (n - 1))) α (2 / Real.pi))
    (hpoint : 1 + diskPointEnergyGapConstant ≤ Real.log A)
    (hsmall : diskEquilibriumWeightConstant / A ≤ (2 / Real.pi) / 8) :
    let K := brownianTimeMatrix (geometricDiskPointTime R A q α n) (n + 1)
    let e := geometricDiskPointError b A R q (2 / Real.pi) n
    (K - Matrix.diagonal e).PosDef ∧
    (gaussianCoordinateLaw (K - Matrix.diagonal e)).prod ν ≤
      ENNReal.ofReal (Real.exp (4 * diskEquilibriumWeightConstant / (A * (2 / Real.pi)))) •
        ((gaussianCoordinateLaw K).prod ν) ∧
    ∀ (s : Set (((Fin (n + 1)) → ℝ) × β)), MeasurableSet s → ∀ C : ℝ,
      (∫ x in s, gaussianInverseCorrection K (K - Matrix.diagonal e) x.1
        ∂(gaussianCoordinateLaw K).prod ν ≤ C * ((gaussianCoordinateLaw K).prod ν).real s) →
      Real.exp (-C / 2) * ((gaussianCoordinateLaw K).prod ν).real s ≤
        ((gaussianCoordinateLaw (K - Matrix.diagonal e)).prod ν).real s := by
  let T := geometricDiskPointTime R A q α n
  let K := brownianTimeMatrix T (n + 1)
  let e := geometricDiskPointError b A R q (2 / Real.pi) n
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hT : T 0 = 0 := geometricDiskPointTime_zero R A q α n
  have hgap := geometricDiskPointTime_gaps R A q α n hn (by linarith) (by linarith)
    hlog (fun i hi ↦ hsep ⟨i, hi⟩) hfirst hpoint
  have hK : K.PosDef := by
    dsimp [K]
    rw [brownianTimeMatrix_eq_increment T hT (n + 1)
      (fun k hk ↦ by linarith [hgap k hk])]
    exact incrementCovariance_posDef _ 1 (by norm_num) (fun i ↦ hgap i.val i.isLt)
  have hlo (x : Fin (n + 1) → ℝ) : (1 / 4 : ℝ) * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x) := by
    have hh := brownianTimeMatrix_quadratic_lower T hT (n + 1) 1 (by norm_num) hgap x
    simpa only [K, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hh
  have he (i : Fin (n + 1)) : 0 ≤ e i :=
    geometricDiskPointError_nonneg b A R q _ hg.le n i
  have hsum : (∑ i, e i) ≤ (diskEquilibriumWeightConstant / A) / (2 / Real.pi) := by
    dsimp [e]
    rw [geometricDiskPointError_sum]
    exact equilibriumDiscreteError_geometric_sum_upper b A R q _ hA hq hg hsep
  have hsumSmall : (∑ i, e i) ≤ (1 / 4 : ℝ) / 2 := by
    apply hsum.trans
    apply (div_le_iff₀ hg).mpr
    nlinarith
  have hesmall (i : Fin (n + 1)) : e i ≤ (1 / 4 : ℝ) / 2 :=
    (Finset.single_le_sum (fun j _ ↦ he j) (Finset.mem_univ i)).trans hsumSmall
  have hh := gaussian_smallDiagonal_event_comparison ν K hK (1 / 4) (by norm_num)
    hlo e he hesmall
  have hexp : (∑ i, e i) / (1 / 4) ≤
      4 * diskEquilibriumWeightConstant / (A * (2 / Real.pi)) := by
    calc
      _ ≤ ((diskEquilibriumWeightConstant / A) / (2 / Real.pi)) / (1 / 4) :=
        div_le_div_of_nonneg_right hsum (by norm_num)
      _ = _ := by ring
  refine ⟨hh.1, hh.2.1.trans ?_, hh.2.2⟩
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)) _

end SRWTightness
