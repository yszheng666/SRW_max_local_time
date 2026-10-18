import SRWTightness.PairResidualDeterminant
import SRWTightness.GaussianCovarianceDensity

open Matrix

namespace SRWTightness

/-- Uniform two-dimensional residual Gaussian density bound of order inverse remaining time. -/
theorem pairResidualMatrix_density_upper (Vz Vw c v d C : ℝ)
    (hC : 0 ≤ C) (hd : 0 < d - v) (hlarge : 4 * C ≤ d - v)
    (hz : |Vz - d| ≤ C) (hw : |Vw - d| ≤ C) (hc : |c - v| ≤ C)
    (x : Fin 2 → ℝ) :
    (gaussianCovarianceDensity (pairResidualMatrix Vz Vw c v) x).toReal ≤
      2 * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2) / (d - v) := by
  let G := pairResidualMatrix Vz Vw c v
  have hG : G.PosDef := pairResidualMatrix_posDef Vz Vw c v d C hC hd hlarge hz hw hc
  have hdet := pairResidualMatrix_det_lower Vz Vw c v d C hC hd hlarge hz hw hc
  have hs : (d - v) / 2 ≤ Real.sqrt G.det := by
    apply (Real.le_sqrt (by linarith) hG.det_pos.le).mpr
    dsimp [G]
    nlinarith
  have hInv : (Real.sqrt G.det)⁻¹ ≤ 2 / (d - v) := by
    have hh := one_div_le_one_div_of_le (by linarith : 0 < (d - v) / 2) hs
    calc
      _ = 1 / Real.sqrt G.det := by rw [one_div]
      _ ≤ 1 / ((d - v) / 2) := hh
      _ = 2 / (d - v) := by field_simp
  have hq : 0 ≤ x ⬝ᵥ (G⁻¹ *ᵥ x) := by
    simpa only [star_trivial] using hG.inv.posSemidef.dotProduct_mulVec_nonneg x
  have he : Real.exp (-(x ⬝ᵥ (G⁻¹ *ᵥ x)) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  rw [gaussianCovarianceDensity_toReal _ hG]
  simp only [Fintype.card_fin]
  calc
    _ ≤ (Real.sqrt G.det)⁻¹ * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2) :=
      mul_le_of_le_one_right (by positivity) he
    _ ≤ (2 / (d - v)) * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_right hInv (sq_nonneg _)
    _ = _ := by ring

end SRWTightness
