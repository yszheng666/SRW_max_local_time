import SRWTightness.GaussianQuadraticIntegrable
import Mathlib.MeasureTheory.Integral.Prod

open Matrix MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem gaussian_event_aux_lower_of_correction_moment {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace β] (ν : Measure β) [IsFiniteMeasure ν]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef)
    (hfactor : 1 ≤ Real.sqrt K.det / Real.sqrt S.det)
    (hn : ∀ x, 0 ≤ gaussianInverseCorrection K S x)
    (s : Set ((ι → ℝ) × β)) (hs : MeasurableSet s) (C : ℝ)
    (hmean : ∫ x in s, gaussianInverseCorrection K S x.1 ∂(gaussianCoordinateLaw K).prod ν ≤
      C * ((gaussianCoordinateLaw K).prod ν).real s) :
    Real.exp (-C / 2) * ((gaussianCoordinateLaw K).prod ν).real s ≤
      ((gaussianCoordinateLaw S).prod ν).real s := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hp : 0 ≤ Real.sqrt K.det / Real.sqrt S.det := le_trans zero_le_one hfactor
  have hu (x : (ι → ℝ) × β) : gaussianDensityWeight K S x.1 ≤ Real.sqrt K.det / Real.sqrt S.det := by
    unfold gaussianDensityWeight
    apply mul_le_of_le_one_right hp
    apply Real.exp_le_one_iff.mpr
    have hh := hn x.1
    change 0 ≤ x.1 ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x.1) at hh
    linarith
  have hl (x : (ι → ℝ) × β) : Real.exp (-gaussianInverseCorrection K S x.1 / 2) ≤
      gaussianDensityWeight K S x.1 := by
    have hh := mul_le_mul_of_nonneg_right hfactor
      (Real.exp_nonneg (-gaussianInverseCorrection K S x.1 / 2))
    simpa only [one_mul, gaussianDensityWeight, gaussianInverseCorrection] using hh
  rw [gaussianCoordinateLaw_changeDensity K S hK hS,
    prod_withDensity_left (gaussianDensityWeight_measurable K S).ennreal_ofReal]
  exact density_event_lower_of_moment ((gaussianCoordinateLaw K).prod ν)
    (fun x ↦ gaussianDensityWeight K S x.1) (fun x ↦ gaussianInverseCorrection K S x.1)
    C (Real.sqrt K.det / Real.sqrt S.det)
    ((gaussianDensityWeight_measurable K S).comp measurable_fst)
    (fun x ↦ gaussianDensityWeight_nonneg K S x.1) hu
    ((gaussianInverseCorrection_measurable K S).comp measurable_fst) (fun x ↦ hn x.1) hl s hs
    ((gaussianInverseCorrection_integrable K S).comp_fst ν).integrableOn hmean

end SRWTightness
