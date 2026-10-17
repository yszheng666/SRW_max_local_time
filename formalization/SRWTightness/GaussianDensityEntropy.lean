import SRWTightness.GaussianQuadraticIntegrable
import SRWTightness.WeightedMgfDerivative
import SRWTightness.DensityEntropyEvent

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The exact log density ratio of two nondegenerate centered Gaussian laws. -/
theorem gaussianDensityWeight_log {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef) (x : ι → ℝ) :
    Real.log (gaussianDensityWeight K S x) =
      Real.log (Real.sqrt K.det / Real.sqrt S.det) - gaussianInverseCorrection K S x / 2 := by
  have hp : 0 < Real.sqrt K.det / Real.sqrt S.det :=
    div_pos (Real.sqrt_pos.mpr hK.det_pos) (Real.sqrt_pos.mpr hS.det_pos)
  rw [gaussianDensityWeight, Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp]
  dsimp only [gaussianInverseCorrection]
  ring

/-- The log likelihood ratio is integrable under the numerator Gaussian law. -/
theorem gaussianDensityWeight_log_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef) :
    Integrable (fun x ↦ Real.log (gaussianDensityWeight K S x)) (gaussianCoordinateLaw S) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure S
  have he : gaussianInverseCorrection K S = fun x ↦ -gaussianInverseCorrection S K x := by
    funext x
    simp only [gaussianInverseCorrection, Matrix.sub_mulVec, dotProduct_sub]
    ring
  have hQ : Integrable (gaussianInverseCorrection K S) (gaussianCoordinateLaw S) := by
    rw [he]
    exact (gaussianInverseCorrection_integrable S K).neg
  simp_rw [gaussianDensityWeight_log K S hK hS]
  exact (integrable_const _).sub (hQ.div_const 2)

/-- Gaussian density ratios are normalized and have integrable relative entropy. -/
theorem gaussianDensityWeight_entropy_data {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef) :
    Integrable (gaussianDensityWeight K S) (gaussianCoordinateLaw K) ∧
    (∫ x, gaussianDensityWeight K S x ∂gaussianCoordinateLaw K) = 1 ∧
    Integrable (fun x ↦ gaussianDensityWeight K S x * Real.log (gaussianDensityWeight K S x))
      (gaussianCoordinateLaw K) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure S
  have hm := gaussianDensityWeight_measurable K S
  have hn := gaussianDensityWeight_nonneg K S
  have hconst : Integrable (fun _ : ι → ℝ ↦ (1 : ℝ))
      ((gaussianCoordinateLaw K).withDensity (fun x ↦ ENNReal.ofReal (gaussianDensityWeight K S x))) := by
    rw [← gaussianCoordinateLaw_changeDensity K S hK hS]
    exact integrable_const 1
  have hf := (integrable_nonnegative_density_iff (gaussianCoordinateLaw K)
    (gaussianDensityWeight K S) hm hn (fun _ ↦ 1)).mp hconst
  have hf' : Integrable (gaussianDensityWeight K S) (gaussianCoordinateLaw K) := by
    simpa only [mul_one] using hf
  have hmass := withDensity_ofReal_event_real (gaussianCoordinateLaw K)
    (gaussianDensityWeight K S) hm hn Set.univ MeasurableSet.univ
  rw [← gaussianCoordinateLaw_changeDensity K S hK hS] at hmass
  have hmass' : (∫ x, gaussianDensityWeight K S x ∂gaussianCoordinateLaw K) = 1 := by
    simpa using hmass.symm
  have hi := gaussianDensityWeight_log_integrable K S hK hS
  rw [gaussianCoordinateLaw_changeDensity K S hK hS] at hi
  exact ⟨hf', hmass', (integrable_nonnegative_density_iff (gaussianCoordinateLaw K)
    (gaussianDensityWeight K S) hm hn (fun x ↦ Real.log (gaussianDensityWeight K S x))).mp hi⟩

/-- Every event under two actual centered Gaussian laws is controlled by their density entropy. -/
theorem gaussian_entropy_event_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef)
    (s : Set (ι → ℝ)) (hs : MeasurableSet s) :
    |(gaussianCoordinateLaw S).real s - (gaussianCoordinateLaw K).real s| ≤
      2 * Real.sqrt (∫ x, gaussianDensityWeight K S x *
        Real.log (gaussianDensityWeight K S x) ∂gaussianCoordinateLaw K) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hh := gaussianDensityWeight_entropy_data K S hK hS
  rw [gaussianCoordinateLaw_changeDensity K S hK hS]
  exact density_entropy_event_bound (gaussianCoordinateLaw K) (gaussianDensityWeight K S)
    (gaussianDensityWeight_measurable K S) hh.1 (gaussianDensityWeight_nonneg K S)
    hh.2.1 hh.2.2 s hs

end SRWTightness
