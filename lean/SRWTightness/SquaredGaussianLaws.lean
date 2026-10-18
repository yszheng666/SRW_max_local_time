import SRWTightness.GaussianGreenLaplace
import SRWTightness.ContinuousLaplace

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

noncomputable def shiftedGaussianSquareLaw (D A : Finset Site) (u : ℝ) : Measure (A → ℝ) :=
  (gaussianGreenLaw D A).map (fun φ z ↦ (φ z + Real.sqrt (2 * u)) ^ 2 / 2)

noncomputable def occupationPlusGaussianSquareLaw (D A : Finset Site) (α : ℝ) (r : ℝ≥0) :
    Measure (A → ℝ) :=
  ((continuousOccupationLaw D A α r).prod (gaussianGreenLaw D A)).map
    (fun p z ↦ p.1 z + (p.2 z) ^ 2 / 2)

 theorem measurable_shiftedGaussianSquare (A : Finset Site) (u : ℝ) :
    Measurable (fun φ : EuclideanSpace ℝ A ↦ fun z ↦ (φ z + Real.sqrt (2 * u)) ^ 2 / 2) := by
  fun_prop

 theorem measurable_occupationPlusGaussianSquare (A : Finset Site) :
    Measurable (fun p : (A → ℝ) × EuclideanSpace ℝ A ↦ fun z ↦ p.1 z + (p.2 z) ^ 2 / 2) := by
  fun_prop

instance shiftedGaussianSquareLaw_isProbabilityMeasure (D A : Finset Site) (u : ℝ) :
    IsProbabilityMeasure (shiftedGaussianSquareLaw D A u) :=
  Measure.isProbabilityMeasure_map (measurable_shiftedGaussianSquare A u).aemeasurable

 theorem occupationPlusGaussianSquareLaw_isProbabilityMeasure (D A : Finset Site)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1) (r : ℝ≥0) :
    IsProbabilityMeasure (occupationPlusGaussianSquareLaw D A α r) := by
  letI := continuousOccupationLaw_isProbabilityMeasure D A α hα hcap r
  exact Measure.isProbabilityMeasure_map (measurable_occupationPlusGaussianSquare A).aemeasurable

 theorem shiftedGaussianSquareLaw_nonneg (D A : Finset Site) (u : ℝ) :
    ∀ᵐ L ∂shiftedGaussianSquareLaw D A u, ∀ z, 0 ≤ L z := by
  apply (ae_map_iff (measurable_shiftedGaussianSquare A u).aemeasurable
    (measurableSet_nonneg_field A)).mpr
  exact Filter.Eventually.of_forall (fun φ z ↦ by positivity)

 theorem occupationPlusGaussianSquareLaw_nonneg (D A : Finset Site) (α : ℝ) (r : ℝ≥0) :
    ∀ᵐ L ∂occupationPlusGaussianSquareLaw D A α r, ∀ z, 0 ≤ L z := by
  apply (ae_map_iff (measurable_occupationPlusGaussianSquare A).aemeasurable
    (measurableSet_nonneg_field A)).mpr
  have hm := (measurePreserving_fst (μ := continuousOccupationLaw D A α r)
    (ν := gaussianGreenLaw D A)).quasiMeasurePreserving.ae (continuousOccupationLaw_nonneg D A α r)
  filter_upwards [hm] with p hp
  intro z
  exact add_nonneg (hp z) (by positivity)

 theorem shiftedGaussianSquareLaw_laplace (D A : Finset Site) (u : ℝ) (f : A → ℝ) :
    (∫ L, Real.exp (-(∑ z, f z * L z)) ∂shiftedGaussianSquareLaw D A u) =
      gaussianGreenSquaredLaplace D A f (fun _ ↦ Real.sqrt (2 * u)) := by
  have hm : Measurable (fun L : A → ℝ ↦ Real.exp (-(∑ z, f z * L z))) := by fun_prop
  rw [shiftedGaussianSquareLaw, integral_map (measurable_shiftedGaussianSquare A u).aemeasurable
    hm.aestronglyMeasurable]
  unfold gaussianGreenSquaredLaplace
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro φ
  dsimp only
  congr 1
  simp only [mul_div_assoc, Finset.sum_div, neg_div]

 theorem occupationPlusGaussianSquareLaw_laplace (D A : Finset Site) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1) (r : ℝ≥0) (f : A → ℝ) :
    (∫ L, Real.exp (-(∑ z, f z * L z)) ∂occupationPlusGaussianSquareLaw D A α r) =
      (∫ L, Real.exp (-(∑ z, f z * L z)) ∂continuousOccupationLaw D A α r) *
        gaussianGreenSquaredLaplace D A f 0 := by
  letI := continuousOccupationLaw_isProbabilityMeasure D A α hα hcap r
  have hm : Measurable (fun L : A → ℝ ↦ Real.exp (-(∑ z, f z * L z))) := by fun_prop
  rw [occupationPlusGaussianSquareLaw,
    integral_map (measurable_occupationPlusGaussianSquare A).aemeasurable hm.aestronglyMeasurable]
  have he (p : (A → ℝ) × EuclideanSpace ℝ A) :
      Real.exp (-(∑ z, f z * (p.1 z + (p.2 z) ^ 2 / 2))) =
      Real.exp (-(∑ z, f z * p.1 z)) *
        Real.exp (-(∑ z, f z * ((p.2 z) + (0 : A → ℝ) z) ^ 2) / 2) := by
    simp only [Pi.zero_apply, add_zero, mul_add, Finset.sum_add_distrib,
      mul_div_assoc, Finset.sum_div, neg_add, neg_div, Real.exp_add]
  simp_rw [he]
  exact integral_prod_mul (fun L : A → ℝ ↦ Real.exp (-(∑ z, f z * L z)))
    (fun φ : EuclideanSpace ℝ A ↦ Real.exp (-(∑ z, f z * (φ z + (0 : A → ℝ) z) ^ 2) / 2))

end SRWTightness
