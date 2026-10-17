import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- One endpoint coefficient and a countable array of dyadic bridge coefficients. -/
abbrev GaussianCoefficientIndex := Option (ℕ × ℕ)

abbrev GaussianCoefficientSpace := GaussianCoefficientIndex → ℝ

/-- The actual product probability law used for a Gaussian series construction. -/
noncomputable def gaussianCoefficientLaw : Measure GaussianCoefficientSpace :=
  Measure.infinitePi (fun _ ↦ gaussianReal 0 1)

instance : IsProbabilityMeasure gaussianCoefficientLaw := by
  unfold gaussianCoefficientLaw
  infer_instance

theorem gaussianCoefficient_map (i : GaussianCoefficientIndex) :
    gaussianCoefficientLaw.map (fun ω ↦ ω i) = gaussianReal 0 1 :=
  Measure.infinitePi_map_eval _ i

theorem gaussianCoefficient_independent :
    iIndepFun (fun i (ω : GaussianCoefficientSpace) ↦ ω i) gaussianCoefficientLaw :=
  iIndepFun_infinitePi (X := fun _ (x : ℝ) ↦ x) (fun _ ↦ measurable_id)

theorem gaussianCoefficient_pair (i j : GaussianCoefficientIndex) (hij : i ≠ j) :
    gaussianCoefficientLaw.map (fun ω ↦ (ω i, ω j)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) :=
  Measure.infinitePi_map_eval_prod hij

theorem gaussianCoefficient_finite (I : Finset GaussianCoefficientIndex) :
    gaussianCoefficientLaw.map I.restrict =
      Measure.pi (fun _ : I ↦ gaussianReal 0 1) :=
  Measure.infinitePi_map_restrict _

end SRWTightness
