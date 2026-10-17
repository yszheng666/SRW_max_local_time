import SRWTightness.GaussianMeanLaw
import SRWTightness.LocalizedIntervalBridge
import SRWTightness.TimeGridInterpolation

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- A finite list of Gaussian endpoint coordinates, preceded by zero and extended by zero. -/
noncomputable def finiteGaussianMesh (n : ℕ) (x : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : 0 < j ∧ j ≤ n then x ⟨j - 1, by omega⟩ else 0

noncomputable def finiteGaussianBridgedPath (T : ℕ → ℝ) (n M : ℕ)
    (x : Fin n → ℝ) (ω : ℕ → GaussianCoefficientSpace) (v : ℝ) : ℝ :=
  timeGridInterpolation T (finiteGaussianMesh n x) M v + timeGridBridge T M ω v

/-- The dyadic flat-prefix event with a prescribed endpoint interval. -/
def finiteGaussianPrefixWindow (T : ℕ → ℝ) (n M : ℕ) (last : Fin n) (q a b : ℝ) :
    Set ((Fin n → ℝ) × (ℕ → GaussianCoefficientSpace)) :=
  {p | p.1 last ∈ Set.Icc a b ∧ ∀ r j : ℕ, (j : ℝ) / 2 ^ r ≤ T n →
    finiteGaussianBridgedPath T n M p.1 p.2 ((j : ℝ) / 2 ^ r) ≤ q}

/-- Standard finite Gaussian interpolation and reflection-kernel identity, supplied as a hypothesis.
The extra bridge intervals after the retained endpoint do not affect this prefix event. -/
def FiniteGaussianBridgeKernelInput : Prop :=
  ∀ (T : ℕ → ℝ) (n M : ℕ) (last : Fin n), last.val + 1 = n →
    n ≤ M → T 0 = 0 → (∀ j < M, T j < T (j + 1)) →
    ∀ q a b : ℝ, 0 < q → a ≤ b → b ≤ q →
    ((gaussianCoordinateLaw (fun j l : Fin n ↦ min (T (j.val + 1)) (T (l.val + 1)))).prod
      (independentBridgeLaw ℕ)).real (finiteGaussianPrefixWindow T n M last q a b) =
      ∫ s in Set.Icc a b, gaussianPDFReal 0 (T n).toNNReal s *
        (1 - Real.exp (-(2 * q * (q - s) / T n)))

end SRWTightness
