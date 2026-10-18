import SRWTightness.GaussianFiniteProcess
import SRWTightness.GaussianCoefficientMoments

open MeasureTheory ProbabilityTheory

namespace SRWTightness

abbrev GaussianFiniteIndex (m : ℕ) := Option (Σ n : Fin m, Fin (2 ^ n.val))

def gaussianFiniteIndex (m : ℕ) : GaussianFiniteIndex m → GaussianCoefficientIndex
  | none => none
  | some ⟨n, k⟩ => some (n.val, k.val)

theorem gaussianFiniteIndex_injective (m : ℕ) : Function.Injective (gaussianFiniteIndex m) := by
  intro a b h
  cases a with
  | none => cases b <;> simp_all [gaussianFiniteIndex]
  | some a =>
    cases b with
    | none => simp [gaussianFiniteIndex] at h
    | some b =>
      obtain ⟨n, k⟩ := a
      obtain ⟨l, j⟩ := b
      simp only [gaussianFiniteIndex, Option.some.injEq, Prod.mk.injEq] at h
      have hn : n = l := Fin.ext h.1
      subst l
      have hk : k = j := Fin.ext h.2
      subst j
      rfl

noncomputable def gaussianFiniteWeight (m : ℕ) (t : ℝ) : GaussianFiniteIndex m → ℝ
  | none => t
  | some ⟨n, k⟩ => scaledSchauderTent ((2 : ℝ) ^ n.val) k.val
      ((Real.sqrt 2)⁻¹ ^ n.val) t

theorem gaussianFinitePath_linear (m : ℕ) (t : ℝ) (ω : GaussianCoefficientSpace) :
    gaussianFinitePath (m, t) ω =
      ∑ i : GaussianFiniteIndex m, gaussianFiniteWeight m t i * ω (gaussianFiniteIndex m i) := by
  simp only [Fintype.sum_option, Fintype.sum_sigma, gaussianFiniteWeight, gaussianFiniteIndex,
    gaussianFinitePath, schauderLevel]
  simp_rw [← Fin.sum_univ_eq_sum_range]
  simp [mul_comm]

theorem gaussianFinitePath_covariance (m : ℕ) (s t : ℝ) :
    cov[gaussianFinitePath (m, s), gaussianFinitePath (m, t); gaussianCoefficientLaw] =
      ∑ i : GaussianFiniteIndex m, gaussianFiniteWeight m s i * gaussianFiniteWeight m t i := by
  classical
  simp_rw [show gaussianFinitePath (m, s) = fun ω ↦
    ∑ i : GaussianFiniteIndex m, gaussianFiniteWeight m s i * ω (gaussianFiniteIndex m i) from
    funext (gaussianFinitePath_linear m s)]
  simp_rw [show gaussianFinitePath (m, t) = fun ω ↦
    ∑ i : GaussianFiniteIndex m, gaussianFiniteWeight m t i * ω (gaussianFiniteIndex m i) from
    funext (gaussianFinitePath_linear m t)]
  rw [covariance_fun_sum_fun_sum
    (fun i ↦ ((gaussianCoefficient_subgaussian (gaussianFiniteIndex m i)).memLp 2).const_mul _)
    (fun i ↦ ((gaussianCoefficient_subgaussian (gaussianFiniteIndex m i)).memLp 2).const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    gaussianCoefficient_covariance, (gaussianFiniteIndex_injective m).eq_iff]
  simp [mul_ite, mul_comm]

/-- The explicit covariance contributed by all bridge levels below depth m. -/
noncomputable def dyadicTentKernel (m : ℕ) (s t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range m, ∑ k ∈ Finset.range (2 ^ n),
    scaledSchauderTent ((2 : ℝ) ^ n) k ((Real.sqrt 2)⁻¹ ^ n) s *
    scaledSchauderTent ((2 : ℝ) ^ n) k ((Real.sqrt 2)⁻¹ ^ n) t

theorem gaussianFinitePath_covariance_explicit (m : ℕ) (s t : ℝ) :
    cov[gaussianFinitePath (m, s), gaussianFinitePath (m, t); gaussianCoefficientLaw] =
      s * t + dyadicTentKernel m s t := by
  rw [gaussianFinitePath_covariance]
  simp only [Fintype.sum_option, Fintype.sum_sigma, gaussianFiniteWeight, dyadicTentKernel]
  simp_rw [← Fin.sum_univ_eq_sum_range]

theorem gaussianFinitePath_mean (m : ℕ) (t : ℝ) :
    (∫ ω, gaussianFinitePath (m, t) ω ∂gaussianCoefficientLaw) = 0 := by
  simp_rw [gaussianFinitePath_linear]
  rw [integral_finsetSum _ (fun i _ ↦
    (gaussianCoefficient_subgaussian (gaussianFiniteIndex m i)).integrable.const_mul _)]
  simp [integral_const_mul, gaussianCoefficient_mean]

end SRWTightness
