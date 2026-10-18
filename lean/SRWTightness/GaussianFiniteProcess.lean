import SRWTightness.GaussianCoefficientSpace
import SRWTightness.GaussianDyadicNodes
import SRWTightness.SchauderLevel
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem gaussianCoefficient_gaussianProcess :
    IsGaussianProcess (fun i (ω : GaussianCoefficientSpace) ↦ ω i) gaussianCoefficientLaw where
  hasGaussianLaw I := by
    apply iIndepFun.hasGaussianLaw
    · intro i
      constructor
      change IsGaussian (gaussianCoefficientLaw.map (fun ω ↦ ω i.val))
      rw [gaussianCoefficient_map]
      infer_instance
    · exact gaussianCoefficient_independent.restrict I

/-- All finite dyadic approximations, jointly in their depth and time parameter. -/
noncomputable def gaussianFinitePath (p : ℕ × ℝ) (ω : GaussianCoefficientSpace) : ℝ :=
  p.2 * ω none + ∑ n ∈ Finset.range p.1,
    schauderLevel (2 ^ n) ((2 : ℝ) ^ n) ((Real.sqrt 2)⁻¹ ^ n)
      (fun k ↦ ω (some (n, k))) p.2

theorem gaussianFinitePath_gaussianProcess :
    IsGaussianProcess gaussianFinitePath gaussianCoefficientLaw := by
  classical
  apply gaussianCoefficient_gaussianProcess.of_isGaussianProcess
  intro p
  let I : Finset GaussianCoefficientIndex := insert none
    ((Finset.range p.1).biUnion fun n ↦ (Finset.range (2 ^ n)).image fun k ↦ some (n, k))
  have hi (n : Fin p.1) (k : Fin (2 ^ n.val)) : some (n.val, k.val) ∈ I := by
    simp only [I, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
    exact Or.inr ⟨n.val, n.isLt, k.val, k.isLt, rfl⟩
  let L : (I → ℝ) →L[ℝ] ℝ :=
    { toFun x := p.2 * x ⟨none, by simp [I]⟩ +
        ∑ n : Fin p.1, ∑ k : Fin (2 ^ n.val),
          x ⟨some (n.val, k.val), hi n k⟩ *
            scaledSchauderTent ((2 : ℝ) ^ n.val) k.val ((Real.sqrt 2)⁻¹ ^ n.val) p.2
      map_add' x y := by simp [add_mul, mul_add, Finset.sum_add_distrib]; ring
      map_smul' c x := by
        simp [mul_assoc, mul_left_comm, Finset.mul_sum, mul_add] }
  refine ⟨I, L, ?_⟩
  intro ω
  simp only [L, gaussianFinitePath, schauderLevel, ContinuousLinearMap.coe_mk',
    LinearMap.coe_mk, AddHom.coe_mk, Finset.restrict_def]
  simp_rw [← Fin.sum_univ_eq_sum_range]

/-- All dyadic-time observations of the actual infinite path are jointly Gaussian. -/
theorem gaussianDyadicPath_dyadic_gaussianProcess :
    IsGaussianProcess
      (fun p : ℕ × ℕ ↦ fun ω ↦ gaussianDyadicPath ω ((p.2 : ℝ) / (2 : ℝ) ^ p.1))
      gaussianCoefficientLaw := by
  have h := gaussianFinitePath_gaussianProcess.comp_right
    (fun p : ℕ × ℕ ↦ (p.1, (p.2 : ℝ) / (2 : ℝ) ^ p.1))
  apply h.congr
  intro p
  exact Filter.Eventually.of_forall (fun ω ↦ (gaussianDyadicPath_dyadic ω p.1 p.2).symm)

end SRWTightness
