import SRWTightness.GaussianPathCharFun

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem gaussianPath_vector_gaussian {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (ht' : ∀ i, t i ≤ 1) :
    HasGaussianLaw (fun ω i ↦ gaussianDyadicPath ω (t i)) gaussianCoefficientLaw := by
  classical
  constructor
  apply isGaussian_of_isGaussian_map
  intro L
  have hv : Measurable (fun ω i ↦ gaussianDyadicPath ω (t i)) :=
    measurable_pi_lambda _ (fun i ↦ gaussianDyadicPath_measurable _)
  rw [Measure.map_map L.continuous.measurable hv]
  have hL (x : ι → ℝ) : L x = ∑ i, L (Pi.single i 1) * x i := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have he : Pi.single i (x i) = x i • (Pi.single i 1 : ι → ℝ) := by
      ext j
      by_cases h : i = j
      · subst j
        simp
      · simp [Ne.symm h]
    rw [he, map_smul]
    simp [mul_comm]
  have he : L ∘ (fun ω i ↦ gaussianDyadicPath ω (t i)) =
      (fun ω ↦ ∑ i, L (Pi.single i 1) * gaussianDyadicPath ω (t i)) :=
    funext (fun ω ↦ hL _)
  rw [he]
  exact (gaussianPath_linear_gaussian t (fun i ↦ L (Pi.single i 1)) ht ht').isGaussian_map

theorem gaussianPath_unit_gaussianProcess :
    IsGaussianProcess (fun t : Set.Icc (0 : ℝ) 1 ↦ fun ω ↦ gaussianDyadicPath ω t)
      gaussianCoefficientLaw where
  hasGaussianLaw I := by
    exact gaussianPath_vector_gaussian (fun i : I ↦ i.val.val)
      (fun i ↦ i.val.property.1) (fun i ↦ i.val.property.2)

theorem gaussianPath_linear_hasLaw {ι : Type*} [Fintype ι]
    (t a : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (ht' : ∀ i, t i ≤ 1) :
    HasLaw (fun ω ↦ ∑ i, a i * gaussianDyadicPath ω (t i))
      (gaussianReal 0 (Real.toNNReal (∑ i, ∑ k, a i * a k * min (t i) (t k))))
      gaussianCoefficientLaw :=
  ⟨(gaussianPath_linear_gaussian t a ht ht').aemeasurable,
    gaussianPath_linear_law t a ht ht'⟩

theorem gaussianPath_linear_mean {ι : Type*} [Fintype ι]
    (t a : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (ht' : ∀ i, t i ≤ 1) :
    (∫ ω, ∑ i, a i * gaussianDyadicPath ω (t i) ∂gaussianCoefficientLaw) = 0 := by
  rw [(gaussianPath_linear_hasLaw t a ht ht').integral_eq, integral_id_gaussianReal]

theorem gaussianPath_linear_variance {ι : Type*} [Fintype ι]
    (t a : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (ht' : ∀ i, t i ≤ 1) :
    Var[fun ω ↦ ∑ i, a i * gaussianDyadicPath ω (t i); gaussianCoefficientLaw] =
      ∑ i, ∑ k, a i * a k * min (t i) (t k) := by
  rw [(gaussianPath_linear_hasLaw t a ht ht').variance_eq, variance_id_gaussianReal]
  exact Real.coe_toNNReal _ (gaussianPath_quadratic_nonneg t a ht ht')

theorem gaussianPath_eval_hasLaw (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    HasLaw (fun ω ↦ gaussianDyadicPath ω t) (gaussianReal 0 t.toNNReal)
      gaussianCoefficientLaw := by
  simpa using gaussianPath_linear_hasLaw (fun _ : Unit ↦ t) (fun _ ↦ 1)
    (fun _ ↦ ht) (fun _ ↦ ht')

theorem gaussianPath_eval_variance (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    Var[fun ω ↦ gaussianDyadicPath ω t; gaussianCoefficientLaw] = t := by
  rw [(gaussianPath_eval_hasLaw t ht ht').variance_eq, variance_id_gaussianReal]
  exact Real.coe_toNNReal t ht

theorem gaussianPath_covariance (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (ht : 0 ≤ t) (ht' : t ≤ 1) :
    cov[fun ω ↦ gaussianDyadicPath ω s, fun ω ↦ gaussianDyadicPath ω t;
      gaussianCoefficientLaw] = min s t := by
  have hsum : Var[fun ω ↦ gaussianDyadicPath ω s + gaussianDyadicPath ω t;
      gaussianCoefficientLaw] = s + t + 2 * min s t := by
    have h := gaussianPath_linear_variance (fun b : Bool ↦ if b then s else t)
      (fun _ ↦ 1) (by intro b; cases b <;> assumption)
      (by intro b; cases b <;> assumption)
    simpa [add_comm, add_left_comm, add_assoc, min_comm, two_mul] using h
  have hmems := (gaussianPath_unit_gaussianProcess.hasGaussianLaw_eval ⟨s, hs, hs'⟩).memLp_two
  have hmemt := (gaussianPath_unit_gaussianProcess.hasGaussianLaw_eval ⟨t, ht, ht'⟩).memLp_two
  rw [variance_fun_add hmems hmemt, gaussianPath_eval_variance s hs hs',
    gaussianPath_eval_variance t ht ht'] at hsum
  linarith

end SRWTightness
