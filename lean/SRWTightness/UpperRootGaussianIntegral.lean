import SRWTightness.UpperRootGaussianMoment

open Set MeasureTheory

namespace SRWTightness

/-- The continuous centered kernel obtained by replacing discrete root counts by unit intervals. -/
noncomputable def upperRootGaussianIntegrand (q c x : ℝ) : ℝ :=
  x ^ (1 / 4 : ℝ) * Real.exp (-((Real.sqrt (2 * x) - c) ^ 2 / (4 * q)))

/-- Every finite root integral has the uniform quadratic scale required in source (4.27). -/
theorem upper_root_gaussian_integral_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ q c : ℝ, 1 ≤ q → 0 ≤ c → c ≤ 3 * q → ∀ M : ℕ,
      (∫ x in (0 : ℝ)..(M : ℝ), upperRootGaussianIntegrand q c x) ≤ K * q ^ 2 := by
  obtain ⟨K, hK, hmoment⟩ := upper_root_gaussian_moment_bound
  refine ⟨32 * K, by positivity, ?_⟩
  intro q c hq hc hcap M
  have hq0 : 0 < q := by linarith
  obtain ⟨hH, hI⟩ := hmoment (4 * q) c (by linarith) hc (by linarith)
  let H := upperRootGaussianMoment (4 * q) c
  let G := upperRootGaussianIntegrand q c
  let F := fun y : ℝ ↦ (2 * y) * G (y ^ 2)
  have hs0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ)), Real.sqrt_nonneg (2 : ℝ)]
  have hHcomp : Integrable (fun y : ℝ ↦ H (Real.sqrt 2 * y)) :=
    hH.comp_mul_left' hs0.ne'
  have hdom (y : ℝ) (hy : y ∈ Ioi (0 : ℝ)) : F y ≤ 2 * H (Real.sqrt 2 * y) := by
    have hy0 : 0 < y := hy
    have hpow : (y ^ 2) ^ (1 / 4 : ℝ) = y ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_two y, ← Real.rpow_mul hy0.le]
      norm_num
    have hfac : y * (y ^ 2) ^ (1 / 4 : ℝ) = y ^ (3 / 2 : ℝ) := by
      rw [hpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy0,
        Real.rpow_one]
    have hsqrt : Real.sqrt (2 * y ^ 2) = Real.sqrt 2 * y := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)), Real.sqrt_sq_eq_abs, abs_of_pos hy0]
    have hweight : y ^ (3 / 2 : ℝ) ≤ (|Real.sqrt 2 * y| + 1) ^ (3 / 2 : ℝ) := by
      apply Real.rpow_le_rpow hy0.le _ (by norm_num)
      rw [abs_of_pos (mul_pos hs0 hy0)]
      nlinarith
    dsimp only [F, G, H, upperRootGaussianIntegrand, upperRootGaussianMoment]
    rw [hsqrt]
    calc
      _ = 2 * y ^ (3 / 2 : ℝ) *
          Real.exp (-((Real.sqrt 2 * y - c) ^ 2 / (4 * q))) := by
        calc
          _ = 2 * (y * (y ^ 2) ^ (1 / 4 : ℝ)) *
              Real.exp (-((Real.sqrt 2 * y - c) ^ 2 / (4 * q))) := by ring
          _ = _ := by rw [hfac]
      _ ≤ 2 * (|Real.sqrt 2 * y| + 1) ^ (3 / 2 : ℝ) *
          Real.exp (-((Real.sqrt 2 * y - c) ^ 2 / (4 * q))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hweight (by norm_num))
          (Real.exp_nonneg _)
      _ = _ := by ring
  have hFcont : Continuous F := by
    dsimp [F, G, upperRootGaussianIntegrand]
    fun_prop (disch := norm_num)
  have hF : IntegrableOn F (Ioi 0) := by
    apply (hHcomp.const_mul 2).integrableOn.mono' hFcont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [F, G, upperRootGaussianIntegrand]; positivity)]
    exact hdom y hy
  have hG : IntegrableOn G (Ioi 0) := by
    apply (integrableOn_Ioi_comp_rpow_iff G (p := 2) (by norm_num)).mp
    simpa only [abs_of_pos (by norm_num : 0 < (2 : ℝ)),
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, smul_eq_mul, F] using hF
  have hchange : (∫ y in Ioi 0, F y) = ∫ x in Ioi 0, G x := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
      smul_eq_mul, F] using integral_comp_rpow_Ioi_of_pos (g := G) (p := 2) (by norm_num)
  have hG0 : 0 ≤ᵐ[volume.restrict (Ioi 0)] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    dsimp [G, upperRootGaussianIntegrand]
    positivity
  have hH0 : 0 ≤ ∫ y : ℝ, H y := integral_nonneg (fun _ ↦ by
    dsimp [H, upperRootGaussianMoment]; positivity)
  calc
    _ ≤ ∫ x in Ioi 0, G x := by
      rw [intervalIntegral.integral_of_le (Nat.cast_nonneg M)]
      exact setIntegral_mono_set hG hG0 (ae_of_all _ (fun _ hx ↦ hx.1))
    _ = ∫ y in Ioi 0, F y := hchange.symm
    _ ≤ ∫ y in Ioi 0, 2 * H (Real.sqrt 2 * y) :=
      setIntegral_mono_on hF (hHcomp.const_mul 2).integrableOn measurableSet_Ioi hdom
    _ ≤ ∫ y : ℝ, 2 * H (Real.sqrt 2 * y) :=
      setIntegral_le_integral (hHcomp.const_mul 2) (ae_of_all _ (fun _ ↦ by
        dsimp [H, upperRootGaussianMoment]; positivity))
    _ = 2 * ((Real.sqrt 2)⁻¹ * ∫ y : ℝ, H y) := by
      rw [integral_const_mul, Measure.integral_comp_mul_left, smul_eq_mul,
        abs_of_pos (inv_pos.mpr hs0)]
    _ ≤ 2 * ∫ y : ℝ, H y := mul_le_mul_of_nonneg_left
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right ((inv_le_one₀ hs0).mpr hs1) hH0) (by norm_num)
    _ ≤ 32 * K * q ^ 2 := by
      have hb := mul_le_mul_of_nonneg_left hI (by norm_num : 0 ≤ (2 : ℝ))
      convert hb using 1 <;> first | rfl | ring

end SRWTightness
