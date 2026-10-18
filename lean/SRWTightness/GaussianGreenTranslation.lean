import SRWTightness.GaussianField
import SRWTightness.GreenTranslation

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Reindexing a finite Green field by a translation preserves its law. -/
theorem gaussian_green_translation (b : Site) (D : Finset Site) :
    ∃ T : EuclideanSpace ℝ D ≃ₗᵢ[ℝ] EuclideanSpace ℝ (translateFinset b D),
      (∀ (φ : EuclideanSpace ℝ D) (x : D),
        T φ ⟨b + x, (mem_translateFinset_add b D x).mpr x.2⟩ = φ x) ∧
      MeasurePreserving T (gaussianGreenLaw D D)
        (gaussianGreenLaw (translateFinset b D) (translateFinset b D)) := by
  classical
  let e : D ≃ translateFinset b D :=
    { toFun := fun x ↦ ⟨b + x, (mem_translateFinset_add b D x).mpr x.2⟩
      invFun := fun y ↦ ⟨y - b, (mem_translateFinset_iff b D y).mp y.2⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro y; apply Subtype.ext; simp }
  let T := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  have hTe (φ : EuclideanSpace ℝ D) (x : D) : T φ (e x) = φ x := by
    change φ (e.symm (e x)) = φ x
    rw [e.symm_apply_apply]
  refine ⟨T, hTe, ⟨by fun_prop, ?_⟩⟩
  let L := T.toContinuousLinearEquiv.toContinuousLinearMap
  change (gaussianGreenLaw D D).map L = _
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map]
    · simp only [gaussianGreenLaw_mean, map_zero]
    · exact IsGaussian.integrable_id
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis
      (EuclideanSpace.basisFun (translateFinset b D) ℝ).toBasis fun i j ↦ ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covariance_map]
    · have heval (i : translateFinset b D) :
          (fun u ↦ inner ℝ
            ((EuclideanSpace.basisFun (translateFinset b D) ℝ).toBasis i) u) ∘ L =
            fun u ↦ u (e.symm i) := by
        ext u
        simp only [Function.comp_apply, OrthonormalBasis.coe_toBasis,
          EuclideanSpace.basisFun_inner]
        change L u i = u (e.symm i)
        rfl
      rw [heval i, heval j, gaussianGreenLaw_covariance D D (by rfl),
        covarianceBilin_apply_eq_cov]
      have hinner (i : translateFinset b D) :
          (fun u : EuclideanSpace ℝ (translateFinset b D) ↦
            inner ℝ ((EuclideanSpace.basisFun (translateFinset b D) ℝ).toBasis i) u) =
              fun u ↦ u i := by ext u; simp [PiLp.inner_apply]
      rw [hinner i, hinner j,
        gaussianGreenLaw_covariance _ _ (by rfl)]
      have hi : b + ((e.symm i : D) : Site) = i := by
        have ht := congrArg Subtype.val (e.apply_symm_apply i)
        exact ht
      have hj : b + ((e.symm j : D) : Site) = j := by
        have ht := congrArg Subtype.val (e.apply_symm_apply j)
        exact ht
      rw [← hi, ← hj, killedGreen_translate]
      all_goals exact IsGaussian.memLp_two_id
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

/-- Translation does not change any full-field maximum exceedance probability. -/
theorem gaussian_green_maximum_translation (b : Site) (D : Finset Site) (t : ℝ) :
    (gaussianGreenLaw (translateFinset b D) (translateFinset b D)).real
      {φ | ∃ x : translateFinset b D, t ≤ φ x} =
      (gaussianGreenLaw D D).real {φ | ∃ x : D, t ≤ φ x} := by
  classical
  obtain ⟨T, hT, hmp⟩ := gaussian_green_translation b D
  have hs : MeasurableSet {φ : EuclideanSpace ℝ (translateFinset b D) |
      ∃ x : translateFinset b D, t ≤ φ x} := by
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion (fun x ↦ measurableSet_le measurable_const (by fun_prop))
  have hp := hmp.measure_preimage hs.nullMeasurableSet
  have he : T ⁻¹' {φ : EuclideanSpace ℝ (translateFinset b D) |
        ∃ x : translateFinset b D, t ≤ φ x} =
      {φ : EuclideanSpace ℝ D | ∃ x : D, t ≤ φ x} := by
    ext φ
    constructor
    · rintro ⟨y, hy⟩
      have hyD := (mem_translateFinset_iff b D y).mp y.2
      refine ⟨⟨y - b, hyD⟩, ?_⟩
      have ht := hT φ ⟨y - b, hyD⟩
      have hh : (⟨b + (y - b), (mem_translateFinset_add b D (y - b)).mpr hyD⟩ :
          translateFinset b D) = y := by apply Subtype.ext; simp
      rw [hh] at ht
      rwa [← ht]
    · rintro ⟨x, hx⟩
      exact ⟨⟨b + x, (mem_translateFinset_add b D x).mpr x.2⟩, by rwa [hT]⟩
  rw [he] at hp
  exact congrArg ENNReal.toReal hp.symm

end SRWTightness
