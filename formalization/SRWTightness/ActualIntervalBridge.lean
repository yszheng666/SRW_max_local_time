import SRWTightness.ActualUnitBridge
import Mathlib.Tactic.FieldSimp

open MeasureTheory ProbabilityTheory

namespace SRWTightness

noncomputable def actualIntervalBridge (T t : ℝ) (ω : GaussianCoefficientSpace) : ℝ :=
  Real.sqrt T * actualUnitBridge (t / T) ω

theorem actualIntervalBridge_zero (T : ℝ) (ω : GaussianCoefficientSpace) :
    actualIntervalBridge T 0 ω = 0 := by
  simp [actualIntervalBridge, actualUnitBridge_zero]

theorem actualIntervalBridge_terminal (T : ℝ) (hT : 0 < T) (ω : GaussianCoefficientSpace) :
    actualIntervalBridge T T ω = 0 := by
  simp [actualIntervalBridge, hT.ne', actualUnitBridge_one]

theorem actualIntervalBridge_continuous (T : ℝ) :
    ∀ᵐ ω ∂gaussianCoefficientLaw, Continuous (fun t ↦ actualIntervalBridge T t ω) := by
  filter_upwards [actualUnitBridge_continuous] with ω hω
  exact continuous_const.mul (hω.comp (continuous_id.div_const T))

theorem actualIntervalBridge_measurable (T t : ℝ) : Measurable (actualIntervalBridge T t) :=
  measurable_const.mul (actualUnitBridge_measurable _)

theorem actualIntervalBridge_mean (T t : ℝ) (hT : 0 < T) (ht : 0 ≤ t) (ht' : t ≤ T) :
    (∫ ω, actualIntervalBridge T t ω ∂gaussianCoefficientLaw) = 0 := by
  unfold actualIntervalBridge
  rw [integral_const_mul,
    actualUnitBridge_mean _ (div_nonneg ht hT.le) ((div_le_one hT).mpr ht'), mul_zero]

theorem actualIntervalBridge_covariance (T s t : ℝ) (hT : 0 < T)
    (hs : 0 ≤ s) (hs' : s ≤ T) (ht : 0 ≤ t) (ht' : t ≤ T) :
    cov[actualIntervalBridge T s, actualIntervalBridge T t; gaussianCoefficientLaw] =
      min s t - s * t / T := by
  unfold actualIntervalBridge
  rw [covariance_const_mul_left, covariance_const_mul_right,
    actualUnitBridge_covariance _ _ (div_nonneg hs hT.le) ((div_le_one hT).mpr hs')
      (div_nonneg ht hT.le) ((div_le_one hT).mpr ht')]
  have hm : min (s / T) (t / T) = min s t / T := by
    rcases le_total s t with h | h
    · rw [min_eq_left h, min_eq_left ((div_le_div_iff_of_pos_right hT).mpr h)]
    · rw [min_eq_right h, min_eq_right ((div_le_div_iff_of_pos_right hT).mpr h)]
  rw [hm, ← mul_assoc, Real.mul_self_sqrt hT.le]
  field_simp

theorem actualIntervalBridge_gaussian (T : ℝ) (hT : 0 < T) :
    IsGaussianProcess (fun t : Set.Icc (0 : ℝ) T ↦ actualIntervalBridge T t)
      gaussianCoefficientLaw := by
  let f : Set.Icc (0 : ℝ) T → Set.Icc (0 : ℝ) 1 := fun t ↦
    ⟨t.val / T, div_nonneg t.property.1 hT.le, (div_le_one hT).mpr t.property.2⟩
  exact (actualUnitBridge_gaussian.comp_right f).smul (fun _ ↦ Real.sqrt T)

/-- Independent coefficient samples for an arbitrary family of bridge segments. -/
noncomputable def independentBridgeLaw (ι : Type*) : Measure (ι → GaussianCoefficientSpace) :=
  Measure.infinitePi (fun _ ↦ gaussianCoefficientLaw)

instance independentBridgeLaw_probability (ι : Type*) :
    IsProbabilityMeasure (independentBridgeLaw ι) := by
  unfold independentBridgeLaw
  infer_instance

theorem actualIntervalBridge_path_measurable (T : ℝ) :
    Measurable (fun ω t ↦ actualIntervalBridge T t ω) :=
  measurable_pi_lambda _ (actualIntervalBridge_measurable T)

theorem independentBridge_paths {ι : Type*} (T : ι → ℝ) :
    iIndepFun (fun i (ω : ι → GaussianCoefficientSpace) ↦
      fun t ↦ actualIntervalBridge (T i) t (ω i)) (independentBridgeLaw ι) :=
  iIndepFun_infinitePi (fun i ↦ actualIntervalBridge_path_measurable (T i))

end SRWTightness
