import SRWTightness.GaussianFuturePastProduct
import SRWTightness.ScaledGaussianKilledProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The surviving future increment endpoint has the killed kernel for its remaining duration. -/
theorem gaussian_future_killed_probability (hReflection : BridgeReflectionInput)
    (r x : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (hx : 0 < x)
    (A : Set ℝ) (hA : MeasurableSet A) :
    gaussianCoefficientLaw.real {ω |
      x - (gaussianDyadicPath ω (r + (1 - r)) - gaussianDyadicPath ω r) ∈ A ∧
      ∀ t ∈ Set.Icc (0 : ℝ) (1 - r),
        gaussianDyadicPath ω (r + t) - gaussianDyadicPath ω r ≤ x} =
      (killedBrownianDensityLaw (1 - r) x).real A := by
  have hT : 0 < 1 - r := sub_pos.mpr hr1
  let e : Set.Icc (0 : ℝ) (1 - r) := ⟨1 - r, hT.le, le_rfl⟩
  let C : Set (Set.Icc (0 : ℝ) (1 - r) → ℝ) :=
    {f | x - f e ∈ A ∧ f ∈ dyadicFlatPathEvent (1 - r) x}
  have hC : MeasurableSet C :=
    (hA.preimage (measurable_const.sub (measurable_pi_apply e))).inter
      (dyadicFlatPathEvent_measurable (1 - r) x)
  have hm : Measurable (fun ω (t : Set.Icc (0 : ℝ) (1 - r)) ↦
      gaussianDyadicPath ω (r + t) - gaussianDyadicPath ω r) :=
    measurable_pi_lambda _ (fun _ ↦
      (gaussianDyadicPath_measurable _).sub (gaussianDyadicPath_measurable _))
  have hn : Measurable (fun ω (t : Set.Icc (0 : ℝ) (1 - r)) ↦
      Real.sqrt (1 - r) * gaussianDyadicPath ω (t / (1 - r))) :=
    measurable_pi_lambda _ (fun _ ↦ measurable_const.mul (gaussianDyadicPath_measurable _))
  have he := congrArg (fun μ : Measure (Set.Icc (0 : ℝ) (1 - r) → ℝ) ↦ μ.real C)
    (gaussian_future_path_law r hr hr1)
  rw [map_measureReal_apply hm hC, map_measureReal_apply hn hC] at he
  have hleft : gaussianCoefficientLaw.real {ω |
      x - (gaussianDyadicPath ω (r + (1 - r)) - gaussianDyadicPath ω r) ∈ A ∧
      ∀ t ∈ Set.Icc (0 : ℝ) (1 - r),
        gaussianDyadicPath ω (r + t) - gaussianDyadicPath ω r ≤ x} =
      gaussianCoefficientLaw.real ((fun ω (t : Set.Icc (0 : ℝ) (1 - r)) ↦
        gaussianDyadicPath ω (r + t) - gaussianDyadicPath ω r) ⁻¹' C) := by
    apply measureReal_congr
    filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
    apply propext
    apply and_congr_right
    intro hAω
    exact continuous_flat_iff_dyadic _
      ((hω.comp (continuous_const.add continuous_id)).sub continuous_const) (1 - r) x
  have hright : gaussianCoefficientLaw.real ((fun ω (t : Set.Icc (0 : ℝ) (1 - r)) ↦
      Real.sqrt (1 - r) * gaussianDyadicPath ω (t / (1 - r))) ⁻¹' C) =
      gaussianCoefficientLaw.real {ω |
        x - Real.sqrt (1 - r) * gaussianDyadicPath ω ((1 - r) / (1 - r)) ∈ A ∧
        ∀ t ∈ Set.Icc (0 : ℝ) (1 - r),
          Real.sqrt (1 - r) * gaussianDyadicPath ω (t / (1 - r)) ≤ x} := by
    apply measureReal_congr
    filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
    apply propext
    apply and_congr_right
    intro hAω
    exact (continuous_flat_iff_dyadic _
      (continuous_const.mul (hω.comp (continuous_id.div_const (1 - r)))) (1 - r) x).symm
  exact hleft.trans (he.trans (hright.trans
    (scaled_gaussian_killed_probability hReflection (1 - r) x hT hx A hA)))

end SRWTightness
