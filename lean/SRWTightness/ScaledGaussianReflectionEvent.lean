import SRWTightness.ScaledGaussianDeterministicReflection

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A measurable past event can be retained when reflecting the later endpoint. -/
theorem scaled_gaussian_reflection_event (T r t : ℝ) (hT : 0 < T)
    (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ≤ T)
    (A : Set (Set.Icc (0 : ℝ) r → ℝ)) (B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    gaussianCoefficientLaw.real {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A ∧
      Real.sqrt T * gaussianDyadicPath ω (t / T) ∈ B} =
    gaussianCoefficientLaw.real {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A ∧
      2 * (Real.sqrt T * gaussianDyadicPath ω (r / T)) -
        Real.sqrt T * gaussianDyadicPath ω (t / T) ∈ B} := by
  have hP : Measurable (fun ω (u : Set.Icc (0 : ℝ) r) ↦
      Real.sqrt T * gaussianDyadicPath ω (u / T)) :=
    measurable_pi_lambda _ (fun _ ↦
      measurable_const.mul (gaussianDyadicPath_measurable _))
  have hX : Measurable (fun ω ↦ Real.sqrt T * gaussianDyadicPath ω (t / T)) :=
    measurable_const.mul (gaussianDyadicPath_measurable _)
  have hY : Measurable (fun ω ↦ 2 * (Real.sqrt T * gaussianDyadicPath ω (r / T)) -
      Real.sqrt T * gaussianDyadicPath ω (t / T)) :=
    (measurable_const.mul (measurable_const.mul (gaussianDyadicPath_measurable _))).sub hX
  have he := congrArg (fun μ ↦ μ.real (A ×ˢ B))
    (scaled_gaussian_deterministic_reflection T r t hT hr hrt ht)
  rw [map_measureReal_apply (hP.prodMk hX) (hA.prod hB),
    map_measureReal_apply (hP.prodMk hY) (hA.prod hB)] at he
  exact he

end SRWTightness
