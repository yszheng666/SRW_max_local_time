import SRWTightness.ScaledGaussianPastKilledIntegral
import SRWTightness.KilledBrownianFirstMoment

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The surviving future distance has the current distance as its mean on every past event. -/
theorem scaled_gaussian_killed_first_moment_past (hReflection : BridgeReflectionInput)
    (T r t x : ℝ) (hT : 0 < T) (hr : 0 ≤ r) (hrt : r < t) (ht : t ≤ T)
    (A : Set (Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A)
    (hpos : ∀ p ∈ A, p ⟨r, hr, le_rfl⟩ < x) :
    (∫ ω in {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A ∧
      ∀ u ∈ Set.Icc (0 : ℝ) (t - r),
        Real.sqrt T * gaussianDyadicPath ω ((r + u) / T) ≤ x},
      x - Real.sqrt T * gaussianDyadicPath ω (t / T) ∂gaussianCoefficientLaw) =
    ∫ ω in {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A},
      x - Real.sqrt T * gaussianDyadicPath ω (r / T) ∂gaussianCoefficientLaw := by
  have hg := ((scaled_gaussian_path_process T hT).hasGaussianLaw_eval
    ⟨t, hr.trans hrt.le, ht⟩).integrable
  have hi := (integrable_const x).sub hg
  have he := scaled_gaussian_past_killed_integral hReflection T r t x hT hr hrt ht
    A hA hpos (fun y ↦ y) measurable_id hi
  rw [he]
  apply integral_congr_ae
  have hP : Measurable (fun ω (u : Set.Icc (0 : ℝ) r) ↦
      Real.sqrt T * gaussianDyadicPath ω (u / T)) :=
    measurable_pi_lambda _ (fun _ ↦ measurable_const.mul (gaussianDyadicPath_measurable _))
  filter_upwards [ae_restrict_mem (hA.preimage hP)] with ω hω
  exact killed_brownian_first_moment (t - r)
    (x - Real.sqrt T * gaussianDyadicPath ω (r / T)) (sub_pos.mpr hrt)
    (sub_pos.mpr (hpos _ hω))

end SRWTightness
