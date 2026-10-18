import SRWTightness.GaussianFuturePathLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Elapsed-time indexing preserves independence of future increments from the whole past. -/
theorem gaussian_elapsed_future_indep_past (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    IndepFun (fun ω (u : Set.Icc (0 : ℝ) s) ↦ gaussianDyadicPath ω u)
      (fun ω (t : Set.Icc (0 : ℝ) (1 - s)) ↦
        gaussianDyadicPath ω (s + t) - gaussianDyadicPath ω s) gaussianCoefficientLaw := by
  let H : (Set.Icc s (1 : ℝ) → ℝ) → (Set.Icc (0 : ℝ) (1 - s) → ℝ) :=
    fun f t ↦ f ⟨s + t, by linarith [t.property.1], by linarith [t.property.2]⟩
  have hH : Measurable H := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  exact (gaussian_future_path_indep_past s hs hs1).comp measurable_id hH

/-- The actual past and future increment paths have the product of their actual path laws. -/
theorem gaussian_future_past_product_law (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    gaussianCoefficientLaw.map (fun ω ↦
      ((fun u : Set.Icc (0 : ℝ) s ↦ gaussianDyadicPath ω u),
       (fun t : Set.Icc (0 : ℝ) (1 - s) ↦
         gaussianDyadicPath ω (s + t) - gaussianDyadicPath ω s))) =
    (gaussianCoefficientLaw.map (fun ω (u : Set.Icc (0 : ℝ) s) ↦ gaussianDyadicPath ω u)).prod
      (gaussianCoefficientLaw.map (fun ω (t : Set.Icc (0 : ℝ) (1 - s)) ↦
        Real.sqrt (1 - s) * gaussianDyadicPath ω (t / (1 - s)))) := by
  have hm : Measurable (fun ω (u : Set.Icc (0 : ℝ) s) ↦ gaussianDyadicPath ω u) :=
    measurable_pi_lambda _ (fun _ ↦ gaussianDyadicPath_measurable _)
  have hn : Measurable (fun ω (t : Set.Icc (0 : ℝ) (1 - s)) ↦
      gaussianDyadicPath ω (s + t) - gaussianDyadicPath ω s) :=
    measurable_pi_lambda _ (fun _ ↦
      (gaussianDyadicPath_measurable _).sub (gaussianDyadicPath_measurable _))
  have he := (gaussian_elapsed_future_indep_past s hs hs1.le).map_prod_eq_prod_map_map
    hm.aemeasurable hn.aemeasurable
  rw [gaussian_future_path_law s hs hs1] at he
  exact he

end SRWTightness
