import SRWTightness.GeneratingFunction

open MeasureTheory

namespace SRWTightness

/-- Integrability transports through the independent first direction and remaining path. -/
theorem integrable_first_step_future (f : Direction → Sample → ℝ)
    (hm : ∀ d, Measurable (f d)) (hf : ∀ d, Integrable (f d) pathLaw) :
    Integrable (fun ω ↦ f (ω 0) (shift 1 ω)) pathLaw := by
  have hmeas : Measurable (fun p : Direction × Sample ↦ f p.1 p.2) :=
    measurable_from_prod_countable_right hm
  have hprod : Integrable (fun p : Direction × Sample ↦ f p.1 p.2)
      (directionLaw.prod pathLaw) :=
    (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hf, Integrable.of_finite⟩
  rw [← first_step_future_law] at hprod
  exact (integrable_map_measure hmeas.aestronglyMeasurable
    ((measurable_pi_apply 0).prodMk (measurable_shift 1)).aemeasurable).mp hprod

/-- Occupation weight stopped after a fixed number of steps or on leaving the domain. -/
noncomputable def finiteHorizonWeight (D A : Finset Site) (v : A → ℝ) :
    ℕ → Site → Sample → ℝ
  | 0, _, _ => 1
  | n + 1, x, ω => if x ∈ D then siteWeight A v x *
      finiteHorizonWeight D A v n (x + step (ω 0)) (shift 1 ω) else 1

/-- Each finite horizon weight is measurable. -/
theorem measurable_finiteHorizonWeight (D A : Finset Site) (v : A → ℝ)
    (n : ℕ) (x : Site) : Measurable (finiteHorizonWeight D A v n x) := by
  induction n generalizing x with
  | zero => exact measurable_const
  | succ n ih =>
    by_cases hx : x ∈ D
    · simp only [finiteHorizonWeight, if_pos hx]
      have hm : Measurable (fun p : Direction × Sample ↦
          finiteHorizonWeight D A v n (x + step p.1) p.2) :=
        measurable_from_prod_countable_right (fun d ↦ ih (x + step d))
      exact measurable_const.mul (hm.comp
        ((measurable_pi_apply 0).prodMk (measurable_shift 1)))
    · simpa only [finiteHorizonWeight, if_neg hx] using
        (measurable_const : Measurable (fun _ : Sample ↦ (1 : ℝ)))

/-- Fixed horizons have finite integrals for arbitrary finite site weights. -/
theorem integrable_finiteHorizonWeight (D A : Finset Site) (v : A → ℝ)
    (n : ℕ) (x : Site) : Integrable (finiteHorizonWeight D A v n x) pathLaw := by
  induction n generalizing x with
  | zero => exact integrable_const 1
  | succ n ih =>
    by_cases hx : x ∈ D
    · simp only [finiteHorizonWeight, if_pos hx]
      exact (integrable_first_step_future _
        (fun d ↦ measurable_finiteHorizonWeight D A v n (x + step d))
        (fun d ↦ ih (x + step d))).const_mul _
    · simpa only [finiteHorizonWeight, if_neg hx] using (integrable_const (1 : ℝ))

/-- Nonnegative site weights give nonnegative finite horizon weights. -/
theorem finiteHorizonWeight_nonneg (D A : Finset Site) (v : A → ℝ)
    (hv : ∀ z, 0 ≤ v z) (n : ℕ) (x : Site) (ω : Sample) :
    0 ≤ finiteHorizonWeight D A v n x ω := by
  induction n generalizing x ω with
  | zero => exact zero_le_one
  | succ n ih =>
    by_cases hx : x ∈ D
    · simp only [finiteHorizonWeight, if_pos hx]
      apply mul_nonneg _ (ih _ _)
      unfold siteWeight
      split <;> first | apply hv | exact zero_le_one
    · simp only [finiteHorizonWeight, if_neg hx, zero_le_one]

/-- A positive weighted harmonic function bounds every finite horizon expectation. -/
theorem finiteHorizonWeight_integral_le (D A : Finset Site) (v : A → ℝ)
    (hv : ∀ z, 0 ≤ v z) (F : Site → ℝ) (hF : ∀ x, 1 ≤ F x)
    (hhar : ∀ x ∈ D, F x = siteWeight A v x *
      ((1 / 4 : ℝ) * ∑ d : Direction, F (x + step d)))
    (n : ℕ) (x : Site) : ∫ ω, finiteHorizonWeight D A v n x ω ∂pathLaw ≤ F x := by
  induction n generalizing x with
  | zero => simpa only [finiteHorizonWeight, integral_const, probReal_univ,
      one_smul] using hF x
  | succ n ih =>
    by_cases hx : x ∈ D
    · simp only [finiteHorizonWeight, if_pos hx]
      rw [integral_const_mul, integral_first_step_future _
        (fun d ↦ measurable_finiteHorizonWeight D A v n (x + step d))
        (fun d ↦ integrable_finiteHorizonWeight D A v n (x + step d)),
        integral_direction_average, hhar x hx]
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d _ ↦ ih _)) (by norm_num)
      · unfold siteWeight
        split <;> first | apply hv | exact zero_le_one
    · simpa only [finiteHorizonWeight, if_neg hx, integral_const, probReal_univ,
        one_smul] using hF x

end SRWTightness
