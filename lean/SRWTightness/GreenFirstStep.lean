import SRWTightness.OccupationFirstStep
import SRWTightness.FirstStepLaw

open MeasureTheory

namespace SRWTightness

 theorem killedGreen_zero_of_not_mem (D : Finset Site) (x y : Site) (hx : x ∉ D) :
    killedGreen D x y = 0 := by
  unfold killedGreen
  simp only [domainLocalTime_zero_of_not_mem D x y hx, Nat.cast_zero, integral_zero]

/-- The Green kernel satisfies the exact first-step equation of the four-neighbor SRW. -/
theorem killedGreen_first_step (D : Finset Site) (x y : Site) (hx : x ∈ D) :
    killedGreen D x y = (if x = y then 1 else 0) +
      ∫ d, killedGreen D (x + step d) y ∂directionLaw := by
  let f : Direction → Sample → ℝ := fun d ω ↦ (domainLocalTime D (x + step d) y ω : ℝ)
  have hm : ∀ d, Measurable (f d) := fun d ↦
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_domainLocalTime D (x + step d) y)
  have hf : ∀ d, Integrable (f d) pathLaw := fun d ↦ integrable_domainLocalTime D _ y
  have hpmeas : Measurable (fun p : Direction × Sample ↦ f p.1 p.2) :=
    measurable_from_prod_countable_right hm
  have hp : Integrable (fun p : Direction × Sample ↦ f p.1 p.2)
      (directionLaw.prod pathLaw) :=
    (integrable_prod_iff hpmeas.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hf, Integrable.of_finite⟩
  have hg : Integrable (fun ω : Sample ↦ f (ω 0) (shift 1 ω)) pathLaw := by
    rw [← first_step_future_law] at hp
    exact hp.comp_measurable ((measurable_pi_apply 0).prodMk (measurable_shift 1))
  have he : (fun ω ↦ (domainLocalTime D x y ω : ℝ)) =ᵐ[pathLaw]
      (fun ω : Sample ↦ (if x = y then (1 : ℝ) else 0) + f (ω 0) (shift 1 ω)) := by
    filter_upwards [domainExit_ne_top_ae D x] with ω hω
    have h := domainLocalTime_first_step D x y hx ω hω
    dsimp [f]
    simpa only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
      congrArg (fun n : ℕ ↦ (n : ℝ)) h
  unfold killedGreen
  rw [integral_congr_ae he, integral_add (integrable_const _) hg]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]
  rw [integral_first_step_future f hm hf]

 theorem killedGreen_first_step_sum (D : Finset Site) (x y : Site) (hx : x ∈ D) :
    killedGreen D x y = (if x = y then 1 else 0) +
      (1 / 4 : ℝ) * ∑ d : Direction, killedGreen D (x + step d) y := by
  rw [killedGreen_first_step D x y hx, directionLaw, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, smul_eq_mul]
  rw [← Finset.mul_sum]
  norm_num

end SRWTightness
