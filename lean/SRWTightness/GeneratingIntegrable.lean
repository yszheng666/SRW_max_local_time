import SRWTightness.GeneratingPoisson

open MeasureTheory

namespace SRWTightness
 theorem killedGenerating_first_step_integrable (D K : Finset Site) (v : K → ℝ)
    (hI : ∀ y : Site, Integrable (fun ω ↦ markMonomial v (killedMark D K y ω)) pathLaw) (x : Site) (hx : x ∈ D) :
    killedGenerating D K v x = siteWeight K v x *
      ((1 / 4 : ℝ) * ∑ d : Direction, killedGenerating D K v (x + step d)) := by
  have he : (fun ω ↦ markMonomial v (killedMark D K x ω)) =ᵐ[pathLaw]
      (fun ω ↦ siteWeight K v x * markMonomial v (killedMark D K (x + step (ω 0)) (shift 1 ω))) := by
    filter_upwards [domainExit_ne_top_ae D x] with ω hω
    exact monomial_first_step D K v x hx ω hω
  unfold killedGenerating markTestExpectation
  rw [integral_congr_ae he, integral_const_mul, integral_first_step_future
    (fun d ω ↦ markMonomial v (killedMark D K (x + step d) ω))
    (fun d ↦ (measurable_markMonomial v).comp (measurable_killedMark D K _))
    (fun d ↦ hI _), integral_direction_average]

 theorem generating_poisson_integrable (D A : Finset Site) (v : A → ℝ)
    (hI : ∀ y : Site, Integrable (fun ω ↦ markMonomial v (killedMark D A y ω)) pathLaw) (x : Site) (hx : x ∈ D) :
    (killedGenerating D A v x - 1) - (1 / 4 : ℝ) *
      ∑ d : Direction, (killedGenerating D A v (x + step d) - 1) =
      extendZero A (fun z : A ↦ (v z - 1) * afterStepGenerating D A v z) x := by
  have hh := killedGenerating_first_step_integrable D A v hI x hx
  change killedGenerating D A v x = siteWeight A v x * afterStepGenerating D A v x at hh
  have hav : (1 / 4 : ℝ) * ∑ d : Direction, (killedGenerating D A v (x + step d) - 1) =
      afterStepGenerating D A v x - 1 := by
    rw [Finset.sum_sub_distrib]
    have hc : (∑ _ : Direction, (1 : ℝ)) = 4 := by simp [Direction]
    rw [hc]
    unfold afterStepGenerating
    ring
  rw [hav]
  by_cases hxA : x ∈ A
  · simp only [siteWeight, dif_pos hxA] at hh
    simp only [extendZero, dif_pos hxA]
    nlinarith
  · simp only [siteWeight, dif_neg hxA, one_mul] at hh
    rw [extendZero_not_mem A _ x hxA]
    linarith

 theorem generating_green_representation_integrable (D A : Finset Site) (hAD : A ⊆ D) (v : A → ℝ)
    (hI : ∀ y : Site, Integrable (fun ω ↦ markMonomial v (killedMark D A y ω)) pathLaw) (x : Site) :
    killedGenerating D A v x - 1 = observationLift D A
      (fun z : A ↦ (v z - 1) * afterStepGenerating D A v z) x := by
  let c : A → ℝ := fun z ↦ (v z - 1) * afterStepGenerating D A v z
  have hz : ∀ y, y ∉ D → killedGenerating D A v y - 1 = 0 := by
    intro y hy
    rw [killedGenerating_eq_one_of_not_mem D A v y hy, sub_self]
  rw [green_representation D (fun y ↦ killedGenerating D A v y - 1) hz x]
  calc
    _ = ∑ y ∈ D, killedGreen D x y * extendZero A c y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [generating_poisson_integrable D A v hI y hy]
    _ = ∑ y ∈ A, killedGreen D x y * extendZero A c y := by
      apply (Finset.sum_subset hAD ?_).symm
      intro y hy hyA
      rw [extendZero_not_mem A c y hyA, mul_zero]
    _ = _ := by
      rw [← Finset.sum_coe_sort A (fun y ↦ killedGreen D x y * extendZero A c y)]
      unfold observationLift
      apply Finset.sum_congr rfl
      intro y hy
      rw [extendZero_mem]

end SRWTightness
