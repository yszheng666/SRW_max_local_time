import SRWTightness.MarkTest

open MeasureTheory

namespace SRWTightness

noncomputable def markMonomial {K : Finset Site} (v : K → ℝ) (Y : Mark K) : ℝ :=
  ∏ z : K, v z ^ Y z

 theorem measurable_markMonomial {K : Finset Site} (v : K → ℝ) : Measurable (markMonomial v) := by
  apply Finset.measurable_prod
  intro z hz
  exact (measurable_of_countable (fun n : ℕ ↦ v z ^ n)).comp (measurable_pi_apply z)

 theorem markMonomial_nonneg {K : Finset Site} (v : K → ℝ) (hv : ∀ z, 0 ≤ v z) (Y : Mark K) :
    0 ≤ markMonomial v Y := Finset.prod_nonneg (fun z _ ↦ pow_nonneg (hv z) _)

 theorem markMonomial_le_one {K : Finset Site} (v : K → ℝ) (hv0 : ∀ z, 0 ≤ v z)
    (hv1 : ∀ z, v z ≤ 1) (Y : Mark K) : markMonomial v Y ≤ 1 :=
  Finset.prod_le_one (fun z _ ↦ pow_nonneg (hv0 z) _) (fun z _ ↦ pow_le_one₀ (hv0 z) (hv1 z))

 theorem norm_markMonomial_le_one {K : Finset Site} (v : K → ℝ) (hv0 : ∀ z, 0 ≤ v z)
    (hv1 : ∀ z, v z ≤ 1) (Y : Mark K) : ‖markMonomial v Y‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (markMonomial_nonneg v hv0 Y)]
  exact markMonomial_le_one v hv0 hv1 Y

@[simp] theorem markMonomial_zero {K : Finset Site} (v : K → ℝ) : markMonomial v 0 = 1 := by
  simp [markMonomial]

noncomputable def siteWeight (K : Finset Site) (v : K → ℝ) (x : Site) : ℝ :=
  if hx : x ∈ K then v ⟨x, hx⟩ else 1

 theorem monomial_initial_visit (K : Finset Site) (v : K → ℝ) (x : Site) :
    (∏ z : K, v z ^ (if x = (z : Site) then 1 else 0)) = siteWeight K v x := by
  classical
  by_cases hx : x ∈ K
  · let xx : K := ⟨x, hx⟩
    have he (z : K) : x = (z : Site) ↔ z = xx := by
      constructor
      · exact fun h ↦ Subtype.ext h.symm
      · rintro rfl
        rfl
    simp only [he]
    simp [siteWeight, hx, xx]
  · have he (z : K) : x ≠ (z : Site) := fun h ↦ hx (h ▸ z.property)
    simp [siteWeight, hx, he]

 theorem monomial_first_step (D K : Finset Site) (v : K → ℝ) (x : Site) (hx : x ∈ D)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    markMonomial v (killedMark D K x ω) = siteWeight K v x *
      markMonomial v (killedMark D K (x + step (ω 0)) (shift 1 ω)) := by
  unfold markMonomial killedMark
  simp_rw [domainLocalTime_first_step D x _ hx ω hfin, pow_add]
  rw [Finset.prod_mul_distrib, monomial_initial_visit]

noncomputable def killedGenerating (D K : Finset Site) (v : K → ℝ) (x : Site) : ℝ :=
  markTestExpectation D K (markMonomial v) x

 theorem killedGenerating_eq_one_of_not_mem (D K : Finset Site) (v : K → ℝ)
    (x : Site) (hx : x ∉ D) : killedGenerating D K v x = 1 := by
  rw [killedGenerating, markTestExpectation_eq_of_not_mem D K _ x hx, markMonomial_zero]

 theorem killedGenerating_first_step (D K : Finset Site) (v : K → ℝ)
    (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∀ z, v z ≤ 1) (x : Site) (hx : x ∈ D) :
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
    (fun d ↦ integrable_markTest D K _ (measurable_markMonomial v) 1
      (norm_markMonomial_le_one v hv0 hv1) _), integral_direction_average]

end SRWTightness
