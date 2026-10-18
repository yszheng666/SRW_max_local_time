import SRWTightness.GeneratingFunction
import SRWTightness.OccupationExponential

open MeasureTheory

namespace SRWTightness

 theorem prod_le_one_add_sum_pow_card {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) : (∏ i, f i) ≤ 1 + ∑ i, (f i) ^ Fintype.card ι := by
  classical
  by_cases hn : (Finset.univ : Finset ι).Nonempty
  · obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ f hn
    have hp : (∏ i, f i) ≤ (f j) ^ Fintype.card ι := by
      calc
        _ ≤ ∏ _ : ι, f j := Finset.prod_le_prod (fun i _ ↦ hf i) hmax
        _ = _ := by simp
    have hs : (f j) ^ Fintype.card ι ≤ ∑ i, (f i) ^ Fintype.card ι :=
      Finset.single_le_sum (fun i _ ↦ pow_nonneg (hf i) _) hj
    linarith
  · have he : (Finset.univ : Finset ι) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]

 theorem markMonomial_bound (A : Finset Site) (v : A → ℝ) (b : ℝ)
    (hv0 : ∀ z, 0 ≤ v z) (hvb : ∀ z, v z ≤ b) (hb : 0 ≤ b) (Y : Mark A) :
    ‖markMonomial v Y‖ ≤ 1 + ∑ z : A, (b ^ Fintype.card A) ^ Y z := by
  rw [Real.norm_eq_abs, abs_of_nonneg (markMonomial_nonneg v hv0 Y)]
  calc
    _ ≤ ∏ z : A, b ^ Y z := Finset.prod_le_prod
      (fun z _ ↦ pow_nonneg (hv0 z) _) (fun z _ ↦ pow_le_pow_left₀ (hv0 z) (hvb z) _)
    _ ≤ 1 + ∑ z : A, (b ^ Y z) ^ Fintype.card A :=
      prod_le_one_add_sum_pow_card _ (fun z ↦ pow_nonneg hb _)
    _ = _ := by simp only [← pow_mul, Nat.mul_comm]

 theorem integrable_killedMonomial (D A : Finset Site) (v : A → ℝ) (b : ℝ)
    (hv0 : ∀ z, 0 ≤ v z) (hvb : ∀ z, v z ≤ b) (hb : 0 ≤ b)
    (hqb : ∀ z : A, (1 - 1 / killedGreen D z z) * b ^ Fintype.card A < 1)
    (x : Site) : Integrable (fun ω ↦ markMonomial v (killedMark D A x ω)) pathLaw := by
  have hi : Integrable (fun ω ↦ 1 + ∑ z : A,
      (b ^ Fintype.card A) ^ domainLocalTime D x z ω) pathLaw :=
    (integrable_const 1).add (integrable_finset_sum _ (fun z _ ↦
      integrable_domainLocalTime_pow D x z _ (pow_nonneg hb _) (hqb z)))
  apply hi.mono' ((measurable_markMonomial v).comp (measurable_killedMark D A x)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω ↦ markMonomial_bound A v b hv0 hvb hb _)

end SRWTightness
