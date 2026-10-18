import SRWTightness.IndependentPowerMoments
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Moments of a finite sum of independent centered variables with variance 1 and fourth moment 9. -/
theorem independent_centered_sum_moments {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (hI : ∀ i j, j ≤ 4 → Integrable (fun ω ↦ X i ω ^ j) μ)
    (h1 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    (h4 : ∀ i, ∫ ω, X i ω ^ 4 ∂μ = 9) (s : Finset ι) :
    (∀ j ≤ 4, Integrable (fun ω ↦ (∑ i ∈ s, X i ω) ^ j) μ) ∧
    (∫ ω, (∑ i ∈ s, X i ω) ∂μ) = 0 ∧
    (∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ) = s.card ∧
    (∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ) = 3 * (s.card : ℝ) ^ 2 + 6 * s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨hsI, hs1, hs2, hs4⟩ := ih
    have hd : IndepFun (X i) (fun ω ↦ ∑ j ∈ s, X j ω) μ := by
      simpa only [Finset.sum_fn] using (hInd.indepFun_finsetSum_of_notMem hXm hi).symm
    have hm (j : ℕ) (hj : j ≤ 4) := integral_independent_add_power μ (X i)
      (fun ω ↦ ∑ l ∈ s, X l ω) hd j
      (fun l hl ↦ hI i l (hl.trans hj)) (fun l hl ↦ hsI l (hl.trans hj))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      simpa only [Finset.sum_insert hi] using integrable_independent_add_power μ (X i)
        (fun ω ↦ ∑ l ∈ s, X l ω) hd j
        (fun l hl ↦ hI i l (hl.trans hj)) (fun l hl ↦ hsI l (hl.trans hj))
    · have he := hm 1 (by decide)
      norm_num [Finset.sum_range_succ, h1, hs1] at he
      simpa only [Finset.sum_insert hi] using he
    · have he := hm 2 (by decide)
      norm_num [Finset.sum_range_succ, h1, h2, hs1, hs2] at he
      simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_add,
        Nat.cast_one] using he
    · have he := hm 4 (by decide)
      norm_num [Finset.sum_range_succ, Nat.choose, h1, h2, h4, hs1, hs2, hs4] at he
      rw [show (fun ω ↦ (∑ j ∈ insert i s, X j ω) ^ 4) =
        (fun ω ↦ (X i ω + ∑ j ∈ s, X j ω) ^ 4) by funext ω; rw [Finset.sum_insert hi], he]
      rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      ring

end SRWTightness
