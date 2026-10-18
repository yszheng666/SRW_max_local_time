import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
namespace SRWTightness

/-- Real conditional probabilities retain their original normalized intersection formula. -/
theorem conditional_real_apply {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (H S : Set Ω) (hH : MeasurableSet H) :
    (ProbabilityTheory.cond μ H).real S = μ.real (S ∩ H) / μ.real H := by
  unfold Measure.real
  rw [ProbabilityTheory.cond_apply hH, ENNReal.toReal_mul, ENNReal.toReal_inv, Set.inter_comm H S]
  exact (div_eq_inv_mul _ _).symm

/-- A finite collection of disjoint record atoms can be bounded inside an original event, retaining
its original measure. Only almost-everywhere containment of the atoms is needed. -/
theorem finite_reference_count_lower {Ω R ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → R) (r : ι → R)
    (hr : Function.Injective r) (s : Finset ι) (q : ι → ℝ) (F : ℝ) (S : Set Ω)
    (hf : ∀ i ∈ s, MeasurableSet {ω | f ω = r i})
    (hsub : ∀ᵐ ω ∂μ, ∀ i ∈ s, f ω = r i → ω ∈ S)
    (h : ∀ i ∈ s, q i ≤ Real.exp F * μ.real {ω | f ω = r i}) :
    (∑ i ∈ s, q i) ≤ Real.exp F * μ.real S := by
  have hd : Set.PairwiseDisjoint (↑s) (fun i ↦ {ω | f ω = r i}) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact hij (hr (hi.symm.trans hj))
  have hU : ∀ᵐ ω ∂μ, ω ∈ (⋃ i ∈ s, {ω | f ω = r i}) → ω ∈ S := by
    filter_upwards [hsub] with ω hω
    intro hu
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
    obtain ⟨his, hfi⟩ := Set.mem_iUnion.mp hi
    exact hω i his hfi
  have hμ : μ.real (⋃ i ∈ s, {ω | f ω = r i}) ≤ μ.real S :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hU)
  calc
    _ ≤ ∑ i ∈ s, Real.exp F * μ.real {ω | f ω = r i} := Finset.sum_le_sum h
    _ = Real.exp F * μ.real (⋃ i ∈ s, {ω | f ω = r i}) := by
      rw [← Finset.mul_sum, measureReal_biUnion_finset hd hf]
    _ ≤ _ := mul_le_mul_of_nonneg_left hμ (Real.exp_pos _).le

end SRWTightness
