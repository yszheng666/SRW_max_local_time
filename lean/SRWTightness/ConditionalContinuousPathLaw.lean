import Mathlib.Probability.ConditionalProbability
import Mathlib.Topology.Bases
import Mathlib.Topology.DenseEmbedding
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory TopologicalSpace

namespace SRWTightness

/-- Conditioning commutes with a measurable path map for an almost-everywhere preimage event. -/
theorem conditional_map_of_ae_preimage {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) (F : Ω → E) (hF : Measurable F)
    (A : Set Ω) (B : Set E) (hB : MeasurableSet B) (hA : A =ᵐ[μ] F ⁻¹' B) :
    (cond μ A).map F = cond (μ.map F) B := by
  unfold ProbabilityTheory.cond
  rw [measure_congr hA, Measure.restrict_congr_set hA, Measure.map_smul,
    ← Measure.restrict_map hF hB, Measure.map_apply hF hB]

/-- Equal laws of almost surely continuous paths remain equal after nonnegative conditioning. -/
theorem continuous_path_nonnegative_conditional_law_eq {Ω ι : Type*}
    [MeasurableSpace Ω] [TopologicalSpace ι] [SeparableSpace ι] [Nonempty ι]
    (μ : Measure Ω) (F G : Ω → ι → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hcF : ∀ᵐ ω ∂μ, Continuous (F ω)) (hcG : ∀ᵐ ω ∂μ, Continuous (G ω))
    (hlaw : μ.map F = μ.map G) :
    (cond μ {ω | ∀ t, 0 ≤ F ω t}).map F =
      (cond μ {ω | ∀ t, 0 ≤ G ω t}).map G := by
  obtain ⟨d, hd⟩ := exists_dense_seq ι
  let B : Set (ι → ℝ) := {f | ∀ n : ℕ, 0 ≤ f (d n)}
  have hB : MeasurableSet B := by
    simp only [B, Set.setOf_forall]
    exact MeasurableSet.iInter (fun n ↦ measurableSet_le measurable_const
      (measurable_pi_apply (d n)))
  have he (H : Ω → ι → ℝ) (hc : ∀ᵐ ω ∂μ, Continuous (H ω)) :
      {ω | ∀ t, 0 ≤ H ω t} =ᵐ[μ] H ⁻¹' B := by
    filter_upwards [hc] with ω hω
    apply propext
    change (∀ t, 0 ≤ H ω t) ↔ ∀ n : ℕ, 0 ≤ H ω (d n)
    constructor
    · intro h n
      exact h (d n)
    · intro h t
      exact hd.induction_on t (isClosed_le continuous_const hω) h
  rw [conditional_map_of_ae_preimage μ F hF _ B hB (he F hcF),
    conditional_map_of_ae_preimage μ G hG _ B hB (he G hcG), hlaw]

end SRWTightness
