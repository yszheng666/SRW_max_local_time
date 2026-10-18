import SRWTightness.FiniteFirstCrossingEvents
import SRWTightness.FinitePartitionEventLaw
import SRWTightness.FiniteReflectedCrossing

open MeasureTheory
namespace SRWTightness

/-- First-crossing reflection gives two-sided finite-grid bounds
with an explicit overshoot error. -/
theorem finite_reflection_probability_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (W : ℕ → Ω → ℝ)
    (hW : ∀ k, Measurable (W k)) (n : ℕ) (q b δ : ℝ)
    (hzero : ∀ ω, W 0 ω < q) (hb : b < q) (hδ : 0 ≤ δ)
    (hreflect : ∀ k ≤ n,
      μ.real (firstCrossingEvent W q k ∩ {ω | W n ω ≤ b}) =
      μ.real (firstCrossingEvent W q k ∩ {ω | 2 * W k ω - W n ω ≤ b})) :
    μ.real {ω | (∃ k ≤ n, q ≤ W k ω) ∧ W n ω ≤ b} ≤
      μ.real {ω | 2 * q - b ≤ W n ω} ∧
    μ.real {ω | 2 * (q + δ) - b ≤ W n ω} -
      μ.real {ω | ∃ j < n, δ < W (j + 1) ω - W j ω} ≤
      μ.real {ω | (∃ k ≤ n, q ≤ W k ω) ∧ W n ω ≤ b} := by
  let A : Fin (n + 1) → Set Ω := fun k ↦ firstCrossingEvent W q k
  let F : Fin (n + 1) → Set Ω := fun k ↦ {ω | 2 * W k ω - W n ω ≤ b}
  have hA (k : Fin (n + 1)) : MeasurableSet (A k) :=
    firstCrossingEvent_measurable W hW q k
  have hF (k : Fin (n + 1)) : MeasurableSet (F k) :=
    measurableSet_le ((measurable_const.mul (hW k)).sub (hW n)) measurable_const
  have hd : Pairwise (fun j k ↦ Disjoint (A j) (A k)) := by
    intro j k hjk
    exact firstCrossingEvent_disjoint W q (fun he ↦ hjk (Fin.ext he))
  have he := finite_partition_event_law μ A F {ω | W n ω ≤ b} hA hF
    (measurableSet_le (hW n) measurable_const) hd (fun k ↦ hreflect k (by omega))
  have hcov : (⋃ k, A k) = {ω | ∃ k ≤ n, q ≤ W k ω} := firstCrossingEvent_union W q n
  rw [hcov] at he
  change μ.real {ω | (∃ k ≤ n, q ≤ W k ω) ∧ W n ω ≤ b} = _ at he
  rw [he]
  constructor
  · refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hω
    exact reflected_crossing_endpoint_lower (fun j ↦ W j ω) q b n k hk.1.1 hk.2
  · apply le_trans le_measureReal_sdiff
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    have hs : ∀ j < n, W (j + 1) ω - W j ω ≤ δ := by
      intro j hj
      exact le_of_not_gt (fun h ↦ hω.2 ⟨j, hj, h⟩)
    obtain ⟨k, hkn, hk, hend⟩ := high_endpoint_reflected_first_crossing
      (fun j ↦ W j ω) q b δ n (hzero ω) hb hδ hs hω.1
    exact Set.mem_iUnion.mpr ⟨⟨k, by omega⟩, hk, hend⟩

end SRWTightness
