import SRWTightness.PairChernoffBound
import SRWTightness.SourcePairUpperEvent

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Chernoff control of the actual retained pair event, with its full bridge constraint. -/
theorem source_pair_event_chernoff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t A : ℝ) (I i : ℕ)
    (F : Ω → PairObservationIndex (I - i + 1) → ℝ) (hF : Measurable F)
    (At d q f C ε : ℝ)
    (hX : Integrable (fun Y ↦ Real.exp (2 * F Y (.inr false) +
      2 * F Y (.inr true) - 2 * F Y (.inl (Fin.last (I - i))))) μ)
    (hΛ : cgf (fun Y ↦ 2 * F Y (.inr false) + 2 * F Y (.inr true) -
      2 * F Y (.inl (Fin.last (I - i)))) μ 1 ≤
        4 * d - 2 * sourceObservationTime t A I (I - i + 1) + C)
    (hAt : 2 * d + q - ε ≤ At) :
    ((μ.map F).prod (independentBridgeLaw ℕ)).real (sourcePairUpperEvent t A I i At q f) ≤
      Real.exp (C + 4 * ε) * Real.exp (-2 * d -
        2 * (d - sourceObservationTime t A I (I - i + 1)) - 2 * q - 2 * f) := by
  have hm := Measure.map_prod_map μ (independentBridgeLaw ℕ) hF measurable_id
  rw [Measure.map_id] at hm
  rw [hm, map_measureReal_apply (hF.prodMap measurable_id)
    (sourcePairUpperEvent_measurable t A I i At q f)]
  apply pair_chernoff_bound μ (independentBridgeLaw ℕ)
    (fun Y ↦ F Y (.inr false)) (fun Y ↦ F Y (.inr true))
    (fun Y ↦ F Y (.inl (Fin.last (I - i)))) hX _
    ((sourcePairUpperEvent_measurable t A I i At q f).preimage
      (hF.prodMap measurable_id)) At d (sourceObservationTime t A I (I - i + 1)) q f C ε
    hΛ hAt
  · exact fun _ hp ↦ hp.1
  · exact fun _ hp ↦ hp.2.1
  · exact fun _ hp ↦ hp.2.2.1

end SRWTightness
