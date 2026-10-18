import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
namespace SRWTightness

/-- Equal past laws and a common measurable endpoint kernel determine the joint law. -/
theorem joint_law_from_past_kernel {Ω Ω' E F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P : Ω → E) (Q : Ω' → E) (X : Ω → F) (Y : Ω' → F)
    (hP : Measurable P) (hQ : Measurable Q) (hX : Measurable X) (hY : Measurable Y)
    (K : Set F → E → ℝ) (hK : ∀ B, MeasurableSet B → Measurable (K B))
    (hpast : μ.map P = ν.map Q)
    (hμ : ∀ A B, MeasurableSet A → MeasurableSet B →
      μ.real {ω | P ω ∈ A ∧ X ω ∈ B} = ∫ ω in P ⁻¹' A, K B (P ω) ∂μ)
    (hν : ∀ A B, MeasurableSet A → MeasurableSet B →
      ν.real {ω | Q ω ∈ A ∧ Y ω ∈ B} = ∫ ω in Q ⁻¹' A, K B (Q ω) ∂ν) :
    μ.map (fun ω ↦ (P ω, X ω)) = ν.map (fun ω ↦ (Q ω, Y ω)) := by
  apply Measure.ext_prod
  intro A B hA hB
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (μ.map (fun ω ↦ (P ω, X ω))).real (A ×ˢ B) =
    (ν.map (fun ω ↦ (Q ω, Y ω))).real (A ×ˢ B)
  rw [map_measureReal_apply (hP.prodMk hX) (hA.prod hB),
    map_measureReal_apply (hQ.prodMk hY) (hA.prod hB)]
  change μ.real {ω | P ω ∈ A ∧ X ω ∈ B} = ν.real {ω | Q ω ∈ A ∧ Y ω ∈ B}
  rw [hμ A B hA hB, hν A B hA hB,
    ← setIntegral_map hA (hK B hB).aestronglyMeasurable hP.aemeasurable,
    ← setIntegral_map hA (hK B hB).aestronglyMeasurable hQ.aemeasurable, hpast]

end SRWTightness
