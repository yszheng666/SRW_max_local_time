import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- A restricted record comparison bounds any original event whose records lie almost surely
in both the good region and the reference event. -/
theorem restricted_event_comparison {Ω R : Type*} [MeasurableSpace Ω] [MeasurableSpace R]
    (μ : Measure Ω) (η ξ : Measure R) (f : Ω → R) (hf : MeasurePreserving f μ η)
    (G T : Set R) (hG : MeasurableSet G) (hT : MeasurableSet T) (c : ℝ≥0∞)
    (hdom : η.restrict G ≤ c • ξ) (S : Set Ω)
    (hS : ∀ᵐ x ∂μ, x ∈ S → f x ∈ G ∧ f x ∈ T) :
    μ S ≤ c * ξ T := by
  calc
    μ S ≤ μ (f ⁻¹' (T ∩ G)) := measure_mono_ae (hS.mono (fun _ hx hs ↦
      ⟨(hx hs).2, (hx hs).1⟩))
    _ = η (T ∩ G) := hf.measure_preimage (hT.inter hG).nullMeasurableSet
    _ = η.restrict G T := (Measure.restrict_apply hT).symm
    _ ≤ (c • ξ) T := hdom T
    _ = c * ξ T := Measure.smul_apply c ξ T

/-- The real-valued form retains the finite reference-event mass, so no infinite mass is hidden
by conversion from extended nonnegative reals. -/
theorem restricted_event_comparison_real {Ω R : Type*} [MeasurableSpace Ω]
    [MeasurableSpace R] (μ : Measure Ω) (η ξ : Measure R) [IsFiniteMeasure ξ]
    (f : Ω → R) (hf : MeasurePreserving f μ η)
    (G T : Set R) (hG : MeasurableSet G) (hT : MeasurableSet T) (E : ℝ)
    (hdom : η.restrict G ≤ ENNReal.ofReal (Real.exp E) • ξ) (S : Set Ω)
    (hS : ∀ᵐ x ∂μ, x ∈ S → f x ∈ G ∧ f x ∈ T) :
    μ.real S ≤ Real.exp E * ξ.real T := by
  have hb := restricted_event_comparison μ η ξ f hf G T hG hT _ hdom S hS
  have ht : ENNReal.ofReal (Real.exp E) * ξ T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ξ T)
  have hr := ENNReal.toReal_mono ht hb
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos E).le] using hr

end SRWTightness
