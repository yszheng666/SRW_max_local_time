import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory
namespace SRWTightness

/-- A property verified on every positive atom holds almost everywhere for any countable record. -/
theorem ae_support_of_positive_atoms {Ω R : Type*} [MeasurableSpace Ω] [Countable R]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → R) (P : R → Prop)
    (h : ∀ r, 0 < μ.real {ω | f ω = r} → P r) : ∀ᵐ ω ∂μ, P (f ω) := by
  have hs (r : R) : ∀ᵐ ω ∂μ, f ω = r → P r := by
    by_cases hp : P r
    · exact Filter.Eventually.of_forall (fun _ _ ↦ hp)
    · have hz : μ.real {ω | f ω = r} = 0 :=
        le_antisymm (le_of_not_gt (fun hr ↦ hp (h r hr))) measureReal_nonneg
      have hn : ∀ᵐ ω ∂μ, f ω ≠ r :=
        measure_eq_zero_iff_ae_notMem.mp ((measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz)
      filter_upwards [hn] with ω hω
      exact fun he ↦ False.elim (hω he)
  filter_upwards [ae_all_iff.mpr hs] with ω hω
  exact hω (f ω) rfl

/-- Positive record atoms inherit every almost-sure property of that record. -/
theorem support_of_positive_atom {Ω R : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → R) (P : R → Prop)
    (h : ∀ᵐ ω ∂μ, P (f ω)) (r : R) (hr : 0 < μ.real {ω | f ω = r}) : P r := by
  by_contra hp
  have hn : ∀ᵐ ω ∂μ, f ω ≠ r := h.mono (fun ω hω he ↦ hp (he ▸ hω))
  have hz : μ {ω | f ω = r} = 0 := measure_eq_zero_iff_ae_notMem.mpr hn
  exact hr.ne' ((measureReal_eq_zero_iff (measure_ne_top _ _)).mpr hz)

end SRWTightness
