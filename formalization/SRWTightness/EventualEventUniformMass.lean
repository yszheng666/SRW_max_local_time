import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open MeasureTheory Filter
namespace SRWTightness

/-- A uniform finite-measure bound passes to the event of eventual membership. -/
theorem eventual_event_uniform_mass (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Set Ω) (C : ℝ)
    (hC : 0 ≤ C) (hE : ∀ n, μ.real (E n) ≤ C) :
    μ.real {ω | ∀ᶠ n in atTop, ω ∈ E n} ≤ C := by
  let F : ℕ → Set Ω := fun N ↦ {ω | ∀ n ≥ N, ω ∈ E n}
  have hmono : Monotone F := by
    intro n m hnm ω hω j hj
    exact hω j (hnm.trans hj)
  have heq : {ω | ∀ᶠ n in atTop, ω ∈ E n} = ⋃ N, F N := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, F, eventually_atTop]
  have hμ : μ (⋃ N, F N) ≤ ENNReal.ofReal C := by
    rw [hmono.measure_iUnion]
    apply iSup_le
    intro N
    have hh : F N ⊆ E N := fun ω hω ↦ hω N le_rfl
    apply (measure_mono hh).trans
    rw [← ofReal_measureReal (measure_ne_top μ (E N))]
    exact ENNReal.ofReal_le_ofReal (hE N)
  rw [heq]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ).trans_eq
    (ENNReal.toReal_ofReal hC)

end SRWTightness
