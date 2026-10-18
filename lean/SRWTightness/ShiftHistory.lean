import SRWTightness.Shift
import SRWTightness.Filtration

open MeasureTheory

namespace SRWTightness

 theorem measurable_direction_history {i n : ℕ} (h : i < n) :
    Measurable[history n] (fun ω : Sample ↦ ω i) := by
  letI : MeasurableSpace Sample := history n
  have hr : Measurable[history n] ((Finset.range n).restrict :
      Sample → (j : Finset.range n) → Direction) :=
    measurable_iff_comap_le.mpr le_rfl
  exact (measurable_pi_apply (⟨i, Finset.mem_range.mpr h⟩ : Finset.range n)).comp hr

/-- Observing k future increments after time n only uses the first n+k increments. -/
theorem measurable_shift_history (n k : ℕ) :
    @Measurable Sample Sample (history (n + k)) (history k) (shift n) := by
  apply measurable_iff_comap_le.mpr
  change MeasurableSpace.comap (shift n)
    (MeasurableSpace.comap (fun ω : Sample ↦ fun i : Finset.range k ↦ ω i) inferInstance) ≤ _
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (fun ω : Sample ↦ fun i : Finset.range k ↦ ω (n + i))
    inferInstance ≤ _
  rw [MeasurableSpace.comap_process_pi]
  apply iSup_le
  intro i
  exact (measurable_direction_history (Nat.add_lt_add_left
    (Finset.mem_range.mp i.property) n)).comap_le

end SRWTightness
