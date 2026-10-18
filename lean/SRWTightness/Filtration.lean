import SRWTightness.Exit

open MeasureTheory

namespace SRWTightness

/-- Information from exactly the first n increments. -/
def history : Filtration ℕ (inferInstance : MeasurableSpace Sample) where
  seq n := Filtration.piFinset (X := fun _ : ℕ ↦ Direction) (Finset.range n)
  mono' := fun _ _ h ↦ Filtration.piFinset.mono (Finset.range_mono h)
  le' := fun n ↦ Filtration.piFinset.le (Finset.range n)

 theorem history_measurable_prefix (n : ℕ) :
    Measurable[history n] (fun ω : Sample ↦ fun k : Fin n ↦ ω k) := by
  letI : MeasurableSpace Sample := history n
  have hr : Measurable[history n] ((Finset.range n).restrict :
      Sample → (i : Finset.range n) → Direction) :=
    measurable_iff_comap_le.mpr le_rfl
  exact measurable_pi_lambda _ (fun k ↦
    (measurable_pi_apply (⟨(k : ℕ), Finset.mem_range.mpr k.isLt⟩ : Finset.range n)).comp hr)

 theorem adapted_position : Adapted history (fun n ω ↦ position ω n) := by
  intro n
  letI : MeasurableSpace Sample := history n
  have hm := (measurable_of_countable
    (fun w : Fin n → Direction ↦ position (extendWord w) n)).comp
    (history_measurable_prefix n)
  convert hm using 1
  funext ω
  apply position_congr
  intro k hk
  simp [extendWord, hk]

 theorem exitTime_isStoppingTime (R : ℝ) : IsStoppingTime history (exitTime R) := by
  exact adapted_position.isStoppingTime_hittingAfter (Set.to_countable _).measurableSet

end SRWTightness
