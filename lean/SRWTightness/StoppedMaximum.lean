import SRWTightness.Filtration

open MeasureTheory

namespace SRWTightness

 theorem adapted_maxLocalTime : Adapted history (fun n ω ↦ maxLocalTime ω n) := by
  intro n
  letI : MeasurableSpace Sample := history n
  have hm := (measurable_of_countable
    (fun w : Fin n → Direction ↦ maxLocalTime (extendWord w) n)).comp
    (history_measurable_prefix n)
  convert hm using 1
  funext ω
  exact maxLocalTime_prefix ω n

noncomputable def stoppedMax (τ : Sample → WithTop ℕ) : Sample → ℕ :=
  stoppedValue (fun n ω ↦ maxLocalTime ω n) τ

 theorem measurable_stoppedMax (τ : Sample → WithTop ℕ) (hτ : IsStoppingTime history τ) :
    Measurable[hτ.measurableSpace] (stoppedMax τ) := by
  have hs : StronglyAdapted history (fun n ω ↦ maxLocalTime ω n) :=
    fun n ↦ (adapted_maxLocalTime n).stronglyMeasurable
  exact measurable_stoppedValue hs.isStronglyProgressive_of_discrete hτ

 theorem stoppedMax_eq (τ : Sample → WithTop ℕ) (ω : Sample) (h : τ ω ≠ ⊤) :
    stoppedMax τ ω = maxLocalTime ω ((τ ω).untopD 0) := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp h
  simp only [stoppedMax, stoppedValue, ← hk, WithTop.untopA]
  rfl

end SRWTightness
