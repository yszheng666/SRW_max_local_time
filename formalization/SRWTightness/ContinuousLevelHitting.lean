import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

namespace SRWTightness

/-- A continuous path starting above a level can cross below it only by hitting that level. -/
theorem continuous_lower_hit_iff_level (f : ℝ → ℝ) (hf : Continuous f) (b : ℝ)
    (h0 : b ≤ f 0) :
    (∃ t ∈ Set.Ici (0 : ℝ), f t ≤ b) ↔ ∃ t ∈ Set.Ici (0 : ℝ), f t = b := by
  constructor
  · rintro ⟨t, ht, hb⟩
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc' ht hf.continuousOn ⟨hb, h0⟩
    exact ⟨s, hs.1, he⟩
  · rintro ⟨t, ht, he⟩
    exact ⟨t, ht, he.le⟩

/-- A continuous path starting below a level hits it before reaching any later value above it. -/
theorem continuous_level_hit_of_above (f : ℝ → ℝ) (hf : Continuous f) (b t : ℝ)
    (h0 : f 0 ≤ b) (ht : 0 ≤ t) (hb : b ≤ f t) :
    ∃ s ∈ Set.Ici (0 : ℝ), f s = b := by
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc ht hf.continuousOn ⟨h0, hb⟩
  exact ⟨s, hs.1, he⟩

end SRWTightness
