import SRWTightness.SupportedForestUpper

open MeasureTheory

namespace SRWTightness

/-- The first entrance costs at most one; only the subsequent roots incur return factors. -/
theorem supported_initial_forest_upper {X R : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (U : X → Measure X) (S : X → R → Measure X) (V : X → ℝ) (A B : Set X)
    (hUf : ∀ x, IsFiniteMeasure (U x)) (hSf : ∀ z r, IsFiniteMeasure (S z r))
    (hUs : ∀ x ∈ A, ∀ᵐ z ∂U x, z ∈ B)
    (hSs : ∀ z ∈ B, ∀ r, ∀ᵐ y ∂S z r, y ∈ A)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (W : R → ℝ) (hW : ∀ r, 0 ≤ W r)
    (hU : ∀ x ∈ A, (U x).real Set.univ ≤ ρ)
    (hV : ∀ x ∈ A, 0 ≤ V x ∧ V x ≤ 1)
    (hS : ∀ z ∈ B, ∀ r, (S z r).real Set.univ ≤ W r) (x : X) (hUx : (U x).real Set.univ ≤ 1)
    (hUsx : ∀ᵐ z ∂U x, z ∈ B) (r : R) (rs : List R) :
    0 ≤ orderedRecordWeight U S V (r :: rs) x ∧
      orderedRecordWeight U S V (r :: rs) x ≤
        ρ ^ rs.length * ((r :: rs).map W).prod := by
  have htail := supported_return_forest_upper U S V A B hUf hSf hUs hSs ρ hρ W hW hU hV hS rs
  have hp : 0 ≤ (rs.map W).prod := by
    apply List.prod_nonneg
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact hW v
  let H := ρ ^ rs.length * (rs.map W).prod
  have hH : 0 ≤ H := mul_nonneg (pow_nonneg hρ _) hp
  let g := fun z ↦ ∫ y, orderedRecordWeight U S V rs y ∂S z r
  have hg : ∀ z ∈ B, 0 ≤ g z ∧ g z ≤ H * W r := by
    intro z hz
    letI := hSf z r
    have hh := integral_bounds_on_support (S z r) A (hSs z hz r) _ 0 H (by norm_num) htail
    exact ⟨by simpa only [zero_mul] using hh.1,
      hh.2.trans (mul_le_mul_of_nonneg_left (hS z hz r) hH)⟩
  letI := hUf x
  have hh := integral_bounds_on_support (U x) B hUsx g 0 (H * W r) (by norm_num) hg
  constructor
  · simpa only [zero_mul, orderedRecordWeight] using hh.1
  · calc
      orderedRecordWeight U S V (r :: rs) x ≤ (H * W r) * (U x).real Set.univ := hh.2
      _ ≤ (H * W r) * 1 := mul_le_mul_of_nonneg_left hUx (mul_nonneg hH (hW r))
      _ = ρ ^ rs.length * ((r :: rs).map W).prod := by
        simp only [List.map_cons, List.prod_cons, H]
        ring

end SRWTightness
