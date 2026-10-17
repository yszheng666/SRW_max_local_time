import SRWTightness.SupportedRecordComparison

open MeasureTheory

namespace SRWTightness

/-- Returning from a root exit costs one factor rho for each further prescribed root. -/
theorem supported_return_forest_upper {X R : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (U : X → Measure X) (S : X → R → Measure X) (V : X → ℝ) (A B : Set X)
    (hUf : ∀ x, IsFiniteMeasure (U x)) (hSf : ∀ z r, IsFiniteMeasure (S z r))
    (hUs : ∀ x ∈ A, ∀ᵐ z ∂U x, z ∈ B)
    (hSs : ∀ z ∈ B, ∀ r, ∀ᵐ y ∂S z r, y ∈ A)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (W : R → ℝ) (hW : ∀ r, 0 ≤ W r)
    (hU : ∀ x ∈ A, (U x).real Set.univ ≤ ρ)
    (hV : ∀ x ∈ A, 0 ≤ V x ∧ V x ≤ 1)
    (hS : ∀ z ∈ B, ∀ r, (S z r).real Set.univ ≤ W r) :
    ∀ rs x, x ∈ A → 0 ≤ orderedRecordWeight U S V rs x ∧
      orderedRecordWeight U S V rs x ≤ ρ ^ rs.length * (rs.map W).prod := by
  intro rs
  induction rs with
  | nil => intro x hx; simpa only [orderedRecordWeight, List.length_nil, pow_zero,
      List.map_nil, List.prod_nil, mul_one] using hV x hx
  | cons r rs ih =>
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
      have hh := integral_bounds_on_support (S z r) A (hSs z hz r) _ 0 H (by norm_num) ih
      constructor
      · simpa only [zero_mul] using hh.1
      · exact hh.2.trans (mul_le_mul_of_nonneg_left (hS z hz r) hH)
    intro x hx
    letI := hUf x
    have hh := integral_bounds_on_support (U x) B (hUs x hx) g 0 (H * W r)
      (by norm_num) hg
    constructor
    · simpa only [zero_mul, orderedRecordWeight] using hh.1
    · calc
        orderedRecordWeight U S V (r :: rs) x ≤ (H * W r) * (U x).real Set.univ := hh.2
        _ ≤ (H * W r) * ρ :=
          mul_le_mul_of_nonneg_left (hU x hx) (mul_nonneg hH (hW r))
        _ = ρ ^ (r :: rs).length * ((r :: rs).map W).prod := by
          simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ, H]
          ring

end SRWTightness
