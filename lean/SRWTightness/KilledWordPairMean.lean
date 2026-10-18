import SRWTightness.KilledWordRootMean

open MeasureTheory
namespace SRWTightness

/-- Future roots of both labels are counted on one killed walk, without independence. -/
theorem integral_killedWordMark_pair_roots (hLast : FiniteLastVisitCountInput)
    (D L₁ C₁ L₂ C₂ : Finset Site) (hL₁C : L₁ ⊆ C₁) (hL₂C : L₂ ⊆ C₂)
    (hC₁D : C₁ ⊆ D) (hC₂D : C₂ ⊆ D) (x : Site) :
    (∫ Y, ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ)
      ∂killedWordMarkLaw D x) =
      (∑ y ∈ L₁, killedGreen D x y * equilibriumMeasure C₁ L₁ y) +
      ∑ y ∈ L₂, killedGreen D x y * equilibriumMeasure C₂ L₂ y := by
  simp only [Nat.cast_add]
  rw [integral_add
    (integrable_killedWordMark_roots hLast D L₁ C₁ hL₁C hC₁D x)
    (integrable_killedWordMark_roots hLast D L₂ C₂ hL₂C hC₂D x),
    integral_killedWordMark_roots hLast D L₁ C₁ hL₁C hC₁D x,
    integral_killedWordMark_roots hLast D L₂ C₂ hL₂C hC₂D x]

/-- Only Green bounds on nonzero equilibrium support are needed for future-root means. -/
theorem killedWordMark_root_mean_le (hLast : FiniteLastVisitCountInput)
    (D L C : Finset Site) (hLC : L ⊆ C) (hCD : C ⊆ D) (x : Site) (B : ℝ)
    (hG : ∀ y ∈ L, equilibriumMeasure C L y ≠ 0 → killedGreen D x y ≤ B) :
    (∫ Y, (wordMarkRootCount L C Y : ℝ) ∂killedWordMarkLaw D x) ≤
      B * capacity C L := by
  rw [integral_killedWordMark_roots hLast D L C hLC hCD x, capacity, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  by_cases he : equilibriumMeasure C L y = 0
  · simp [he]
  · exact mul_le_mul_of_nonneg_right (hG y hy he) (equilibriumMeasure_nonneg C L y)

/-- The two future-root Green bounds retain their separate short capacities. -/
theorem killedWordMark_pair_mean_le (hLast : FiniteLastVisitCountInput)
    (D L₁ C₁ L₂ C₂ : Finset Site) (hL₁C : L₁ ⊆ C₁) (hL₂C : L₂ ⊆ C₂)
    (hC₁D : C₁ ⊆ D) (hC₂D : C₂ ⊆ D) (x : Site) (B₁ B₂ : ℝ)
    (hG₁ : ∀ y ∈ L₁, equilibriumMeasure C₁ L₁ y ≠ 0 → killedGreen D x y ≤ B₁)
    (hG₂ : ∀ y ∈ L₂, equilibriumMeasure C₂ L₂ y ≠ 0 → killedGreen D x y ≤ B₂) :
    (∫ Y, ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ)
      ∂killedWordMarkLaw D x) ≤ B₁ * capacity C₁ L₁ + B₂ * capacity C₂ L₂ := by
  simp only [Nat.cast_add]
  rw [integral_add
    (integrable_killedWordMark_roots hLast D L₁ C₁ hL₁C hC₁D x)
    (integrable_killedWordMark_roots hLast D L₂ C₂ hL₂C hC₂D x)]
  exact add_le_add (killedWordMark_root_mean_le hLast D L₁ C₁ hL₁C hC₁D x B₁ hG₁)
    (killedWordMark_root_mean_le hLast D L₂ C₂ hL₂C hC₂D x B₂ hG₂)

end SRWTightness
