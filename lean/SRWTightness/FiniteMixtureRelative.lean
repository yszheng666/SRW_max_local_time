import SRWTightness.MarkEntranceDecomposition

namespace SRWTightness

/-- Relative entrance errors propagate through a nonnegative mixture including a large zero atom. -/
theorem finite_mixture_relative_error {ι : Type*} (S : Finset ι) (u v t : ι → ℝ)
    (t₀ ε : ℝ) (ht₀ : 0 ≤ t₀) (hε : 0 ≤ ε)
    (hv : ∀ i ∈ S, 0 ≤ v i) (ht : ∀ i ∈ S, 0 ≤ t i)
    (hmass : ∑ i ∈ S, v i ≤ 1 / 2)
    (hu : ∀ i ∈ S, |u i - v i| ≤ ε * v i) :
    |(t₀ + ∑ i ∈ S, u i * (t i - t₀)) -
      (t₀ + ∑ i ∈ S, v i * (t i - t₀))| ≤
      ε * (t₀ + ∑ i ∈ S, v i * (t i - t₀)) := by
  have hp (i : ι) (hi : i ∈ S) :
      |(u i - v i) * (t i - t₀)| ≤ ε * (v i * (t i + t₀)) := by
    have hb : |t i - t₀| ≤ t i + t₀ := by
      apply abs_le.mpr
      constructor <;> linarith [ht i hi]
    rw [abs_mul]
    calc
      _ ≤ (ε * v i) * (t i + t₀) :=
        mul_le_mul (hu i hi) hb (abs_nonneg _) (mul_nonneg hε (hv i hi))
      _ = _ := by ring
  have hs : (∑ i ∈ S, v i * (t i + t₀)) ≤ t₀ + ∑ i ∈ S, v i * (t i - t₀) := by
    simp_rw [mul_add, mul_sub]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
    nlinarith [mul_le_mul_of_nonneg_right hmass ht₀]
  have he : (t₀ + ∑ i ∈ S, u i * (t i - t₀)) -
      (t₀ + ∑ i ∈ S, v i * (t i - t₀)) =
      ∑ i ∈ S, (u i - v i) * (t i - t₀) := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ ∑ i ∈ S, |(u i - v i) * (t i - t₀)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, ε * (v i * (t i + t₀)) := Finset.sum_le_sum hp
    _ = ε * ∑ i ∈ S, v i * (t i + t₀) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hε

end SRWTightness
