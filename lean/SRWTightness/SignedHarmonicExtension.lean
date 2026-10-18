import SRWTightness.ExternalPositiveHarmonic
import SRWTightness.RecordExitSlice

namespace SRWTightness

/-- Clipping a shifted harmonic function below zero preserves harmonicity under local bounds. -/
theorem signed_harmonic_positive_extension (D : Finset Site) (f : Site → ℝ) (c M : ℝ)
    (hf : ∀ y ∈ D, f y = (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d))
    (hb : ∀ z, z ∈ D ∨ z ∈ domainExitBoundary D → |f z - c| ≤ M) :
    ∀ y ∈ D, max 0 (f y - c + M) =
      (1 / 4 : ℝ) * ∑ d : Direction, max 0 (f (y + step d) - c + M) := by
  intro y hy
  have hpos (z : Site) (hz : z ∈ D ∨ z ∈ domainExitBoundary D) : 0 ≤ f z - c + M := by
    have hh := (abs_le.mp (hb z hz)).1
    linarith
  rw [max_eq_right (hpos y (Or.inl hy))]
  have hn (d : Direction) : max 0 (f (y + step d) - c + M) = f (y + step d) - c + M := by
    apply max_eq_right
    apply hpos
    by_cases hd : y + step d ∈ D
    · exact Or.inl hd
    · exact Or.inr ⟨hd, y, hy, d, rfl⟩
  simp_rw [hn]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Direction, Fintype.card_fin, nsmul_eq_mul]
  linarith [hf y hy]

/-- Positive Harnack estimates imply a local signed oscillation bound after a bounded shift. -/
theorem signed_harmonic_local_difference (hH : PositiveHarmonicRelativeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : Site) (A B : ℝ), 1 ≤ A → 8 * A ≤ B →
      ∀ (f : Site → ℝ) (c M : ℝ), 0 ≤ M →
      (∀ y ∈ translateFinset b (diskFinset B),
        f y = (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d)) →
      (∀ z, z ∈ translateFinset b (diskFinset B) ∨
        z ∈ domainExitBoundary (translateFinset b (diskFinset B)) → |f z - c| ≤ M) →
      b ∈ translateFinset b (diskFinset B) →
      ∀ x ∈ translateFinset b (diskFinset (2 * A)),
      x ∈ translateFinset b (diskFinset B) → |f x - f b| ≤ C * M * (A / B) := by
  obtain ⟨C, hC, hrel⟩ := hH
  refine ⟨2 * C, by positivity, ?_⟩
  intro b A B hA hB f c M hM hf hb hbase x hx hxB
  have hg (z : Site) (hz : z ∈ translateFinset b (diskFinset B)) :
      max 0 (f z - c + M) = f z - c + M := by
    apply max_eq_right
    have hh := (abs_le.mp (hb z (Or.inl hz))).1
    linarith
  have hh := hrel b A B hA hB (fun z ↦ max 0 (f z - c + M))
    (fun z ↦ le_max_left _ _) (signed_harmonic_positive_extension _ f c M hf hb) x hx
  rw [hg x hxB, hg b hbase] at hh
  have he : (f x - c + M) - (f b - c + M) = f x - f b := by ring
  rw [he] at hh
  have hc : f b - c + M ≤ 2 * M := by
    have hp := (abs_le.mp (hb b (Or.inl hbase))).2
    linarith
  have hAB : 0 ≤ A / B := div_nonneg (by linarith) (by linarith)
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hc (mul_nonneg hC.le hAB)])

end SRWTightness
