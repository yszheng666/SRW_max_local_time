import SRWTightness.SignedHarmonicExtension

namespace SRWTightness

/-- Two signed Harnack applications give a quadratic mixed difference for a bounded kernel. -/
theorem biharmonic_mixed_difference_bound (hH : PositiveHarmonicRelativeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : Site) (A B : ℝ), 1 ≤ A → 8 * A ≤ B →
      let D := translateFinset b (diskFinset B)
      ∀ (F : Site → Site → ℝ) (c M : ℝ), 0 ≤ M →
      (∀ t, t ∈ D ∨ t ∈ domainExitBoundary D → ∀ s ∈ D,
        F s t = (1 / 4 : ℝ) * ∑ d : Direction, F (s + step d) t) →
      (∀ s ∈ D, ∀ t ∈ D,
        F s t = (1 / 4 : ℝ) * ∑ d : Direction, F s (t + step d)) →
      (∀ s, s ∈ D ∨ s ∈ domainExitBoundary D →
        ∀ t, t ∈ D ∨ t ∈ domainExitBoundary D → |F s t - c| ≤ M) →
      b ∈ D → ∀ x ∈ translateFinset b (diskFinset (2 * A)), x ∈ D →
        |F x x - F b x - F x b + F b b| ≤ C * M * (A / B) ^ 2 := by
  obtain ⟨C, hC, hlocal⟩ := signed_harmonic_local_difference hH
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro b A B hA hB D F c M hM h1 h2 hbound hb x hx hxD
  have hAB : 0 ≤ A / B := div_nonneg (by linarith) (by linarith)
  have hg (t : Site) (ht : t ∈ D ∨ t ∈ domainExitBoundary D) :
      |F x t - F b t| ≤ C * M * (A / B) :=
    hlocal b A B hA hB (fun s ↦ F s t) c M hM (h1 t ht)
      (fun s hs ↦ hbound s hs t ht) hb x hx hxD
  have hgh : ∀ t ∈ D, F x t - F b t =
      (1 / 4 : ℝ) * ∑ d : Direction, (F x (t + step d) - F b (t + step d)) := by
    intro t ht
    rw [Finset.sum_sub_distrib, mul_sub, ← h2 x hxD t ht, ← h2 b hb t ht]
  have hh := hlocal b A B hA hB (fun t ↦ F x t - F b t) 0
    (C * M * (A / B)) (by positivity) hgh
    (fun t ht ↦ by simpa only [sub_zero] using hg t ht) hb x hx hxD
  convert hh using 1
  · congr 1
    ring
  · ring

end SRWTightness
