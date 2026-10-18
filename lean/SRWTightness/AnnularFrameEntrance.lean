import SRWTightness.AnnularAxisEntrance
import SRWTightness.ExponentialComparisonChain

open MeasureTheory
namespace SRWTightness

/-- Five axis segments connect annular points through a square frame, uniformly in the scale. -/
theorem annular_frame_entrance (hinput : PositiveHarmonicRelativeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m a R : ℝ), 128 ≤ m → 32 * C ≤ m →
      0 ≤ a → a ≤ m / 2 → 2 * m ≤ R → ∀ M : ℤ,
      m ≤ (M : ℝ) → (M : ℝ) ≤ 5 * m / 4 →
      ∀ (b : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
      ∀ (w : Site), w ∈ K → ∀ z y : Site,
      |z.1| ≤ M → |z.2| ≤ M → |y.1| ≤ M → |y.2| ≤ M →
      (3 * m / 4) ^ 2 ≤ normSq z → (3 * m / 4) ^ 2 ≤ normSq y →
      Real.exp (-(400 * C)) *
          (competingEntranceLaw (translateFinset b (diskFinset R)) K (b + z)).real {w} ≤
        (competingEntranceLaw (translateFinset b (diskFinset R)) K (b + y)).real {w} ∧
      (competingEntranceLaw (translateFinset b (diskFinset R)) K (b + y)).real {w} ≤
        Real.exp (400 * C) *
          (competingEntranceLaw (translateFinset b (diskFinset R)) K (b + z)).real {w} := by
  obtain ⟨C, hC, hh⟩ := annular_axis_entrance hinput
  refine ⟨C, hC, ?_⟩
  intro m a R hm hCm ha ham hmR M hmM hMm b K hK w hw z y hz1 hz2 hy1 hy2 hz hy
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hMInt : (0 : ℤ) ≤ M := by exact_mod_cast hM0
  let u : ℤ := if 0 ≤ z.1 then M else -M
  let v : ℤ := if 0 ≤ y.1 then M else -M
  have hu : |u| = M := by
    dsimp [u]
    split_ifs <;> simp [abs_of_nonneg hMInt]
  have hv : |v| = M := by
    dsimp [v]
    split_ifs <;> simp [abs_of_nonneg hMInt]
  have hdirz : (0 ≤ z.1 ∧ z.1 ≤ u) ∨ (u ≤ z.1 ∧ z.1 ≤ 0) := by
    by_cases h : 0 ≤ z.1
    · exact Or.inl ⟨h, by simpa only [u, if_pos h] using (abs_le.mp hz1).2⟩
    · exact Or.inr ⟨by simpa only [u, if_neg h] using (abs_le.mp hz1).1, by omega⟩
  have hdiry : (0 ≤ y.1 ∧ y.1 ≤ v) ∨ (v ≤ y.1 ∧ y.1 ≤ 0) := by
    by_cases h : 0 ≤ y.1
    · exact Or.inl ⟨h, by simpa only [v, if_pos h] using (abs_le.mp hy1).2⟩
    · exact Or.inr ⟨by simpa only [v, if_neg h] using (abs_le.mp hy1).1, by omega⟩
  have hz1r : |(z.1 : ℝ)| ≤ (M : ℝ) := by exact_mod_cast hz1
  have hz2r : |(z.2 : ℝ)| ≤ (M : ℝ) := by exact_mod_cast hz2
  have hy1r : |(y.1 : ℝ)| ≤ (M : ℝ) := by exact_mod_cast hy1
  have hy2r : |(y.2 : ℝ)| ≤ (M : ℝ) := by exact_mod_cast hy2
  have hur : |(u : ℝ)| = (M : ℝ) := by exact_mod_cast hu
  have hvr : |(v : ℝ)| = (M : ℝ) := by exact_mod_cast hv
  have hMr : |(M : ℝ)| ≤ (M : ℝ) := (abs_of_nonneg hM0).le
  have hradM : (3 * m / 4) ^ 2 ≤ (M : ℝ) ^ 2 :=
    (sq_le_sq₀ (by linarith) hM0).mpr (by linarith)
  have hradu : (3 * m / 4) ^ 2 ≤ (u : ℝ) ^ 2 := by
    rw [← sq_abs (u : ℝ), hur]
    exact hradM
  have hradv : (3 * m / 4) ^ 2 ≤ (v : ℝ) ^ 2 := by
    rw [← sq_abs (v : ℝ), hvr]
    exact hradM
  have haxis := hh m a R (M : ℝ) hm hCm ha ham hmR hMm b K hK w hw
  have h1 := haxis false z.1 u z.2 hz1r hur.le hz2r (Or.inr ⟨hdirz, hz⟩)
  have h2 := haxis true z.2 M u hz2r hMr hur.le (Or.inl hradu)
  have h3 := haxis false u v M hur.le hvr.le hMr (Or.inl hradM)
  have h4 := haxis true M y.2 v hMr hy2r hvr.le (Or.inl hradv)
  have h5 := haxis false y.1 v y.2 hy1r hvr.le hy2r (Or.inr ⟨hdiry, hy⟩)
  have h5' := exponential_comparison_symm _ _ _ h5
  have h12 := exponential_comparison_trans _ _ _ _ _ h1 h2
  have h123 := exponential_comparison_trans _ _ _ _ _ h12 h3
  have h1234 := exponential_comparison_trans _ _ _ _ _ h123 h4
  have hfinal := exponential_comparison_trans _ _ _ _ _ h1234 h5'
  have he : (((80 * C + 80 * C) + 80 * C) + 80 * C) + 80 * C = 400 * C := by ring
  rw [he] at hfinal
  exact hfinal

end SRWTightness
