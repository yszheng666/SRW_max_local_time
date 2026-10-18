import SRWTightness.UpperTerminalTiltedPositiveSum
import Mathlib.Algebra.Order.Floor.Ring

namespace SRWTightness

/-- A finite descending positive window grid inherits the uniform tilted Gaussian sum bound. -/
theorem upper_terminal_descending_positive_sum (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ d S β v : ℝ, 1 ≤ d → 0 ≤ S → ∀ I : Finset ℕ,
      (∀ J ∈ I, 0 ≤ v - (J : ℝ)) →
      (∑ J ∈ I, (S + (v - (J : ℝ))) * (1 + (v - (J : ℝ)) / Real.sqrt d) / d *
        Real.exp (β * (v - (J : ℝ)) - c * (max (v - (J : ℝ) - 1) 0) ^ 2 / d)) ≤
      Real.exp (c / d + 2 * d * β ^ 2 / c) * C * (1 + S / Real.sqrt d) := by
  obtain ⟨C, hC, hsum⟩ := upper_terminal_tilted_positive_sum c hc
  refine ⟨C, hC, ?_⟩
  intro d S β v hd hS I hq
  by_cases hv : 0 ≤ v
  · let n := ⌊v⌋₊
    let w := v - (n : ℝ)
    let f := fun q : ℝ ↦ (S + q) * (1 + q / Real.sqrt d) / d *
      Real.exp (β * q - c * (max (q - 1) 0) ^ 2 / d)
    have hw : 0 ≤ w := sub_nonneg.mpr (Nat.floor_le hv)
    have hw1 : w ≤ 1 := by
      have hh := Nat.lt_floor_add_one v
      dsimp [w, n]
      linarith
    have hJn (J : ℕ) (hJ : J ∈ I) : J ≤ n := by
      apply Nat.le_floor
      linarith [hq J hJ]
    have hinj : Set.InjOn (fun J : ℕ ↦ n - J) (I : Set ℕ) := by
      intro J hJ L hL he
      change n - J = n - L at he
      have hj := hJn J hJ
      have hl := hJn L hL
      omega
    have he : (∑ J ∈ I, f (v - (J : ℝ))) =
        ∑ k ∈ I.image (fun J ↦ n - J), f ((k : ℝ) + w) := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro J hJ
      congr 1
      rw [Nat.cast_sub (hJn J hJ)]
      dsimp [w]
      ring
    have hsub : I.image (fun J ↦ n - J) ⊆ Finset.range (n + 1) := by
      intro k hk
      obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
    calc
      _ = ∑ k ∈ I.image (fun J ↦ n - J), f ((k : ℝ) + w) := he
      _ ≤ ∑ k ∈ Finset.range (n + 1), f ((k : ℝ) + w) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ ↦ by dsimp [f]; positivity)
      _ ≤ _ := hsum d S β w hd hS hw hw1 (n + 1)
  · have he : I = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro J hJ
      have hh := hq J hJ
      have hj : (0 : ℝ) ≤ J := Nat.cast_nonneg J
      linarith
    rw [he]
    simp only [Finset.sum_empty]
    positivity

end SRWTightness
