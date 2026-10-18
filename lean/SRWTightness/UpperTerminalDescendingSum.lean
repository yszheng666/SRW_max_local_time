import SRWTightness.UpperTerminalDescendingPositiveSum
import SRWTightness.UpperTerminalNegativeWindowCount

namespace SRWTightness

/-- Positive and negative descending terminal windows satisfy one finite sum bound. -/
theorem upper_terminal_descending_sum (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ d S β v Q : ℝ, 1 ≤ d → 0 ≤ Q → Q ≤ S → ∀ I : Finset ℕ,
      (∀ J ∈ I, -Q ≤ v - (J : ℝ)) →
      (∑ J ∈ I, (S + (v - (J : ℝ))) *
        (1 + max (v - (J : ℝ)) 0 / Real.sqrt d) / d *
        Real.exp (β * (v - (J : ℝ)) - c * (max (v - (J : ℝ) - 1) 0) ^ 2 / d)) ≤
      Real.exp (c / d + 2 * d * β ^ 2 / c) * C * (1 + S / Real.sqrt d) +
        (Q + 1) * (S / d * Real.exp (|β| * Q)) := by
  classical
  obtain ⟨C, hC, hp⟩ := upper_terminal_descending_positive_sum c hc
  refine ⟨C, hC, ?_⟩
  intro d S β v Q hd hQ hQS I hq
  let f := fun J : ℕ ↦ (S + (v - (J : ℝ))) *
    (1 + max (v - (J : ℝ)) 0 / Real.sqrt d) / d *
    Real.exp (β * (v - (J : ℝ)) - c * (max (v - (J : ℝ) - 1) 0) ^ 2 / d)
  have hpos := hp d S β v hd (hQ.trans hQS) (I.filter (fun J : ℕ ↦ 0 ≤ v - (J : ℝ)))
    (fun J hJ ↦ (Finset.mem_filter.mp hJ).2)
  have hpos' : (∑ J ∈ I.filter (fun J : ℕ ↦ 0 ≤ v - (J : ℝ)), f J) ≤
      Real.exp (c / d + 2 * d * β ^ 2 / c) * C * (1 + S / Real.sqrt d) := by
    convert hpos using 1
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp [f]
    rw [max_eq_left (Finset.mem_filter.mp hJ).2]
  have hneg : (∑ J ∈ I.filter (fun J : ℕ ↦ ¬0 ≤ v - (J : ℝ)), f J) ≤
      (Q + 1) * (S / d * Real.exp (|β| * Q)) := by
    apply upper_terminal_negative_shifted_sum _ v d S β Q c (by linarith) hQ hQS
    intro J hJ
    obtain ⟨hJ, hj⟩ := Finset.mem_filter.mp hJ
    exact ⟨hq J hJ, (lt_of_not_ge hj).le⟩
  calc
    _ = (∑ J ∈ I.filter (fun J : ℕ ↦ 0 ≤ v - (J : ℝ)), f J) +
        ∑ J ∈ I.filter (fun J : ℕ ↦ ¬0 ≤ v - (J : ℝ)), f J :=
      (Finset.sum_filter_add_sum_filter_not I (fun J : ℕ ↦ 0 ≤ v - (J : ℝ)) f).symm
    _ ≤ _ := add_le_add hpos' hneg

end SRWTightness
