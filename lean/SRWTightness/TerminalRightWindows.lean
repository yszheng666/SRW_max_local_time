import SRWTightness.TerminalWindowSum

namespace SRWTightness

/-- A half-open height window corresponds to a right-closed deficit window. -/
theorem terminal_deficit_window_orientation (x q v : ℝ)
    (hv : v ∈ Set.Ico (x - q) (x - q + 1)) : x - v ∈ Set.Ioc (q - 1) q := by
  exact ⟨by linarith [hv.2], by linarith [hv.1]⟩

/-- Complete right-closed deficit windows and their right endpoints stay in the source band. -/
theorem terminal_right_inner_window (d : ℝ) (i : ℕ) (hi : i < ⌊Real.sqrt d⌋₊) :
    terminalWindowLeft d i + 1 ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) ∧
      Set.Ioc (terminalWindowLeft d i) (terminalWindowLeft d i + 1) ⊆
        Set.Icc (Real.sqrt d) (2 * Real.sqrt d) := by
  have hf := Nat.floor_le (Real.sqrt_nonneg d)
  have hic : (i : ℝ) + 1 ≤ (⌊Real.sqrt d⌋₊ : ℝ) := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := by positivity
  unfold terminalWindowLeft
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  intro q hq
  exact ⟨by linarith [hq.1], by linarith [hq.2]⟩

/-- Band endpoints are covered using only GW window parameters inside the allowed band. -/
theorem terminal_right_outer_cover (d q : ℝ)
    (hq : q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d)) :
    (∃ i ≤ ⌊Real.sqrt d⌋₊,
      terminalWindowLeft d i ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) ∧
      q ∈ Set.Ioc (terminalWindowLeft d i - 1) (terminalWindowLeft d i)) ∨
    (2 * Real.sqrt d ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) ∧
      q ∈ Set.Ioc (2 * Real.sqrt d - 1) (2 * Real.sqrt d)) := by
  have ha0 := Real.sqrt_nonneg d
  have hf := Nat.floor_le ha0
  have hf' := Nat.lt_floor_add_one (Real.sqrt d)
  by_cases hqf : q ≤ Real.sqrt d + (⌊Real.sqrt d⌋₊ : ℝ)
  · let i : ℕ := ⌈q - Real.sqrt d⌉₊
    have hi : i ≤ ⌊Real.sqrt d⌋₊ := Nat.ceil_le.mpr (by linarith)
    have hic : (i : ℝ) ≤ (⌊Real.sqrt d⌋₊ : ℝ) := by exact_mod_cast hi
    have hil : q - Real.sqrt d ≤ (i : ℝ) := Nat.le_ceil _
    have hiu : (i : ℝ) < q - Real.sqrt d + 1 :=
      Nat.ceil_lt_add_one (by linarith [hq.1])
    left
    refine ⟨i, hi, ?_, ?_⟩
    · unfold terminalWindowLeft
      exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) i], by linarith⟩
    · unfold terminalWindowLeft
      exact ⟨by linarith, by linarith⟩
  · right
    exact ⟨⟨by linarith, le_rfl⟩, ⟨by linarith, hq.2⟩⟩

/-- Complete right-closed windows have disjoint interiors and do not double-count endpoints. -/
theorem terminal_right_inner_unique (d q : ℝ) (i j : ℕ)
    (hi : q ∈ Set.Ioc (terminalWindowLeft d i) (terminalWindowLeft d i + 1))
    (hj : q ∈ Set.Ioc (terminalWindowLeft d j) (terminalWindowLeft d j + 1)) : i = j := by
  unfold terminalWindowLeft at hi hj
  have hij : (i : ℝ) < (j : ℝ) + 1 := by linarith [hi.1, hj.2]
  have hji : (j : ℝ) < (i : ℝ) + 1 := by linarith [hj.1, hi.2]
  have hij' : i < j + 1 := by exact_mod_cast hij
  have hji' : j < i + 1 := by exact_mod_cast hji
  omega

end SRWTightness
