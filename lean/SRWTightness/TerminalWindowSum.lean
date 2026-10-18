import SRWTightness.SourceCoarseExponentExpansion

open scoped BigOperators

namespace SRWTightness

/-- Left endpoints of unit windows starting at the lower edge of the deficit band. -/
noncomputable def terminalWindowLeft (d : ℝ) (i : ℕ) : ℝ := Real.sqrt d + i

/-- Complete unit windows contained in the deficit band. -/
noncomputable def terminalInnerWindowWeight (d : ℝ) : ℝ :=
  ∑ i ∈ Finset.range ⌊Real.sqrt d⌋₊, (1 + terminalWindowLeft d i)

/-- A covering family, including a possible final partial window. -/
noncomputable def terminalOuterWindowWeight (d : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (⌊Real.sqrt d⌋₊ + 1), (1 + terminalWindowLeft d i)

/-- Every inner unit window lies inside the closed source deficit band. -/
theorem terminal_inner_window_subset (d : ℝ) (hd : 0 ≤ d) (i : ℕ)
    (hi : i < ⌊Real.sqrt d⌋₊) (q : ℝ)
    (hq : terminalWindowLeft d i ≤ q) (hq' : q < terminalWindowLeft d i + 1) :
    Real.sqrt d ≤ q ∧ q ≤ 2 * Real.sqrt d := by
  have hf := Nat.floor_le (Real.sqrt_nonneg d)
  have hi' : (i : ℝ) + 1 ≤ (⌊Real.sqrt d⌋₊ : ℝ) := by exact_mod_cast hi
  unfold terminalWindowLeft at *
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i]

/-- Every deficit, including the upper endpoint, belongs to an outer unit window. -/
theorem terminal_outer_window_covers (d q : ℝ)
    (hql : Real.sqrt d ≤ q) (hqu : q ≤ 2 * Real.sqrt d) :
    ∃ i < ⌊Real.sqrt d⌋₊ + 1,
      terminalWindowLeft d i ≤ q ∧ q < terminalWindowLeft d i + 1 := by
  refine ⟨⌊q - Real.sqrt d⌋₊, ?_, ?_, ?_⟩
  · have hh : ⌊q - Real.sqrt d⌋₊ ≤ ⌊Real.sqrt d⌋₊ :=
      Nat.floor_mono (by linarith)
    omega
  · have hh := Nat.floor_le (show 0 ≤ q - Real.sqrt d by linarith)
    unfold terminalWindowLeft
    linarith
  · have hh := Nat.lt_floor_add_one (q - Real.sqrt d)
    unfold terminalWindowLeft
    linarith

/-- The complete-window sum is at least a fixed multiple of the band time. -/
theorem terminal_inner_window_weight_lower (d : ℝ) (hd : 4 ≤ d) :
    d / 2 ≤ terminalInnerWindowWeight d := by
  have hd0 : 0 ≤ d := by linarith
  have hs0 := Real.sqrt_nonneg d
  have hs := Real.sq_sqrt hd0
  have hs2 : 2 ≤ Real.sqrt d := by nlinarith
  have hf := Nat.lt_floor_add_one (Real.sqrt d)
  have hn : Real.sqrt d / 2 ≤ (⌊Real.sqrt d⌋₊ : ℝ) := by linarith
  have hsum : (⌊Real.sqrt d⌋₊ : ℝ) * Real.sqrt d ≤ terminalInnerWindowWeight d := by
    have hh := Finset.sum_le_sum (s := Finset.range ⌊Real.sqrt d⌋₊)
      (f := fun _ : ℕ ↦ Real.sqrt d) (g := fun i ↦ 1 + terminalWindowLeft d i)
      (fun i _ ↦ show Real.sqrt d ≤ 1 + terminalWindowLeft d i by
        unfold terminalWindowLeft; linarith [Nat.cast_nonneg (α := ℝ) i])
    simpa [terminalInnerWindowWeight] using hh
  nlinarith

/-- Even the covering-window sum is at most a fixed multiple of the band time. -/
theorem terminal_outer_window_weight_upper (d : ℝ) (hd : 4 ≤ d) :
    terminalOuterWindowWeight d ≤ 6 * d := by
  have hd0 : 0 ≤ d := by linarith
  have hs0 := Real.sqrt_nonneg d
  have hs := Real.sq_sqrt hd0
  have hs2 : 2 ≤ Real.sqrt d := by nlinarith
  have hf := Nat.floor_le (Real.sqrt_nonneg d)
  have hn : ((⌊Real.sqrt d⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt d := by
    push_cast
    linarith
  have hsum : terminalOuterWindowWeight d ≤
      ((⌊Real.sqrt d⌋₊ + 1 : ℕ) : ℝ) * (3 * Real.sqrt d) := by
    have hh := Finset.sum_le_sum (s := Finset.range (⌊Real.sqrt d⌋₊ + 1))
      (f := fun i ↦ 1 + terminalWindowLeft d i) (g := fun _ : ℕ ↦ 3 * Real.sqrt d)
      (fun i hi ↦ show 1 + terminalWindowLeft d i ≤ 3 * Real.sqrt d by
        have hi' : i ≤ ⌊Real.sqrt d⌋₊ := by simpa using Finset.mem_range.mp hi
        have hic : (i : ℝ) ≤ (⌊Real.sqrt d⌋₊ : ℝ) := by exact_mod_cast hi'
        unfold terminalWindowLeft
        linarith)
    simpa [terminalOuterWindowWeight] using hh
  nlinarith


/-- The half-open windows do not count any deficit twice. -/
theorem terminal_window_unique (d q : ℝ) (i j : ℕ)
    (hi : terminalWindowLeft d i ≤ q ∧ q < terminalWindowLeft d i + 1)
    (hj : terminalWindowLeft d j ≤ q ∧ q < terminalWindowLeft d j + 1) : i = j := by
  unfold terminalWindowLeft at hi hj
  have hij : (i : ℝ) < (j : ℝ) + 1 := by linarith [hi.1, hj.2]
  have hji : (j : ℝ) < (i : ℝ) + 1 := by linarith [hj.1, hi.2]
  have hij' : i < j + 1 := by exact_mod_cast hij
  have hji' : j < i + 1 := by exact_mod_cast hji
  omega

/-- Adding the possible boundary window can only increase the weighted sum. -/
theorem terminal_inner_window_weight_le_outer (d : ℝ) :
    terminalInnerWindowWeight d ≤ terminalOuterWindowWeight d := by
  unfold terminalInnerWindowWeight terminalOuterWindowWeight
  rw [Finset.sum_range_succ]
  have hh : 0 ≤ 1 + terminalWindowLeft d ⌊Real.sqrt d⌋₊ := by
    unfold terminalWindowLeft
    positivity
  linarith

/-- Normalized window sums are bounded above and below by absolute positive constants. -/
theorem terminal_window_weight_normalized (d : ℝ) (hd : 4 ≤ d) :
    (1 / 2 : ℝ) ≤ terminalInnerWindowWeight d / d ∧
      terminalInnerWindowWeight d / d ≤ terminalOuterWindowWeight d / d ∧
      terminalOuterWindowWeight d / d ≤ 6 := by
  have hd0 : 0 < d := by linarith
  refine ⟨(le_div_iff₀ hd0).mpr ?_,
    div_le_div_of_nonneg_right (terminal_inner_window_weight_le_outer d) hd0.le,
    (div_le_iff₀ hd0).mpr (terminal_outer_window_weight_upper d hd)⟩
  have hh := terminal_inner_window_weight_lower d hd
  linarith

end SRWTightness
