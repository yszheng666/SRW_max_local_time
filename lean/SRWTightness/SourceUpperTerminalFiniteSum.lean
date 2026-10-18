import SRWTightness.UpperTerminalDescendingSum
import SRWTightness.SourceUpperTerminalTiltCosts
import SRWTightness.SourceUpperTerminalPrefactor

open Filter

namespace SRWTightness

/-- Actual source scales uniformly bound every finite descending terminal-window sum. -/
theorem source_upper_terminal_finite_sum (hScale : ExponentialFloorScaleInput)
    (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ v : ℝ, ∀ I : Finset ℕ,
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let β := sourceUpperTarget t s /
        (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) - 2
      let Q := 7 + s + d ^ (1 / 4 : ℝ)
      let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
      (∀ J ∈ I, -Q ≤ v - (J : ℝ)) →
      (∑ J ∈ I, (S + (v - (J : ℝ))) *
        (1 + max (v - (J : ℝ)) 0 / Real.sqrt d) / d *
        Real.exp (β * (v - (J : ℝ)) - c * (max (v - (J : ℝ) - 1) 0) ^ 2 / d)) ≤ C := by
  obtain ⟨C, hC, hsum⟩ := upper_terminal_descending_sum c hc
  let K := Real.exp (c + 2 / c) * C + Real.exp 9
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨122 * K, by positivity, ?_⟩
  filter_upwards [source_upper_terminal_sqrt_scale hScale,
    source_upper_terminal_tilt_costs hScale c hc,
    source_upper_terminal_prefactor hScale] with t ht he hp
  intro b hb s hs hslog v I
  dsimp only
  intro hq
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let β := sourceUpperTarget t s /
    (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) - 2
  let Q := 7 + s + d ^ (1 / 4 : ℝ)
  let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
  have hsqrt : 1 ≤ Real.sqrt d := ht.1
  have hd0 : 0 < d := Real.sqrt_pos.mp (by linarith)
  have hd1 : 1 ≤ d := by nlinarith [Real.sq_sqrt hd0.le]
  have hr0 : 0 ≤ d ^ (1 / 4 : ℝ) := Real.rpow_nonneg hd0.le _
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hQS : Q ≤ S := by dsimp [Q, S]; linarith
  have hh := hsum d S β v Q hd1 hQ hQS I hq
  have hcost := he b hb s hs hslog
  have hpoly : 1 + S / Real.sqrt d + (Q + 1) * S / d ≤ 122 := hp s hs hslog
  have ha : 0 ≤ 1 + S / Real.sqrt d := by positivity
  have hb' : 0 ≤ (Q + 1) * S / d := by positivity
  have hpos : Real.exp (c / d + 2 * d * β ^ 2 / c) * C * (1 + S / Real.sqrt d) ≤
      K * (1 + S / Real.sqrt d) := by
    apply mul_le_mul_of_nonneg_right _ ha
    have hm := mul_le_mul_of_nonneg_right hcost.1 hC.le
    dsimp [K]
    linarith [Real.exp_pos (9 : ℝ)]
  have hneg : (Q + 1) * (S / d * Real.exp (|β| * Q)) ≤ K * ((Q + 1) * S / d) := by
    have hm := mul_le_mul_of_nonneg_right hcost.2 hb'
    have hk : Real.exp 9 ≤ K := by
      dsimp [K]
      have hm0 : 0 ≤ Real.exp (c + 2 / c) * C := by positivity
      linarith
    have hn := mul_le_mul_of_nonneg_right hk hb'
    calc
      _ = Real.exp (|β| * Q) * ((Q + 1) * S / d) := by ring
      _ ≤ _ := hm.trans hn
  exact hh.trans ((add_le_add hpos hneg).trans (by
    calc
      _ = K * (1 + S / Real.sqrt d + (Q + 1) * S / d) := by ring
      _ ≤ K * 122 := mul_le_mul_of_nonneg_left hpoly hK.le
      _ = _ := by ring))

end SRWTightness
