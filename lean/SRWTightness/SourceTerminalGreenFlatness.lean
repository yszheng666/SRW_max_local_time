import SRWTightness.GreenGapScale

namespace SRWTightness

/-- Source terminal Green flatness with uniform constants on an intermediate comparison ball. -/
theorem source_terminal_green_flatness (hinput : PotentialKernelAsymptoticInput) :
    ∃ L T : ℝ, 0 ≤ L ∧ 8 ≤ T ∧ ∀ (m H a : ℝ),
      T ≤ m → 0 ≤ H → H ≤ m / 2 → 0 ≤ a → 2 * a < m - H - 2 →
      ∀ b x y : Site,
        (m - H - 1 ≤ Real.sqrt (normSq (x - b)) ∧
          Real.sqrt (normSq (x - b)) ≤ m - H + 1) →
        Real.sqrt (normSq (y - b)) ≤ 3 * a / 2 + 1 →
        |killedGreen (translateFinset b (diskFinset (Real.exp 1 * m + H))) x y -
          (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))| ≤ L * (a + 1) / m := by
  obtain ⟨κ, C, R₀, hC, hR₀, hbound⟩ := hinput
  let L := 256 * C + 64 * (2 / Real.pi)
  let T := 16 * R₀ + 8
  have hg : 0 ≤ (2 / Real.pi : ℝ) := by positivity
  refine ⟨L, T, by dsimp [L]; positivity, by dsimp [T]; linarith, ?_⟩
  intro m H a hm hH hHm ha hsep b x y hx hy
  have hm0 : 0 < m := by dsimp [T] at hm; linarith
  have hr : 4 ≤ m - H := by dsimp [T] at hm; linarith
  have hr0 : 0 < m - H := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have houter : m - H + 1 < Real.exp 1 * m + H := by nlinarith
  have hR0 : 0 < Real.exp 1 * m + H := by nlinarith
  have hlarge : R₀ ≤ (m - H) / 8 := by dsimp [T] at hm; linarith
  have hh := disk_green_intermediate_flatness κ C R₀ hC hR₀ hbound b x y
    (Real.exp 1 * m + H) (m - H) a ha hr hsep houter hlarge hx hy
  rw [Real.log_div hR0.ne' hr0.ne']
  refine hh.trans ?_
  apply (div_le_div_iff₀ hr0 hm0).mpr
  dsimp [L]
  have hn : 0 ≤ (128 * C + 32 * (2 / Real.pi)) * (a + 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (show m ≤ 2 * (m - H) by linarith) hn]

end SRWTightness
