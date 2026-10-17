import SRWTightness.SourceUpperRootTerminalSum
import SRWTightness.SourceUpperReducedBaseline

open Filter

namespace SRWTightness

/-- The real finite root-population and terminal-window principal contribution. -/
noncomputable def sourceUpperRootTerminalContribution (t s K κ B C : ℝ) (b : Site)
    (M : ℕ) (I : Finset ℕ) : ℝ :=
  ∑ J ∈ Finset.range M,
    (1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ (J - 1) *
      ∑ i ∈ I, sourceUpperTerminalWindowWeight t s C κ (t - 1 + (i : ℝ)) *
        sourceUpperBranchingWindowFactor t s B (sourceUpperBlockRoot t b) J (t - 1 + (i : ℝ))

/-- The finite principal contribution has the normalized spatial and root exponential factors. -/
theorem source_upper_root_terminal_normalized (hScale : ExponentialFloorScaleInput)
    (K κ : ℝ) (hK : 1 ≤ K) (hκ : 0 < κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ B C : ℝ, 0 ≤ B → 0 ≤ C →
      ∀ M : ℕ, ∀ I : Finset ℕ,
      (∀ i ∈ I, -(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ≤
        sourceUpperTarget t s - (t - 1 + (i : ℝ)) ∧
        t - 1 + (i : ℝ) ≤ sourceUpperBranchingEnd t s) →
      sourceUpperRootTerminalContribution t s K κ B C b M I ≤
        D * B * C * (5 + s + (sourceUpperBlockRoot t b : ℝ)) *
          ((sourceUpperBlockRoot t b : ℝ) + 1) ^ 2 * Real.exp (2 * sourceUpperBlockRoot t b) *
          (upperTerminalFineRadius (sourceUpperLogRadius t)) ^ 2 * Real.exp (-2 * t) *
          Real.exp (-(2 * Real.sqrt Real.pi * s)) *
          Real.exp (-(9 * (sourceUpperBlockRoot t b : ℝ) / 8)) := by
  obtain ⟨Dr, hDr, hr⟩ := source_upper_root_terminal_sum hScale K κ hK hκ
  obtain ⟨Db, hDb, hb⟩ := source_upper_reduced_baseline hScale
  refine ⟨Dr * Db, by positivity, ?_⟩
  filter_upwards [hr, hb] with t ht hn
  intro b hb s hs hslog B C hB hC M I hI
  let k := sourceUpperBlockRoot t b
  let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let x := sourceUpperTarget t s
  let P := Dr * B * C * (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
    Real.exp (2 * k) * r ^ 2 * Real.exp (-2 * t)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have he : Real.exp (-2 * d - x ^ 2 / (2 * L)) =
      Real.exp (-2 * t) * Real.exp (2 * t - 2 * d - x ^ 2 / (2 * L)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbase := hn b hb s hs hslog
  calc
    _ ≤ Dr * B * C * (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 * Real.exp (2 * k) *
        r ^ 2 * Real.exp (-2 * d - x ^ 2 / (2 * L)) / L ^ 2 :=
      ht b hb s hs hslog B C hB hC M I hI
    _ = P * (Real.exp (2 * t - 2 * d - x ^ 2 / (2 * L)) / L ^ 2) := by
      rw [he]
      dsimp [P]
      ring
    _ ≤ P * (Db * Real.exp (-(2 * Real.sqrt Real.pi * s)) *
        Real.exp (-(9 * (k : ℝ) / 8))) := mul_le_mul_of_nonneg_left hbase hP
    _ = _ := by dsimp [P, k, r]; ring

end SRWTightness
