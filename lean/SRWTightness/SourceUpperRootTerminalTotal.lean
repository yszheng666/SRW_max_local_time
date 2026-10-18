import SRWTightness.SourceUpperRootTerminalFamily
import SRWTightness.UpperRootLayerSeries

open Filter

namespace SRWTightness

/-- All actual block contributions have the source upper-tail prefactor after root and window sums. -/
theorem source_upper_root_terminal_total (hScale : ExponentialFloorScaleInput)
    (K κ : ℝ) (hK : 1 ≤ K) (hκ : 0 < κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ B C : ℝ, 0 ≤ B → 0 ≤ C → ∀ M : ℕ, ∀ I : Finset ℕ,
      (∀ i ∈ I, -(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ≤
        sourceUpperTarget t s - (t - 1 + (i : ℝ)) ∧
        t - 1 + (i : ℝ) ≤ sourceUpperBranchingEnd t s) →
      (∑ b ∈ sourceUpperBlockCenters t,
        sourceUpperRootTerminalContribution t s K κ B C b M I) ≤
        D * B * C * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) := by
  classical
  obtain ⟨Df, hDf, hf⟩ := source_upper_root_terminal_family hScale K κ hK hκ
  obtain ⟨Dr, hDr, hr⟩ := upper_root_layer_series
  refine ⟨Df * Dr, by positivity, ?_⟩
  filter_upwards [hf] with t ht
  intro s hs hslog B C hB hC M I hI
  let P := fun b : Site ↦ sourceUpperRootTerminalContribution t s K κ B C b M I
  let F := (sourceUpperBlockCenters t).image (sourceUpperBlockRoot t)
  let f := fun k : ℕ ↦ (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
    Real.exp (-(9 / 8 : ℝ) * k)
  let E := Df * B * C * Real.exp (-(2 * Real.sqrt Real.pi * s))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  obtain ⟨hfs, hfb⟩ := hr s hs
  have hf0 (k : ℕ) : 0 ≤ f k := by dsimp [f]; positivity
  have hsum : (∑ k ∈ F, f k) ≤ Dr * (1 + s) :=
    (hfs.sum_le_tsum F (fun k _ ↦ hf0 k)).trans hfb
  have hid : (∑ k ∈ F, ∑ b ∈ sourceUpperBlockRootFamily t k, P b) =
      ∑ b ∈ sourceUpperBlockCenters t, P b := by
    simpa only [sourceUpperBlockRootFamily] using
      (Finset.sum_fiberwise_of_maps_to (s := sourceUpperBlockCenters t) (t := F)
        (g := sourceUpperBlockRoot t)
        (fun b hb ↦ Finset.mem_image_of_mem (sourceUpperBlockRoot t) hb) P)
  have hpoint (k : ℕ) : (∑ b ∈ sourceUpperBlockRootFamily t k, P b) ≤ E * f k := by
    have hh := ht s hs hslog B C hB hC M k I hI
    apply hh.trans_eq
    dsimp [E, f]
    rw [show -(9 * (k : ℝ) / 8) = -(9 / 8 : ℝ) * k by ring]
    ring
  calc
    _ = ∑ k ∈ F, ∑ b ∈ sourceUpperBlockRootFamily t k, P b := hid.symm
    _ ≤ ∑ k ∈ F, E * f k := Finset.sum_le_sum (fun k _ ↦ hpoint k)
    _ = E * ∑ k ∈ F, f k := by rw [Finset.mul_sum]
    _ ≤ E * (Dr * (1 + s)) := mul_le_mul_of_nonneg_left hsum hE
    _ = _ := by dsimp [E]; ring

end SRWTightness
