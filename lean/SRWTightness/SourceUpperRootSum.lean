import SRWTightness.SourceUpperRootEndpointRatio
import SRWTightness.UpperGeometricRootSpecialization

open Filter

namespace SRWTightness

/-- Source (4.28) at the actual block root and every admissible endpoint window. -/
theorem source_upper_root_sum (hScale : ExponentialFloorScaleInput) (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ u : ℝ,
      t - 1 ≤ u → u ≤ sourceUpperBranchingEnd t s →
      let k := sourceUpperBlockRoot t b
      let L := sourceUpperCoarseDepth t - k
      Summable (upperGeometricRootTerm (k + K) (u / L)) ∧
        (∑' J : ℕ, upperGeometricRootTerm (k + K) (u / L) J) ≤
          C * ((k : ℝ) + 1) ^ 2 * Real.exp (2 * k) := by
  obtain ⟨C, hC, hsum⟩ := upper_geometric_root_specialization
  obtain ⟨B, hB0, hc⟩ := source_upper_threshold_conditions hScale
  refine ⟨C * K ^ 2 * Real.exp (2 * K + 5 / 2), by positivity, ?_⟩
  filter_upwards [hc, source_upper_block_root_conditions, source_upper_branching_depth_bounds,
    (source_upper_root_slope_error_limit hScale B K).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (2 : ℝ)] with t ht hk hd hsmall ht2
  intro b hb s hs hslog u hu hue
  let δ := sourceUpperRootSlopeError t B
  have hd0 : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) := by
    linarith [ht.2.2.2.2.2.2.1]
  have hδ : 0 ≤ δ := by
    dsimp [δ, sourceUpperRootSlopeError]
    have hl : 0 ≤ Real.log t := by linarith [ht.2.1]
    positivity
  have hδ1 : δ ≤ 1 := by
    have hp : 1 ≤ Real.log t + 1 + K := by linarith [ht.2.1]
    have hm := mul_le_mul_of_nonneg_left hp hδ
    dsimp [δ] at hm ⊢
    nlinarith
  have hε : 2 * ((1 + Real.sqrt Real.pi) * Real.log t + 2 * B) / t ≤ δ := by
    dsimp [δ, sourceUpperRootSlopeError]
    apply div_le_div_of_nonneg_right _ ht.1.le
    nlinarith [ht.2.1]
  have hθ : sourceUpperSlope t s ≤ 3 := by
    have hh := (abs_le.mp (source_upper_slope_error t s B ht.1 hs hslog
      ht.2.2.2.1 ht.2.2.2.2.1)).2
    linarith
  have hL : t / 2 ≤ (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) := by
    linarith [(hd b hb).2.1]
  have hL0 : (0 : ℝ) < (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) := by
    linarith
  have ha : 1 / 2 ≤ u / (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) := by
    apply (le_div_iff₀ hL0).mpr
    linarith [(hd b hb).2.2]
  have hau : u / (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) ≤ 2 + δ := by
    exact (div_le_div_of_nonneg_right hue hL0.le).trans
      (source_upper_root_endpoint_ratio t s B b ht.1 ht.2.1 hB0 hs hslog
        ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2.2.1
        (hd b hb).1 (hk b hb).2.1 hL hθ)
  have hδq : δ * ((sourceUpperBlockRoot t b : ℝ) + K) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left
      (add_le_add_right (hk b hb).2.1 K) hδ
    dsimp [δ] at hm ⊢
    linarith
  exact hsum K hK (sourceUpperBlockRoot t b)
    (u / (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ)) δ
    ha (by linarith) hδ hau hδq

end SRWTightness
