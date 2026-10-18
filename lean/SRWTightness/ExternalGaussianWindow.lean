import SRWTightness.SourceGaussianFinalIncrement

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Standard compact-parameter positivity of Gaussian unit intervals, supplied as a theorem input. -/
def GaussianUnitWindowInput : Prop :=
  ∀ L U vmin vmax : ℝ, L ≤ U → 0 < vmin → vmin ≤ vmax →
    ∃ c : ℝ, 0 < c ∧ ∀ z v : ℝ,
      z ∈ Set.Icc L U → v ∈ Set.Icc vmin vmax →
      c ≤ (gaussianReal 0 v.toNNReal).real (Set.Icc z (z + 1))

/-- The source endpoint and threshold windows meet the standard compact Gaussian window input. -/
theorem source_final_window_probability (hWindow : GaussianUnitWindowInput)
    (a ε K D : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hD : 1 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ At V d q z Δ : ℝ,
      |At - (2 * d + q)| ≤ ε → |V - d| ≤ K →
      z ∈ Set.Icc (q - a - 1) (q - a) → Δ ∈ Set.Icc 1 D →
      c ≤ (gaussianReal 0 Δ.toNNReal).real
        (Set.Icc (At - 2 * V - z) (At - 2 * V - z + 1)) ∧
      (gaussianReal 0 Δ.toNNReal).real
        (Set.Icc (At - 2 * V - z) (At - 2 * V - z + 1)) ≤ 1 := by
  obtain ⟨c, hc, hprob⟩ := hWindow (a - ε - 2 * K) (a + 1 + ε + 2 * K) 1 D
    (by linarith) (by norm_num) hD
  refine ⟨c, hc, ?_⟩
  intro At V d q z Δ hAt hV hz hΔ
  refine ⟨hprob _ _ (source_site_increment_window_location At V d q a z ε K hAt hV hz) hΔ,
    ?_⟩
  exact measureReal_le_one

end SRWTightness
