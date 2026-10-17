import SRWTightness.SourcePairCenteredWindowInclusion
import SRWTightness.PairResidualWindowCoordinates
import SRWTightness.SourcePairFiniteGaussianPath

open MeasureTheory ProbabilityTheory Filter Matrix

namespace SRWTightness

/-- The actual shifted window maps into the independent Brownian-prefix and residual rectangles. -/
theorem source_pair_residual_window_inclusion (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ))
    (At q f : ℝ) (n p l : ℕ) :
    let R := Real.exp 1 * sourceLowerRadius t + 14
    let D := translateFinset b (diskFinset R)
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let μ := markProductLaw D M α k
    let F := fun a ↦ normalizedWeightedSum M k α (2 / Real.pi) u
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y a)
    let mean := fun j ↦ ∑ l, pairObservationTilt (Fin.last (I - i)) l * covariance (F j) (F l) μ
    let e := geometricDiskPointError b A R diskEnergyGapRatio (2 / Real.pi) (I + 1)
      (sourcePairAverageIndex I i (Fin.last (I - i)))
    ∀ᵐ ω ∂independentBridgeLaw ℕ, ∀ (x : Fin (I - i + 1) → ℝ) (r : Fin 2 → ℝ),
      (mean + pairResidualCoordinates (Fin.last (I - i)) (x, r), ω) ∈
        sourcePairWindowEvent t A I i At q f n p l →
      (x, ω) ∈ finiteGaussianPrefixWindow (sourceObservationTime t A I)
        (I - i + 1) (I + 1) (Fin.last (I - i)) q
        (q - f - l - 1 - 2 * e) (q - f - l - 2 * e) ∧
      ∀ j, pairResidualWindowLocation (Fin.last (I - i)) mean At n p (x, ω) j ≤ r j ∧
        r j < pairResidualWindowLocation (Fin.last (I - i)) mean At n p (x, ω) j + 1 := by
  have hh := source_pair_centered_window_inclusion b t A hA ht I hI i hi
    z y hz hρ hlo u hu k hk At q f n p l
  dsimp only at hh ⊢
  filter_upwards [hh] with ω hω
  intro x r hp
  obtain ⟨hw, hb, hend⟩ := hω (pairResidualCoordinates (Fin.last (I - i)) (x, r)) hp
  refine ⟨⟨hend, ?_⟩, pairWindow_residual_unit_windows _ _ At _ n p l x r ω hw⟩
  intro a j hj
  have hh := hb ((j : ℝ) / 2 ^ a) (by positivity) hj
  rw [pairCenteredBridgedPath_finiteGaussian] at hh
  exact hh

end SRWTightness
