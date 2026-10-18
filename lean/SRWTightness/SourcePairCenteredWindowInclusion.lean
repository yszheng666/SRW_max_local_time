import SRWTightness.SourcePairMeanPrefixNonnegative
import SRWTightness.SourcePairMeanTranslation
import SRWTightness.PairWindowMeanShift
import SRWTightness.SourcePairWindowEvent

open MeasureTheory ProbabilityTheory Filter Matrix

namespace SRWTightness

/-- The actual shifted pair window implies a centered flat prefix and the corrected endpoint window. -/
theorem source_pair_centered_window_inclusion (b : Site) (t A : ℝ)
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
    ∀ᵐ ω ∂independentBridgeLaw ℕ, ∀ x : PairObservationIndex (I - i + 1) → ℝ,
      (mean + x, ω) ∈ sourcePairWindowEvent t A I i At q f n p l →
      (mean + x ∈ pairWindow (Fin.last (I - i)) At
        (2 * sourceObservationTime t A I (I - i + 1) + q - f) n p l) ∧
      (∀ v : ℝ, 0 ≤ v → v ≤ sourceObservationTime t A I (I - i + 1) →
        pairCenteredBridgedPath t A I i x ω v ≤ q) ∧
      x (.inl (Fin.last (I - i))) ∈
        Set.Icc (q - f - l - 1 - 2 * e) (q - f - l - 2 * e) := by
  have hm := source_pair_comparison_mean_prefix_nonneg b t A hA ht I hI i hi
    z y hz hρ hlo u hu k hk
  have hmean := source_pair_average_comparison_mean b t A hA ht I hI i hi
    z y hz hρ hlo u hu k hk
  dsimp only at hm hmean ⊢
  filter_upwards [sourcePairWindowEvent_ae_iff t A I i At q f n p l] with ω hω
  intro x hx
  have hp := (hω _).mp hx
  refine ⟨hp.1, ?_, ?_⟩
  · intro v hv hvtop
    exact pairCenteredBridgedPath_barrier_of_shift t A I i _ x ω v q
      (hm v hv hvtop) (hp.2 v hv hvtop)
  · apply pairWindow_centered_last _ _ x At
      (sourceObservationTime t A I (I - i + 1)) q f _ n p l _ hp.1
    simpa only [Fin.val_last, if_pos rfl, if_true] using hmean (Fin.last (I - i))

end SRWTightness
