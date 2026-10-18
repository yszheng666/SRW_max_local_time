import SRWTightness.SourcePairTiltApproximation
import SRWTightness.SourcePairWindowEvent

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology

namespace SRWTightness

/-- The actual tilted pair law obeys the CLT bound on the combined window and prefix event. -/
theorem source_pair_window_approximation
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) :
    ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (A : ℝ)
      (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : 4 * sourcePairResidualError + 3 + sourceEquilibriumTimeError +
      sourceLowerTimeError ≤ Real.log A)
    (hsmall : (diskEquilibriumWeightConstant / A) / (2 / Real.pi) ≤ 1 / 16)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (hhi : A * diskEnergyGapRatio ^ i ≤
      4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)))
    (u : ℝ) (hu : t ≤ u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) (At q f : ℝ) (n m l : ℕ),
    let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let μ := markProductLaw D M α k
    let F := fun j ↦ normalizedWeightedSum M k α (2 / Real.pi) u
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j)
    let β := pairObservationTilt (Fin.last (I - i))
    let ρ := μ.tilted (fun Y ↦ ∑ j, β j * F j Y)
    let Sigma : Matrix (PairObservationIndex (I - i + 1)) _ ℝ :=
      fun j l ↦ covariance (F j) (F l) μ
    let target := fun j ↦ ∑ l, β l * Sigma j l
    |((ρ.map (fun Y j ↦ F j Y)).prod (independentBridgeLaw ℕ)).real
        (sourcePairWindowEvent t A I i At q f n m l) -
      ((gaussianMeanCoordinateLaw target Sigma).prod (independentBridgeLaw ℕ)).real
        (sourcePairWindowEvent t A I i At q f n m l)| ≤
      sourceTiltApproximationConstant 1 6 (2 * sourceObservationDimensionConstant) (1 / 16) *
        sourceLowerTime (sourceLowerRadius t) ^ 5 / t := by
  filter_upwards [source_pair_tilt_approximation hBE] with t happ
  intro b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi u hu k hk At q f n m l
  have h := happ b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi u hu k hk
  exact h.2.2.2 _ (independentBridgeLaw ℕ) (sourcePairWindowEvent t A I i At q f n m l)
    (sourcePairWindowEvent_measurable t A I i At q f n m l)
    (Eventually.of_forall (sourcePairWindowEvent_convex t A I i At q f n m l))

end SRWTightness
