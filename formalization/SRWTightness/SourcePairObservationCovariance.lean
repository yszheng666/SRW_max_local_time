import SRWTightness.SourcePairAverageEntries
import SRWTightness.SourcePairAverageCovariance

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The average block, exact site-average columns, and two-site covariance block. -/
noncomputable def pairObservationCovarianceMatrix {n : ℕ}
    (T e : Fin n → ℝ) (V : Bool → Bool → ℝ) :
    Matrix (PairObservationIndex n) (PairObservationIndex n) ℝ
  | .inl j, .inl l => min (T j) (T l) - if j = l then e j else 0
  | .inl j, .inr _ => T j
  | .inr _, .inl l => T l
  | .inr c, .inr d => V c d

/-- The full actual two-site observation covariance has the claimed block structure. -/
theorem source_pair_observation_covariance (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let R := Real.exp 1 * sourceLowerRadius t + 14
    let D := translateFinset b (diskFinset R)
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let μ := markProductLaw D M α k
    let F := fun a ↦ normalizedWeightedSum M k α (2 / Real.pi) u
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y a)
    let V := fun c d : Bool ↦ covariance
      (normalizedMarkSum M k α (2 / Real.pi) u (if c then y else z))
      (normalizedMarkSum M k α (2 / Real.pi) u (if d then y else z)) μ
    (fun j l ↦ covariance (F j) (F l) μ) = pairObservationCovarianceMatrix
      (fun j ↦ sourceObservationTime t A I (j.val + 1))
      (fun j ↦ geometricDiskPointError b A R diskEnergyGapRatio (2 / Real.pi) (I + 1)
        (sourcePairAverageIndex I i j)) V := by
  dsimp only
  funext j l
  cases j with
  | inl j =>
    cases l with
    | inl l =>
      simpa only [pairObservationCovarianceMatrix, pairObservationWeight,
        normalizedWeightedSum_observationWeight, normalizedObservation] using
        source_pair_average_entries b t A hA ht I hI i u hu k hk j l
    | inr c =>
      have hh := source_pair_average_covariance b t A hA ht I hI i hi z y hz hρ hlo
        u hu k hk j
      cases c
      · simpa only [pairObservationCovarianceMatrix, pairObservationWeight,
          normalizedWeightedSum_observationWeight, normalizedObservation, covariance_comm] using hh.1
      · simpa only [pairObservationCovarianceMatrix, pairObservationWeight,
          normalizedWeightedSum_observationWeight, normalizedObservation, covariance_comm] using hh.2
  | inr c =>
    cases l with
    | inl l =>
      have hh := source_pair_average_covariance b t A hA ht I hI i hi z y hz hρ hlo
        u hu k hk l
      cases c
      · simpa only [pairObservationCovarianceMatrix, pairObservationWeight,
          normalizedWeightedSum_observationWeight, normalizedObservation] using hh.1
      · simpa only [pairObservationCovarianceMatrix, pairObservationWeight,
          normalizedWeightedSum_observationWeight, normalizedObservation] using hh.2
    | inr d =>
      cases c <;> cases d <;>
        simp [pairObservationCovarianceMatrix, pairObservationWeight,
          normalizedWeightedSum_observationWeight, normalizedObservation]

end SRWTightness
