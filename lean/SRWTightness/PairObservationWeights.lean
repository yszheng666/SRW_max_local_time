import SRWTightness.ObservationWeights
import SRWTightness.PairTiltWeights

namespace SRWTightness

/-- Retained averages and two separately labelled site coordinates. -/
abbrev PairObservationIndex (n : ℕ) := Fin n ⊕ Bool

noncomputable def pairObservationWeight {n : ℕ} (D M : Finset Site)
    (K : Fin n → Finset Site) (z y : M) : PairObservationIndex n → M → ℝ
  | .inl i => observationWeight D M K z (some i)
  | .inr false => observationWeight D M K z none
  | .inr true => observationWeight D M K y none

theorem pairObservationWeight_probability {n : ℕ} (D M : Finset Site)
    (K : Fin n → Finset Site) (z y : M) (hKM : ∀ i, K i ⊆ M) (hMD : M ⊆ D)
    (hne : ∀ i, (K i).Nonempty) :
    (∀ i x, 0 ≤ pairObservationWeight D M K z y i x) ∧
      ∀ i, ∑ x : M, pairObservationWeight D M K z y i x = 1 := by
  constructor
  · intro i x
    cases i with
    | inl i => exact observationWeight_nonneg D M K z (some i) x
    | inr b => cases b <;> exact observationWeight_nonneg D M K _ none x
  · intro i
    cases i with
    | inl i => exact observationWeight_sum D M K z hKM hMD hne (some i)
    | inr b => cases b <;> exact observationWeight_sum D M K _ hKM hMD hne none

noncomputable def pairObservationTilt {n : ℕ} (last : Fin n)
    (i : PairObservationIndex n) : ℝ :=
  pairTiltWeight (.inr false) (.inr true) (fun j ↦ if j = .inl last then 1 else 0) i

theorem pairObservationTilt_l1 {n : ℕ} (last : Fin n) :
    (∑ i, |pairObservationTilt last i|) ≤ 6 := by
  apply pairTiltWeight_l1
  · intro i; split <;> norm_num
  · simp

/-- The vector tilt is exactly the original signed two-site statistic. -/
theorem pairObservationTilt_statistic {n : ℕ} (D M : Finset Site)
    (K : Fin n → Finset Site) (z y : M) (last : Fin n)
    (k : ℕ) (α g u : ℝ) (Y : MarkSamples M k) :
    (∑ i, pairObservationTilt last i *
      normalizedWeightedSum M k α g u (pairObservationWeight D M K z y i) Y) =
      2 * (normalizedMarkSum M k α g u z Y + normalizedMarkSum M k α g u y Y -
        normalizedEquilibriumAverage D M (K last) k α g u Y) := by
  unfold pairObservationTilt
  rw [pairTiltWeight_sum]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [pairObservationWeight, normalizedWeightedSum_observationWeight,
    normalizedObservation]

end SRWTightness
