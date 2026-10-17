import SRWTightness.SourcePairPathRestriction

open MeasureTheory

namespace SRWTightness

/-- Extend retained averages to the full source coordinate space; unused coordinates are zero. -/
def pairObservationExtension (I i : ℕ) :
    (PairObservationIndex (I - i + 1) → ℝ) →ₗ[ℝ] (Fin ((I + 1) + 1) → ℝ) where
  toFun x j := if h : j.val < I - i + 1 then x (.inl ⟨j.val, h⟩) else 0
  map_add' x y := by
    funext j
    by_cases h : j.val < I - i + 1
    · simp only [dif_pos h, Pi.add_apply]
    · simp only [dif_neg h, Pi.add_apply, add_zero]
  map_smul' a x := by
    funext j
    by_cases h : j.val < I - i + 1
    · simp only [dif_pos h, Pi.smul_apply, RingHom.id_apply]
    · simp only [dif_neg h, Pi.smul_apply, RingHom.id_apply, smul_zero]

theorem pairObservationExtension_retained (I i : ℕ)
    (x : PairObservationIndex (I - i + 1) → ℝ) (j : Fin (I - i + 1)) :
    pairObservationExtension I i x (sourcePairAverageIndex I i j) = x (.inl j) := by
  simp only [pairObservationExtension, LinearMap.coe_mk, AddHom.coe_mk,
    sourcePairAverageIndex, Fin.val_castSucc, dif_pos j.isLt]

theorem pairObservationExtension_measurable (I i : ℕ) :
    Measurable (pairObservationExtension I i) := by
  apply measurable_pi_lambda
  intro j
  change Measurable (fun x : PairObservationIndex (I - i + 1) → ℝ ↦
    if h : j.val < I - i + 1 then x (.inl ⟨j.val, h⟩) else 0)
  split
  · exact measurable_pi_apply _
  · exact measurable_const

/-- The extension reproduces the actual source path whenever the retained averages agree. -/
theorem pairObservationExtension_prefix (t A : ℝ) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (x : PairObservationIndex (I - i + 1) → ℝ) (y : Fin ((I + 1) + 1) → ℝ)
    (hxy : ∀ j, x (.inl j) = y (sourcePairAverageIndex I i j))
    (ω : ℕ → GaussianCoefficientSpace) (v : ℝ)
    (hv : v ≤ sourceObservationTime t A I (I - i + 1)) :
    sourceBridgedPath t A I (pairObservationExtension I i x) ω v =
      sourceBridgedPath t A I y ω v := by
  apply source_pair_bridged_prefix_congr t A I i hA ht hI _ _ _ ω v hv
  intro j
  rw [pairObservationExtension_retained]
  exact hxy j

end SRWTightness
