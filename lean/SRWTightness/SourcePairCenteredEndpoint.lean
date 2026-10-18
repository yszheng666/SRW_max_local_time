import SRWTightness.SourcePairMeanTranslation

namespace SRWTightness

/-- The centered prefix endpoint is exactly the last retained Gaussian average coordinate. -/
theorem pairCenteredBridgedPath_endpoint (t A : ℝ) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (x : PairObservationIndex (I - i + 1) → ℝ) (ω : ℕ → GaussianCoefficientSpace) :
    pairCenteredBridgedPath t A I i x ω (sourceObservationTime t A I (I - i + 1)) =
      x (.inl (Fin.last (I - i))) := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  have hs : ∀ j < I + 1, sourceObservationTime t A I j <
      sourceObservationTime t A I (j + 1) := fun j hj ↦ by linarith [hg j (by omega)]
  unfold pairCenteredBridgedPath
  rw [timeGridBridge_node _ _ _ hs (by omega), add_zero,
    timeGridInterpolation_node _ _ _ _ hs (by omega)]
  have hr := pairObservationExtension_retained I i x (Fin.last (I - i))
  simp only [observationMeshValue,
    dif_pos (show 0 < I - i + 1 ∧ I - i + 1 ≤ I + 1 from ⟨by omega, by omega⟩)]
  simpa only [sourcePairAverageIndex, Fin.val_last, Fin.castSucc, Fin.castAdd, Fin.castLE,
    Nat.add_sub_cancel] using hr

end SRWTightness
