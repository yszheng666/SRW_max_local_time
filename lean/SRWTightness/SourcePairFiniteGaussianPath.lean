import SRWTightness.ExternalFiniteGaussianBridgeKernel
import SRWTightness.SourcePairMeanTranslation

namespace SRWTightness

/-- The actual retained-coordinate extension is exactly the finite Gaussian endpoint mesh. -/
theorem pairObservationExtension_mesh (I i : ℕ)
    (x : PairObservationIndex (I - i + 1) → ℝ) :
    observationMeshValue (pairObservationExtension I i x) =
      finiteGaussianMesh (I - i + 1) (fun j ↦ x (.inl j)) := by
  funext j
  by_cases h : 0 < j ∧ j ≤ I - i + 1
  · have hfull : 0 < j ∧ j ≤ I + 1 := ⟨h.1, by omega⟩
    have hj : j - 1 < I - i + 1 := by omega
    simp only [observationMeshValue, finiteGaussianMesh, dif_pos h, dif_pos hfull]
    simpa only [sourcePairAverageIndex, Fin.castSucc, Fin.castAdd, Fin.castLE] using
      pairObservationExtension_retained I i x ⟨j - 1, hj⟩
  · by_cases hfull : 0 < j ∧ j ≤ I + 1
    · have hj : ¬j - 1 < I - i + 1 := by omega
      simp only [observationMeshValue, finiteGaussianMesh, dif_neg h, dif_pos hfull,
        pairObservationExtension, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hj]
    · simp only [observationMeshValue, finiteGaussianMesh, dif_neg h, dif_neg hfull]

theorem pairCenteredBridgedPath_finiteGaussian (t A : ℝ) (I i : ℕ)
    (x : PairObservationIndex (I - i + 1) → ℝ) (ω : ℕ → GaussianCoefficientSpace) (v : ℝ) :
    pairCenteredBridgedPath t A I i x ω v =
      finiteGaussianBridgedPath (sourceObservationTime t A I) (I - i + 1) (I + 1)
        (fun j ↦ x (.inl j)) ω v := by
  unfold pairCenteredBridgedPath finiteGaussianBridgedPath
  rw [pairObservationExtension_mesh]

end SRWTightness
