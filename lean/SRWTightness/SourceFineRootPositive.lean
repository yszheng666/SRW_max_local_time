import SRWTightness.SourceForestContinuationCoordinates

open MeasureTheory
namespace SRWTightness

/-- The root generation counts the roots in the whole finite forest. -/
theorem forest_root_population {M : Type*} (n : ℕ) (rs : List (FiniteExcursionRecord M n)) :
    forestLevelPopulation n rs n = rs.length := by
  simp only [forestLevelPopulation, finiteRecordLevelPopulation_root, List.map_const',
    List.sum_replicate, smul_eq_mul, mul_one]

/-- A positive terminal population forces a positive original root count at every admissible cut. -/
theorem source_fine_root_positive (hF : TwoLevelWordFlatteningInput)
    (t : ℝ) (b : Site) (K : Finset Site) (ν : ℕ)
    (hm : 16 ≤ sourceLowerRadius t)
    (hν : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t))
    (hD : sourceExitDomain (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b 0 ⊆ diskFinset (Real.exp t)) :
    ∀ᵐ ω ∂pathLaw,
      0 < sourceActualCount t b (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) ω →
      0 < sourceActualCount t b ν ω := by
  filter_upwards [source_fine_forest_population hF t b K ν hm hν hD] with ω hp
  intro hterm
  let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)
  have hr := hp n le_rfl
  have he : sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (n + 1) = ν := by
    dsimp [n]; omega
  rw [he, forest_root_population] at hr
  have ht := hp 0 (Nat.zero_le n)
  simp only [Nat.zero_add] at ht
  by_contra h
  have hz : sourceActualCount t b ν ω = 0 := by omega
  have hnil : sourceActualFineForest t b K ν ω = [] := List.length_eq_zero_iff.mp (hr.trans hz)
  rw [hnil] at ht
  simp only [forestLevelPopulation, List.map_nil, List.sum_nil] at ht
  omega

end SRWTightness
