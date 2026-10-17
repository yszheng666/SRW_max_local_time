import SRWTightness.SourceGeneralForestError

open scoped BigOperators
namespace SRWTightness

/-- The literal error bound uses actual forward counts for every source buffer
and path projection. -/
theorem source_general_actual_forest_error {M : Type*} (B W m a r : ℝ)
    (hB : 0 ≤ B) (hW : 0 ≤ W) (hH : 0 ≤ sourceRecordBuffer r) (hm : 0 < m)
    (ha : 0 < a) (ham : a ≤ m) (ℓ k : ℕ) (hk : k < ℓ)
    (b : Site) (D : Finset Site) (x : Site) (F : Site → PathWord → M) (ω : Sample) :
    let rs := killedChildRecords D (sourceEntranceDomain m r ℓ b k)
      (sourceExitDomain m r ℓ b k) x
      (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        F (ℓ - (k + 1))) ω
    (rs.map (finiteRecordError
      (fun i ↦ 4 * (B * sourceRecordBuffer r / growingRecordRadius m i))
      (fun _ ↦ 2 * (W * (a + 1) / m * Real.log (m / a))) (ℓ - (k + 1)))).sum ≤
    (4 * B + 2 * W) * (∑ j ∈ Finset.Icc (k + 1) (ℓ - 1),
      ((sourceForwardRecordCount m r ℓ k (j - 1) b D x ω : ℝ) +
        sourceForwardRecordCount m r ℓ k j b D x ω) *
        sourceRecordBuffer r / sourceRecordRadius m ℓ (j + 1)) +
    (4 * B + 2 * W) * sourceForwardRecordCount m r ℓ k (ℓ - 1) b D x ω *
      (a + 1) / m * Real.log (m / a) := by
  dsimp only
  have h := source_general_forest_error B W (sourceRecordBuffer r) m a
    hB hW hH hm ha ham ℓ k hk
    (killedChildRecords D (sourceEntranceDomain m r ℓ b k)
      (sourceExitDomain m r ℓ b k) x
      (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        F (ℓ - (k + 1))) ω)
  have ht := source_forest_population m r ℓ k (ℓ - 1) (by omega) (by omega)
    b D x F ω
  have hzero : ℓ - (ℓ - 1 + 1) = 0 := by omega
  rw [hzero] at ht
  rw [ht] at h
  convert h using 1
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  have hp := source_forest_population m r ℓ k (j - 1) (by omega) (by omega) b D x F ω
  have hidx : ℓ - (j - 1 + 1) = ℓ - j := by omega
  rw [hidx] at hp
  rw [hp, source_forest_population m r ℓ k j (by omega) (by omega) b D x F ω]

end SRWTightness
