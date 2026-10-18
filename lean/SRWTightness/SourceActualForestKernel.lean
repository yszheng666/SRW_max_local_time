import SRWTightness.SourceActualRootList
import SRWTightness.SourceActualRecordKernel

open MeasureTheory

namespace SRWTightness

/-- Exact exterior forest kernel with each root carrying its actual complete internal tree. -/
theorem source_actual_forest_kernel (R m r : ℝ) (ℓ k : ℕ) (hk : k < ℓ)
    (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m) (b : Site)
    (hroot : sourceExitDomain m r ℓ b k ⊆ diskFinset R)
    {M : Type*} (F : Site → PathWord → M)
    (rs : List (FiniteExcursionRecord M (ℓ - (k + 1)))) :
    let A := sourceEntranceDomain m r ℓ b k
    let C := sourceExitDomain m r ℓ b k
    let T := actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
      F (ℓ - (k + 1))
    pathLaw.real {ω | sourceForwardRecordCount m r ℓ k k b (diskFinset R) 0 ω = rs.length ∧
      actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        F (ℓ - (k + 1) + 1) 0 (killedPathWord (diskFinset R) 0 ω) = rs} =
      orderedRecordWeight (competingEntranceLaw (diskFinset R) A)
        (fun z v ↦ recordExitSlice C z (fun ω ↦ T z (killedPathWord C z ω)) v)
        (competingExitMass (diskFinset R) A) rs 0 := by
  dsimp only
  simp_rw [source_forward_root_count, source_actual_root_list m r ℓ k hk]
  exact source_root_record_kernel R m r ℓ k hk hr hm b hroot
    (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
      F (ℓ - (k + 1))) rs

end SRWTightness
