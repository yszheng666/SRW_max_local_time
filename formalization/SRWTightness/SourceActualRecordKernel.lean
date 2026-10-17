import SRWTightness.ActualRecordKernel
import SRWTightness.SourceExcursionDomains

open MeasureTheory

namespace SRWTightness

/-- The manuscript's ordered record kernel, instantiated at its concrete buffered radii. -/
theorem source_actual_ordered_record_kernel (m r : ℝ) (ℓ j : ℕ) (hj : j + 2 ≤ ℓ)
    (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m) (b : Site)
    {R : Type*} (F : Site → PathWord → R) (rs : List R) (x : Site) :
    let D := sourceExitDomain m r ℓ b j
    let K := sourceEntranceDomain m r ℓ b (j + 1)
    let C := sourceExitDomain m r ℓ b (j + 1)
    pathLaw.real {ω | killedChildRecords D K C x F ω = rs} =
      orderedRecordWeight (competingEntranceLaw D K)
        (fun z r ↦ recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r)
        (competingExitMass D K) rs x := by
  dsimp only
  apply actual_ordered_record_kernel
  · exact sourceEntranceDomain_subset_exit m r ℓ b (j + 1) hr hm (by omega)
  · exact sourceExitDomain_successor_subset m r ℓ b j hr hm

/-- The source root-forest law, including its exact root count and all joint root exit kernels. -/
theorem source_root_record_kernel (R m r : ℝ) (ℓ k : ℕ) (hk : k < ℓ)
    (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m) (b : Site)
    (hroot : sourceExitDomain m r ℓ b k ⊆ diskFinset R)
    {M : Type*} (F : Site → PathWord → M) (rs : List M) :
    let D := diskFinset R
    let K := sourceEntranceDomain m r ℓ b k
    let C := sourceExitDomain m r ℓ b k
    pathLaw.real {ω | (killedChildIntervals D K C 0 ω).length = rs.length ∧
      killedChildRecords D K C 0 F ω = rs} =
      orderedRecordWeight (competingEntranceLaw D K)
        (fun z r ↦ recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r)
        (competingExitMass D K) rs 0 := by
  dsimp only
  apply actual_ordered_record_kernel_with_count
  · exact sourceEntranceDomain_subset_exit m r ℓ b k hr hm (by omega)
  · exact hroot

end SRWTightness
