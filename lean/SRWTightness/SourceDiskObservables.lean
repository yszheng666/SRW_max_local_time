import SRWTightness.SourceTimeObservables
import SRWTightness.DiskOnePoint
import SRWTightness.ExitMoment

open MeasureTheory

namespace SRWTightness

/-- The squared-norm implementation is exactly the source's open Euclidean disk. -/
theorem source_disk_region_iff (R : ℝ) (hR : 0 < R) (x : Site) :
    x ∈ disk R ↔ Real.sqrt (normSq x) < R :=
  (Real.sqrt_lt (normSq_nonneg x) hR.le).symm

/-- Every visited point before a finite disk exit lies in the open disk. -/
theorem source_disk_visited_subset (R : ℝ) (ω : Sample) (hfin : exitTime R ω ≠ ⊤) :
    ∀ x ∈ visited ω (exitSteps R ω), x ∈ disk R := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  apply before_exit_mem
  rw [← coe_exitSteps R ω hfin]
  exact WithTop.coe_lt_coe.mpr (Finset.mem_range.mp hk)

/-- Stopped occupations vanish at every lattice site outside the disk, including its boundary. -/
theorem source_disk_localTime_outside (R : ℝ) (ω : Sample) (hfin : exitTime R ω ≠ ⊤)
    (x : Site) (hx : x ∉ disk R) : localTime ω (exitSteps R ω) x = 0 := by
  apply localTime_eq_zero_of_not_mem
  intro hv
  exact hx (source_disk_visited_subset R ω hfin x hv)

/-- The numerical stopping time is almost surely exactly the first exit, with the open-disk convention. -/
theorem source_disk_first_exit (R : ℝ) (hR : 0 < R) :
    ∀ᵐ ω ∂pathLaw,
      (exitSteps R ω : WithTop ℕ) = exitTime R ω ∧
      (∀ k : ℕ, k < exitSteps R ω → Real.sqrt (normSq (position ω k)) < R) ∧
      R ≤ Real.sqrt (normSq (position ω (exitSteps R ω))) := by
  filter_upwards [exitTime_ne_top_ae hR.le] with ω hfin
  have he := coe_exitSteps R ω hfin
  refine ⟨he, ?_, ?_⟩
  · intro k hk
    apply (source_disk_region_iff R hR _).mp
    apply before_exit_mem
    rw [← he]
    exact WithTop.coe_lt_coe.mpr hk
  · apply (Real.le_sqrt hR.le (normSq_nonneg _)).mpr
    exact normSq_at_exit_ge R ω (exitSteps R ω) he.symm

/-- Source (1.3): exact stopped occupations, unrestricted maximum, exterior support and centering. -/
theorem source_disk_observables (R : ℝ) (hR : 0 < R) :
    ∀ᵐ ω ∂pathLaw,
      (exitSteps R ω : WithTop ℕ) = exitTime R ω ∧
      (∀ x : Site, localTime ω (exitSteps R ω) x =
        ∑ k ∈ Finset.range (exitSteps R ω), if position ω k = x then 1 else 0) ∧
      (∀ x : Site, domainLocalTime (diskFinset R) 0 x ω = localTime ω (exitSteps R ω) x) ∧
      IsGreatest (Set.range (localTime ω (exitSteps R ω))) (diskMax R ω) ∧
      (∀ x : Site, x ∉ disk R → localTime ω (exitSteps R ω) x = 0) ∧
      diskCenter R = (2 * Real.log R - Real.log (Real.log R)) / Real.sqrt Real.pi := by
  filter_upwards [exitTime_ne_top_ae hR.le] with ω hfin
  refine ⟨coe_exitSteps R ω hfin, fun _ ↦ rfl, ?_, ?_, ?_, rfl⟩
  · exact fun x ↦ domainLocalTime_disk R x ω
  · exact maxLocalTime_isGreatest ω (exitSteps R ω)
  · exact fun x hx ↦ source_disk_localTime_outside R ω hfin x hx

end SRWTightness
