import SRWTightness.FiniteDomain
import SRWTightness.CoordinateBounds
import Mathlib.Data.Int.Interval

namespace SRWTightness

 theorem finite_disk (R : ℝ) : (disk R).Finite := by
  let B : ℤ := ⌈|R|⌉
  have hB : |R| ≤ (B : ℝ) := Int.le_ceil _
  apply ((Set.finite_Icc (-B) B).prod (Set.finite_Icc (-B) B)).subset
  intro z hz
  have hsq : normSq z ≤ |R| ^ 2 := by
    have h : normSq z < R ^ 2 := hz
    simpa only [sq_abs] using h.le
  have hf : |(z.1 : ℝ)| ≤ (B : ℝ) :=
    (abs_fst_le_normSq_bound z (abs_nonneg R) hsq).trans hB
  have hs : |(z.2 : ℝ)| ≤ (B : ℝ) :=
    (abs_snd_le_normSq_bound z (abs_nonneg R) hsq).trans hB
  have hfi : |z.1| ≤ B := by exact_mod_cast hf
  have hsi : |z.2| ≤ B := by exact_mod_cast hs
  exact ⟨abs_le.mp hfi, abs_le.mp hsi⟩

noncomputable def diskFinset (R : ℝ) : Finset Site := (finite_disk R).toFinset

@[simp] theorem mem_diskFinset (R : ℝ) (x : Site) : x ∈ diskFinset R ↔ x ∈ disk R :=
  Set.Finite.mem_toFinset (finite_disk R)

 theorem coe_diskFinset (R : ℝ) : (diskFinset R : Set Site) = disk R := by
  ext x
  exact mem_diskFinset R x

 theorem domainExit_disk (R : ℝ) : domainExit (diskFinset R) 0 = exitTime R := by
  unfold domainExit exitTime
  rw [coe_diskFinset]
  simp only [zero_add]

 theorem domainSteps_disk (R : ℝ) (ω : Sample) : domainSteps (diskFinset R) 0 ω = exitSteps R ω := by
  unfold domainSteps exitSteps
  rw [domainExit_disk]

end SRWTightness
