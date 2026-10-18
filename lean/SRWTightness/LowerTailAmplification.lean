import SRWTightness.DiskAmplification
import SRWTightness.AmplificationScaleChoice
import SRWTightness.DiskCenterGrowth

open MeasureTheory Filter

namespace SRWTightness

theorem prob_disk_sqrt_lt_le_pow {a R : ℝ} (ha : 0 ≤ a) (J : ℕ)
    (hgeom : (J : ℝ) * (a + 1) < R) (t : ℝ) (ht : 0 ≤ t) :
    pathLaw.real {ω | Real.sqrt (diskMax R ω) < t} ≤
      (pathLaw.real {ω | Real.sqrt (diskMax a ω) < t}) ^ J := by
  have he (r : ℝ) : {ω | Real.sqrt (diskMax r ω) < t} = {ω | diskMax r ω < ⌈t ^ 2⌉₊} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.sqrt_lt (Nat.cast_nonneg _) ht, Nat.lt_ceil]
  rw [he R, he a]
  exact prob_disk_max_lt_le_pow_real ha J _ hgeom

/-- Finite-radius amplification on the actual SRW, with the manuscript's floor choices. -/
theorem prob_disk_lower_shift_le_pow (s R : ℝ) (hs : 0 ≤ s)
    (hR : (amplificationScale s : ℝ) < R) :
    pathLaw.real {ω | diskFluctuation R ω < -s} ≤
      (pathLaw.real {ω | Real.sqrt (diskMax (R / amplificationScale s) ω) <
        diskCenter (R / amplificationScale s)}) ^ (amplificationScale s / 2) := by
  have hQ : (0 : ℝ) < amplificationScale s := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (amplificationScale_pos s hs))
  have ha : 1 < R / amplificationScale s := (lt_div_iff₀ hQ).mpr (by simpa using hR)
  have hc := diskCenter_amplification_shift s R hs hR
  have hsub : {ω | diskFluctuation R ω < -s} ⊆
      {ω | Real.sqrt (diskMax R ω) < diskCenter (R / amplificationScale s)} := by
    intro ω hω
    change Real.sqrt (diskMax R ω) < diskCenter (R / amplificationScale s)
    change Real.sqrt (diskMax R ω) - diskCenter R < -s at hω
    linarith
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (prob_disk_sqrt_lt_le_pow (by linarith : 0 ≤ R / amplificationScale s) _
      (amplificationScale_geometry s R hs hR) _ (diskCenter_pos _ ha).le)

theorem prob_disk_below_center_le_of_seed (R p : ℝ)
    (hseed : p ≤ pathLaw.real {ω | diskCenter R ≤ Real.sqrt (diskMax R ω)}) :
    pathLaw.real {ω | Real.sqrt (diskMax R ω) < diskCenter R} ≤ 1 - p := by
  have hm : Measurable (fun ω ↦ Real.sqrt (diskMax R ω : ℝ)) :=
    Real.continuous_sqrt.measurable.comp ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_diskMax R))
  have hc := probReal_compl_eq_one_sub (μ := pathLaw) (measurableSet_le (measurable_const (a := diskCenter R)) hm)
  have he : {ω | diskCenter R ≤ Real.sqrt (diskMax R ω)}ᶜ =
      {ω | Real.sqrt (diskMax R ω) < diskCenter R} := by ext ω; simp
  rw [he] at hc
  linarith

theorem prob_disk_lower_shift_le_seed_power (s R p : ℝ) (hs : 0 ≤ s)
    (hR : (amplificationScale s : ℝ) < R)
    (hseed : p ≤ pathLaw.real {ω | diskCenter (R / amplificationScale s) ≤
      Real.sqrt (diskMax (R / amplificationScale s) ω)}) :
    pathLaw.real {ω | diskFluctuation R ω < -s} ≤ (1 - p) ^ (amplificationScale s / 2) := by
  refine (prob_disk_lower_shift_le_pow s R hs hR).trans ?_
  exact pow_le_pow_left₀ (measureReal_nonneg) (prob_disk_below_center_le_of_seed _ p hseed) _

end SRWTightness
