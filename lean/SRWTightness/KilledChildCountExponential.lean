import SRWTightness.KilledChildCountTail
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring

open MeasureTheory

namespace SRWTightness

/-- An exponential return bound gives an exponential count tail with the first entrance retained. -/
theorem killedChildIntervals_count_exp_tail (D K C : Finset Site)
    (hKC : K ⊆ C) (hCD : C ⊆ D) (H : ℝ)
    (hreturn : ∀ ξ ∈ domainExitBoundary C, setHitProbability D K ξ ≤ 1 - 1 / H)
    (n : ℕ) (x : Site) :
    pathLaw.real {ω | n + 1 ≤ (killedChildIntervals D K C x ω).length} ≤
      setHitProbability D K x * Real.exp (-(n : ℝ) / H) := by
  have hb := killedChildIntervals_count_tail D K C hKC hCD (Real.exp (-(1 / H)))
    (Real.exp_nonneg _) (fun ξ hξ ↦ (hreturn ξ hξ).trans (Real.one_sub_le_exp_neg _)) n x
  rw [← Real.exp_nat_mul] at hb
  simpa only [mul_neg, mul_one_div, neg_div] using hb

/-- Positive square-root thresholds preserve the first entrance mass in the count tail. -/
theorem killedChildIntervals_sqrt_count_tail (D K C : Finset Site)
    (hKC : K ⊆ C) (hCD : C ⊆ D) (H : ℝ) (hH : 0 < H)
    (hreturn : ∀ ξ ∈ domainExitBoundary C, setHitProbability D K ξ ≤ 1 - 1 / H)
    (x : Site) (u : ℝ) (hu : 0 < u) :
    pathLaw.real {ω | u ≤ Real.sqrt (2 * (killedChildIntervals D K C x ω).length)} ≤
      setHitProbability D K x * Real.exp (1 / H - u ^ 2 / (2 * H)) := by
  let n := Nat.ceil (u ^ 2 / 2)
  have hn : 1 ≤ n := Nat.ceil_pos.mpr (by positivity)
  have hevent : {ω | u ≤ Real.sqrt (2 * (killedChildIntervals D K C x ω).length)} ⊆
      {ω | n ≤ (killedChildIntervals D K C x ω).length} := by
    intro ω hω
    apply Nat.ceil_le.mpr
    have hs := (Real.le_sqrt' hu).mp hω
    linarith
  have hb := killedChildIntervals_count_exp_tail D K C hKC hCD H hreturn (n - 1) x
  rw [Nat.sub_add_cancel hn] at hb
  have hp : 0 ≤ setHitProbability D K x := by
    rw [setHitProbability_eq_probability]
    exact measureReal_nonneg
  refine (measureReal_mono hevent).trans (hb.trans ?_)
  apply mul_le_mul_of_nonneg_left _ hp
  apply Real.exp_le_exp.mpr
  have hceil : u ^ 2 / 2 ≤ (n : ℝ) := Nat.le_ceil _
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  rw [hcast]
  have hd := div_le_div_of_nonneg_right hceil hH.le
  calc
    -((n : ℝ) - 1) / H = 1 / H - (n : ℝ) / H := by ring
    _ ≤ 1 / H - (u ^ 2 / 2) / H := sub_le_sub_left hd _
    _ = _ := by ring

end SRWTightness
