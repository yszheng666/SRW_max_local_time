import SRWTightness.TimeOneSidedComparison
import Mathlib.Order.LiminfLimsup

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

theorem time_limsup_tail_le_disk_bounds (A K C U L : ℝ) (hA : 1 < A)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      |diskCenter (Real.sqrt n / A) - timeCenter n| ≤ C ∧
      |diskCenter (A * Real.sqrt n) - timeCenter n| ≤ C)
    (hu : limsup (fun R : ℝ ↦ pathLaw.real {ω | K < diskFluctuation R ω}) atTop ≤ U)
    (hl : limsup (fun R : ℝ ↦ pathLaw.real {ω | diskFluctuation R ω < -K}) atTop ≤ L) :
    limsup (fun n : ℕ ↦ pathLaw.real {ω | K + C < |timeFluctuation n ω|}) atTop ≤
      2 / A ^ 2 + L + U := by
  have hAp : 0 < A := by linarith
  apply (limsup_le_iff
    (isCoboundedUnder_le_of_le atTop (fun n ↦ measureReal_nonneg))
    (isBoundedUnder_of ⟨1, fun n ↦ measureReal_le_one⟩)).mpr
  intro b hb
  let δ := (b - (2 / A ^ 2 + L + U)) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have heu : ∀ᶠ R : ℝ in atTop, pathLaw.real {ω | K < diskFluctuation R ω} < U + δ :=
    eventually_lt_of_limsup_lt (by linarith)
      (isBoundedUnder_of ⟨1, fun R ↦ measureReal_le_one⟩)
  have hel : ∀ᶠ R : ℝ in atTop, pathLaw.real {ω | diskFluctuation R ω < -K} < L + δ :=
    eventually_lt_of_limsup_lt (by linarith)
      (isBoundedUnder_of ⟨1, fun R ↦ measureReal_le_one⟩)
  have hs : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hrlo := (hs.atTop_div_const hAp).eventually hel
  have hrhi := (hs.const_mul_atTop hAp).eventually heu
  have he : ∀ᶠ n : ℕ in atTop,
      2 / A ^ 2 + 2 / (A * Real.sqrt n) + 1 / (n : ℝ) < 2 / A ^ 2 + δ :=
    (scaled_disk_comparison_error_tendsto A hAp).eventually (gt_mem_nhds (by linarith))
  filter_upwards [hcenter, hrlo, hrhi, he, eventually_ge_atTop (1 : ℕ)] with n hc hnl hnu hne hn
  have hh := time_tail_le_one_sided_disk_tails A hA n hn K C hc.1 hc.2
  dsimp [δ] at *
  linarith

end SRWTightness
