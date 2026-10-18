import SRWTightness.BufferedForestError
import SRWTightness.SourceUpperForestScale

open Filter

namespace SRWTightness

/-- Quadratic count caps give the manuscript exponential error scale for the actual upper radii. -/
theorem source_upper_forest_error_bound (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop, ∀ (a : ℝ), 1 ≤ a →
      a ≤ 2 * upperTerminalFineRadius (sourceUpperLogRadius t) →
      ∀ (M : Type*) (n : ℕ) (rs : List (FiniteExcursionRecord M n)),
      (∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ 16 * t ^ 2) →
      (rs.map (finiteRecordError
        (fun i ↦ 4 * (B * sourceUpperBuffer t / growingRecordRadius (sourceUpperRadius t) i))
        (fun _ ↦ 2 * (W * (a + 1) / sourceUpperRadius t *
          Real.log (sourceUpperRadius t / a))) n)).sum ≤
        (3584 * B + 96 * W) * t ^ 2 * sourceUpperLogRadius t *
          Real.exp (-3 * sourceUpperLogRadius t / 4) := by
  filter_upwards [sourceUpperLogRadius_eventually 1,
    eventually_ge_atTop (max 2 (Real.exp 1))] with t hD ht
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let m := sourceUpperRadius t
  let D := sourceUpperLogRadius t
  have ht2 : 2 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have hl : 1 ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans ht)
    simpa only [Real.log_exp] using h
  have hr : 1 ≤ r := by
    change (1 : ℝ) ≤ (sourceUpperBlockSide t : ℝ)
    exact_mod_cast (show 1 ≤ sourceUpperBlockSide t from sourceUpperBlockSide_pos t)
  have hm : 0 < m := Real.exp_pos _
  have hratio := source_upper_fine_ratio_bound t ht0 hl
  have hquad : t ^ 2 * r ≤ m := by
    have h := (div_le_div_iff₀ hm ht0).mp hratio
    dsimp [r, m]
    nlinarith
  have hrm : 2 * r ≤ m := by
    have h := mul_le_mul_of_nonneg_right (show 2 ≤ t ^ 2 by nlinarith)
      (show 0 ≤ r by linarith)
    nlinarith
  have hH : 0 ≤ sourceUpperBuffer t := by unfold sourceUpperBuffer; positivity
  have hHr : sourceUpperBuffer t ≤ 14 * r := by unfold sourceUpperBuffer; dsimp [r]; linarith
  intro a ha har M n rs hcounts
  have ha0 : 0 < a := by linarith
  have ham : a ≤ m := har.trans hrm
  have hlog0 : 0 ≤ Real.log (m / a) :=
    Real.log_nonneg ((le_div_iff₀ ha0).mpr (by simpa using ham))
  have hlogD : Real.log (m / a) ≤ D := by
    rw [Real.log_div hm.ne' ha0.ne']
    have heq : Real.log m = D := Real.log_exp _
    rw [heq]
    linarith [Real.log_nonneg ha]
  have har3 : a + 1 ≤ 3 * r := by linarith
  have hraw := buffered_forest_quadratic_error B W 16 (sourceUpperBuffer t) m a t
    hB hW (by norm_num) hH hm ha0 ham n rs hcounts
  have hfirst : 16 * B * sourceUpperBuffer t * 16 * t ^ 2 / m ≤
      3584 * B * t ^ 2 * (r / m) := by
    calc
      _ = (256 * B * t ^ 2 / m) * sourceUpperBuffer t := by ring
      _ ≤ (256 * B * t ^ 2 / m) * (14 * r) :=
        mul_le_mul_of_nonneg_left hHr (by positivity)
      _ = _ := by ring
  have hsecond : 2 * W * 16 * t ^ 2 * (a + 1) / m * Real.log (m / a) ≤
      96 * W * t ^ 2 * D * (r / m) := by
    have hprod := mul_le_mul har3 hlogD hlog0 (by positivity : 0 ≤ 3 * r)
    calc
      _ = (32 * W * t ^ 2 / m) * ((a + 1) * Real.log (m / a)) := by ring
      _ ≤ (32 * W * t ^ 2 / m) * ((3 * r) * D) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by ring
  have hDfirst : 3584 * B * t ^ 2 * (r / m) ≤
      3584 * B * t ^ 2 * D * (r / m) := by
    calc
      _ = (3584 * B * t ^ 2 * (r / m)) * 1 := by ring
      _ ≤ (3584 * B * t ^ 2 * (r / m)) * D :=
        mul_le_mul_of_nonneg_left hD (by positivity)
      _ = _ := by ring
  calc
    _ ≤ _ := hraw
    _ ≤ 3584 * B * t ^ 2 * D * (r / m) + 96 * W * t ^ 2 * D * (r / m) :=
      add_le_add (hfirst.trans hDfirst) hsecond
    _ = (3584 * B + 96 * W) * t ^ 2 * D * (r / m) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (source_upper_fine_exponential_ratio t)
      (by dsimp [D]; positivity)

end SRWTightness
