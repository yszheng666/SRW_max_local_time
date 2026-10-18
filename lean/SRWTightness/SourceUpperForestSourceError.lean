import SRWTightness.SourceUpperComparisonScales

open Filter

namespace SRWTightness

/-- The first inequality of (4.22), retaining both raw source error terms. -/
theorem source_upper_forest_raw_source_error (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop, ∀ (M : Type*) (n : ℕ)
      (rs : List (FiniteExcursionRecord M n)),
      (∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ 16 * t ^ 2) →
      let r := upperTerminalFineRadius (sourceUpperLogRadius t)
      let m := sourceUpperRadius t
      (rs.map (finiteRecordError
        (fun i ↦ 4 * (B * sourceUpperBuffer t / growingRecordRadius m i))
        (fun _ ↦ 2 * (W * (2 * r + 1) / m * Real.log (m / (2 * r)))) n)).sum ≤
        (3584 * B + 96 * W) * t ^ 2 * (r / m + (r + 1) / m * Real.log (m / r)) := by
  filter_upwards [source_upper_record_scale_conditions 0 0 0 (by norm_num)] with t hs
  intro M n rs hcounts
  dsimp only
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let m := sourceUpperRadius t
  change _ ≤ (3584 * B + 96 * W) * t ^ 2 *
    (r / m + (r + 1) / m * Real.log (m / r))
  have hr : 1 ≤ r := by
    change (1 : ℝ) ≤ (sourceUpperBlockSide t : ℝ)
    exact_mod_cast (show 1 ≤ sourceUpperBlockSide t from sourceUpperBlockSide_pos t)
  have hr0 : 0 < r := by linarith
  have hm : 0 < m := Real.exp_pos _
  have hH : sourceUpperBuffer t = 4 * r + 10 := rfl
  have hH0 : 0 ≤ sourceUpperBuffer t := by rw [hH]; linarith
  have hHr : sourceUpperBuffer t ≤ 14 * r := by rw [hH]; linarith
  have hmr : 2 * r ≤ m := by
    have h := hs.2.1
    rw [hH] at h
    change 8 * (4 * r + 10) ≤ m at h
    linarith
  have hlog0 : 0 ≤ Real.log (m / (2 * r)) :=
    Real.log_nonneg ((le_div_iff₀ (by positivity)).mpr (by linarith))
  have hlog : Real.log (m / (2 * r)) ≤ Real.log (m / r) :=
    Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_left hm.le hr0 (by linarith))
  have hlogr : 0 ≤ Real.log (m / r) := hlog0.trans hlog
  have hraw := buffered_forest_quadratic_error B W 16 (sourceUpperBuffer t) m (2 * r) t
    hB hW (by norm_num) hH0 hm (by positivity) hmr n rs hcounts
  have hfirst : 16 * B * sourceUpperBuffer t * 16 * t ^ 2 / m ≤
      3584 * B * t ^ 2 * (r / m) := by
    calc
      _ = (256 * B * t ^ 2 / m) * sourceUpperBuffer t := by ring
      _ ≤ (256 * B * t ^ 2 / m) * (14 * r) :=
        mul_le_mul_of_nonneg_left hHr (by positivity)
      _ = _ := by ring
  have hsecond : 2 * W * 16 * t ^ 2 * (2 * r + 1) / m * Real.log (m / (2 * r)) ≤
      96 * W * t ^ 2 * ((r + 1) / m * Real.log (m / r)) := by
    have hprod := mul_le_mul (show 2 * r + 1 ≤ 3 * (r + 1) by linarith) hlog
      hlog0 (by positivity : 0 ≤ 3 * (r + 1))
    calc
      _ = (32 * W * t ^ 2 / m) * ((2 * r + 1) * Real.log (m / (2 * r))) := by ring
      _ ≤ (32 * W * t ^ 2 / m) * ((3 * (r + 1)) * Real.log (m / r)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by ring
  have hx : 0 ≤ r / m := by positivity
  have hy : 0 ≤ (r + 1) / m * Real.log (m / r) := by positivity
  calc
    _ ≤ _ := hraw
    _ ≤ 3584 * B * t ^ 2 * (r / m) +
        96 * W * t ^ 2 * ((r + 1) / m * Real.log (m / r)) := add_le_add hfirst hsecond
    _ ≤ _ := by
      nlinarith only [mul_nonneg (show 0 ≤ 3584 * B * t ^ 2 by positivity) hy,
        mul_nonneg (show 0 ≤ 96 * W * t ^ 2 by positivity) hx]

/-- The raw source error terms have the exponential scale in the second inequality of (4.22). -/
theorem source_upper_raw_error_shape_bound :
    ∀ᶠ t : ℝ in atTop,
      let r := upperTerminalFineRadius (sourceUpperLogRadius t)
      let m := sourceUpperRadius t
      r / m + (r + 1) / m * Real.log (m / r) ≤
        3 * sourceUpperLogRadius t * Real.exp (-3 * sourceUpperLogRadius t / 4) := by
  filter_upwards [sourceUpperLogRadius_eventually 1,
    source_upper_radius_dominates_fine 1] with t hD hmr
  dsimp only
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let m := sourceUpperRadius t
  let D := sourceUpperLogRadius t
  change r / m + (r + 1) / m * Real.log (m / r) ≤ 3 * D * Real.exp (-3 * D / 4)
  have hr : 1 ≤ r := by
    change (1 : ℝ) ≤ (sourceUpperBlockSide t : ℝ)
    exact_mod_cast (show 1 ≤ sourceUpperBlockSide t from sourceUpperBlockSide_pos t)
  have hr0 : 0 < r := by linarith
  have hm : 0 < m := Real.exp_pos _
  have hmr' : r ≤ m := by simpa only [one_mul] using hmr
  have hD' : 1 ≤ D := hD
  have hlog0 : 0 ≤ Real.log (m / r) :=
    Real.log_nonneg ((le_div_iff₀ hr0).mpr (by simpa only [one_mul] using hmr'))
  have hlogD : Real.log (m / r) ≤ D := by
    rw [Real.log_div hm.ne' hr0.ne']
    have heq : Real.log m = D := Real.log_exp _
    rw [heq]
    linarith only [Real.log_nonneg hr]
  have hprod := mul_le_mul (show r + 1 ≤ 2 * r by linarith) hlogD hlog0
    (show 0 ≤ 2 * r by positivity)
  have hp := div_le_div_of_nonneg_right hprod hm.le
  have hf := mul_le_mul_of_nonneg_right hD' (show 0 ≤ r / m by positivity)
  have hp' : (r + 1) / m * Real.log (m / r) ≤ 2 * D * (r / m) := by
    calc
      _ = (r + 1) * Real.log (m / r) / m := by ring
      _ ≤ 2 * r * D / m := hp
      _ = _ := by ring
  have hf' : r / m ≤ D * (r / m) := by simpa only [one_mul] using hf
  calc
    _ ≤ D * (r / m) + 2 * D * (r / m) := add_le_add hf' hp'
    _ = 3 * D * (r / m) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (source_upper_fine_exponential_ratio t)
      (by dsimp [D]; positivity)

end SRWTightness
