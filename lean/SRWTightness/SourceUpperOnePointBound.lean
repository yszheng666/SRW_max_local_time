import SRWTightness.SourceUpperOnePointExponent

open Filter MeasureTheory

namespace SRWTightness

/-- The actual source cutoff has the one-point tail with its spatial logarithmic prefactor. -/
theorem source_upper_one_point_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s →
      ∀ x : Site, normSq x ≤ (Real.exp t / 2) ^ 2 →
      pathLaw.real {ω | sourceUpperVisitCutoff t s ≤
        domainLocalTime (diskFinset (Real.exp t)) 0 x ω} ≤
      K * t * Real.exp (-2 * t) * Real.exp (-(2 * Real.sqrt Real.pi * s)) *
        (1 + Real.log (Real.exp t / max (Real.sqrt (normSq x)) 1)) := by
  obtain ⟨C, hC, hc⟩ := disk_one_point_log_tail
  refine ⟨C * Real.exp (Real.pi * diskDiagonalError + Real.pi) * Real.pi, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (Real.pi * diskDiagonalError)),
    Real.tendsto_exp_atTop.eventually (eventually_ge_atTop 4)] with t ht hR
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have htD : Real.pi * diskDiagonalError ≤ t := (le_max_right _ _).trans ht
  have hπ := Real.pi_pos
  have hdlo : t / Real.pi ≤ (2 / Real.pi) * t - diskDiagonalError := by
    apply (div_le_iff₀ hπ).mpr
    field_simp
    nlinarith
  have hd : 0 < (2 / Real.pi) * t - diskDiagonalError :=
    (div_pos ht0 hπ).trans_le hdlo
  intro s hs x hx
  have hy : 0 < sourceUpperHeight t s := by
    have hl := Real.log_le_sub_one_of_pos ht0
    have hp : 0 ≤ Real.sqrt Real.pi * s := by positivity
    unfold sourceUpperHeight
    linarith
  have hcut : 1 ≤ sourceUpperVisitCutoff t s := by
    change 0 < Nat.ceil (sourceUpperHeight t s ^ 2 / Real.pi)
    exact Nat.ceil_pos.mpr (div_pos (sq_pos_of_pos hy) hπ)
  have hnorm : Real.sqrt (normSq x) ≤ Real.exp t / 2 := by
    nlinarith [Real.sq_sqrt (normSq_nonneg x), Real.sqrt_nonneg (normSq x), Real.exp_pos t]
  have hmax : max (Real.sqrt (normSq x)) 1 ≤ Real.exp t := by
    apply max_le <;> linarith
  have hmax0 : 0 < max (Real.sqrt (normSq x)) 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hlog0 : 0 ≤ Real.log (Real.exp t / max (Real.sqrt (normSq x)) 1) :=
    Real.log_nonneg ((le_div_iff₀ hmax0).mpr (by simpa using hmax))
  let L := 1 + Real.log (Real.exp t / max (Real.sqrt (normSq x)) 1)
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hp := hc (Real.exp t) hR (by simpa only [Real.log_exp] using hd) x hx _ hcut
  simp only [Real.log_exp] at hp
  have hpref : C * L / ((2 / Real.pi) * t - diskDiagonalError) ≤ C * L / (t / Real.pi) :=
    div_le_div_of_nonneg_left (mul_nonneg hC.le hL) (div_pos ht0 hπ) hdlo
  have hbase : pathLaw.real {ω | sourceUpperVisitCutoff t s ≤
      domainLocalTime (diskFinset (Real.exp t)) 0 x ω} ≤
      C * L / ((2 / Real.pi) * t - diskDiagonalError) *
        Real.exp (-((sourceUpperVisitCutoff t s - 1 : ℕ) : ℝ) /
          ((2 / Real.pi) * t + diskDiagonalError)) := by
    simpa only [domainLocalTime_disk, L] using hp
  apply hbase.trans
  calc
    _ ≤ C * L / ((2 / Real.pi) * t - diskDiagonalError) *
        (Real.exp (Real.pi * diskDiagonalError + Real.pi) * t ^ 2 *
          Real.exp (-2 * t) * Real.exp (-(2 * Real.sqrt Real.pi * s))) :=
      mul_le_mul_of_nonneg_left (source_upper_one_point_exponential t s ht1) (by positivity)
    _ ≤ (C * L / (t / Real.pi)) *
        (Real.exp (Real.pi * diskDiagonalError + Real.pi) * t ^ 2 *
          Real.exp (-2 * t) * Real.exp (-(2 * Real.sqrt Real.pi * s))) :=
      mul_le_mul_of_nonneg_right hpref (by positivity)
    _ = _ := by
      dsimp [L]
      field_simp
      <;> ring

end SRWTightness
