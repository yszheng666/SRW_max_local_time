import SRWTightness.SourceAnnularEntrance

namespace SRWTightness

/-- Uniform positive first-entrance mass for arbitrary separated source scales and buffers. -/
theorem source_general_annular_entrance (hinput : PotentialKernelAsymptoticInput) :
    ∃ c A : ℝ, 0 < c ∧ ∀ (R m H : ℝ), A ≤ m - H → 0 ≤ H → 2 * H ≤ m →
      32 * Real.exp 1 * m ≤ R → ∀ b : Site,
      R / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ R / 3 →
      c ≤ setHitProbability (diskFinset R)
        (translateFinset b (diskFinset
          (sourceRecordRadius m (sourceRootDepth R m) 1 - H))) 0 := by
  obtain ⟨K, A, hK, hA, hh⟩ := annulus_fine_entrance_bound hinput
  have hg : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 < sourceRootReturnShift := by
    have h32 := Real.log_nonneg (show (1 : ℝ) ≤ 32 by norm_num)
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    dsimp [sourceRootReturnShift]
    linarith
  refine ⟨Real.log (3 / 2 : ℝ) / (2 * sourceRootReturnShift),
    max 2 (max A (2 * K / Real.log (3 / 2 : ℝ))), by positivity, ?_⟩
  intro R m H hmH hH hhalf hscale b hblo hbhi
  have htA : A ≤ m - H := (le_max_left _ _).trans ((le_max_right _ _).trans hmH)
  have htK : 2 * K / Real.log (3 / 2 : ℝ) ≤ m - H :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hmH)
  have hm2 : 2 ≤ m - H := (le_max_left _ _).trans hmH
  have hm : 0 < m := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hbase : 32 * m ≤ R := by nlinarith
  have hdepth := source_root_depth_pos R m hm hscale
  let ℓ := sourceRootDepth R m
  let a := sourceRecordRadius m ℓ 1 - H
  have hrad := sourceRecordRadius_ge_terminal m hm.le ℓ 1 (by
    dsimp [ℓ]; omega)
  have haA : A ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have haK : 2 * K / Real.log (3 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have hsmall : K / a ≤ Real.log (3 / 2 : ℝ) / 2 := by
    apply (div_le_iff₀ ha0).mpr
    have hhK := (div_le_iff₀ hg).mp haK
    nlinarith
  have hR : 0 < R := by nlinarith
  have hbr := source_root_depth_bracket R m hm hbase
  have hmono := sourceRecordRadius_antitone m hm.le ℓ
    (show 0 ≤ (1 : ℕ) by omega)
  have haR : a ≤ R / 4 := by dsimp [a, ℓ] at *; linarith [hbr.1]
  have hlocal := hh a (R / 2) (R / 3) haA (by linarith)
    (by linarith) (-b) (by simpa only [normSq_neg] using haR.trans hblo)
    (by simpa only [normSq_neg] using hbhi)
  have hratio : (R / 2) / (R / 3) = (3 / 2 : ℝ) := by
    field_simp [ne_of_gt hR]
    <;> ring
  rw [hratio] at hlocal
  have hden : 0 < Real.log ((R / 2) / a) :=
    Real.log_pos ((one_lt_div ha0).mpr (by linarith))
  have hlogupper := source_root_log_denominator R m H ℓ 0
    hm hR (by linarith) hbr.2.le
  have hdenC : Real.log ((R / 2) / a) ≤ sourceRootReturnShift := by
    have hle := Real.log_le_log (div_pos (by positivity : 0 < R / 2) ha0)
      (div_le_div_of_nonneg_right (by linarith : R / 2 ≤ 2 * R) ha0.le)
    dsimp [a] at hle
    simp only [Nat.cast_zero, zero_add] at hlogupper
    dsimp [sourceRootReturnShift]
    exact hle.trans (by linarith)
  have hlower : Real.log (3 / 2 : ℝ) / (2 * sourceRootReturnShift) ≤
      (Real.log (3 / 2 : ℝ) - K / a) / Real.log ((R / 2) / a) := by
    calc
      _ = (Real.log (3 / 2 : ℝ) / 2) / sourceRootReturnShift := by ring
      _ ≤ (Real.log (3 / 2 : ℝ) / 2) / Real.log ((R / 2) / a) :=
        div_le_div_of_nonneg_left (by positivity) hden hdenC
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hden.le
  have hfit : Real.sqrt (normSq b) + R / 2 + 1 < R := by linarith
  have hsub := (root_domain_and_exit_inside b (R / 2) R
    (by positivity) hfit).1
  have hdom := setHitProbability_mono_domain (translateFinset b (diskFinset (R / 2)))
    (diskFinset R) (translateFinset b (diskFinset a)) hsub 0
  have htrans : setHitProbability (translateFinset b (diskFinset (R / 2)))
      (translateFinset b (diskFinset a)) 0 =
      setHitProbability (diskFinset (R / 2)) (diskFinset a) (-b) := by
    simpa only [add_neg_cancel] using setHitProbability_translate b
      (diskFinset (R / 2)) (diskFinset a) (-b)
  rw [htrans] at hdom
  exact (hlower.trans hlocal).trans hdom

end SRWTightness
