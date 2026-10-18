import SRWTightness.SourceLongEscapeRadii
import SRWTightness.AnnulusEscapeRelative
import SRWTightness.RecordRadialSupport

namespace SRWTightness

/-- The buffered reference parameter is a genuine geometric-law parameter. -/
theorem buffered_long_escape_parameter_pos_lt_one (ρ H J : ℝ) (hρ : 0 < ρ)
    (hH : 0 ≤ H) (hHm : 5 * H ≤ ρ) (hJ : 0 < J) :
    0 < bufferedLongEscapeParameter ρ H J ∧ bufferedLongEscapeParameter ρ H J < 1 := by
  have hd : 0 < ρ - H := by linarith
  have hn : 0 < Real.log ((Real.exp 1 * ρ + H) / (ρ - H)) := by
    apply Real.log_pos
    apply (one_lt_div hd).mpr
    nlinarith [Real.exp_one_gt_two]
  have hsep : Real.exp 1 * ρ + H < Real.exp (J + 1) * ρ + H := by
    have he : Real.exp 1 < Real.exp (J + 1) := Real.exp_lt_exp.mpr (by linarith)
    nlinarith [mul_lt_mul_of_pos_right he hρ]
  have hlog : Real.log ((Real.exp 1 * ρ + H) / (ρ - H)) <
      Real.log ((Real.exp (J + 1) * ρ + H) / (ρ - H)) :=
    Real.log_lt_log (by positivity) (div_lt_div_of_pos_right hsep hd)
  have hden := hn.trans hlog
  exact ⟨div_pos hn hden, (div_lt_one hden).mpr hlog⟩

/-- Equation (8.1) for the actual source radii and every short-exit atom, with explicit uniform constants. -/
theorem source_long_escape_probability (hP : PotentialKernelAsymptoticInput) :
    ∃ C T : ℝ, 0 < C ∧ 2 ≤ T ∧ ∀ (m r : ℝ) (ℓ ν J : ℕ),
      0 ≤ r → 5 * sourceRecordBuffer r ≤ sourceRecordRadius m ℓ (ν + 1) →
      T ≤ sourceRecordRadius m ℓ (ν + 1) - sourceRecordBuffer r →
      1 ≤ J → J ≤ ν →
      (1 / 2 : ℝ) / ((J : ℝ) + 1) ≤ sourceLongEscapeParameter m r ℓ ν J ∧
      sourceLongEscapeParameter m r ℓ ν J ≤ 2 / ((J : ℝ) + 1) ∧
      ∀ b x : Site, x ∈ domainExitBoundary (sourceExitDomain m r ℓ b ν) →
      ∃ δ : ℝ, |δ| ≤ C * (sourceRecordBuffer r + 1) /
          (sourceRecordRadius m ℓ (ν + 1) - sourceRecordBuffer r) ∧
        pathLaw.real {ω | domainExit (sourceExitDomain m r ℓ b (ν - J)) x ω <
          setHittingTime (sourceEntranceDomain m r ℓ b ν) x 0 ω} =
          sourceLongEscapeParameter m r ℓ ν J * (1 + δ) := by
  obtain ⟨C, T, hC, hT, hh⟩ := annulus_escape_relative hP
  refine ⟨C, T, hC, hT, ?_⟩
  intro m r ℓ ν J hr hscale hlarge hJ hJν
  let ρ := sourceRecordRadius m ℓ (ν + 1)
  let H := sourceRecordBuffer r
  have hH : 0 ≤ H := by dsimp [H, sourceRecordBuffer]; linarith
  have ha2 : 2 ≤ ρ - H := hT.trans hlarge
  have hρ2 : 2 ≤ ρ := by linarith
  have hρ0 : 0 < ρ := by linarith
  have ha0 : 0 < ρ - H := by linarith
  have hJreal : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hp := buffered_long_escape_parameter_bounds ρ H (J : ℝ) hρ0 hH hscale hJreal
  refine ⟨hp.1, hp.2, ?_⟩
  intro b x hx
  have hshort : sourceExitDomain m r ℓ b ν =
      translateFinset b (diskFinset (Real.exp 1 * ρ + H)) := by
    dsimp [sourceExitDomain, ρ, H]
    rw [sourceRecordRadius_successor]
  have hlong : sourceExitDomain m r ℓ b (ν - J) =
      translateFinset b (diskFinset (Real.exp ((J : ℝ) + 1) * ρ + H)) := by
    dsimp [sourceExitDomain, ρ, H]
    rw [sourceRecordRadius_long m ℓ ν J hJν]
  rw [hshort] at hx
  have hshort0 : 0 ≤ Real.exp 1 * ρ + H := by positivity
  obtain ⟨hxl, hxu⟩ := translated_disk_boundary_radial b _ hshort0 x hx
  have hab : 2 * (ρ - H) ≤ Real.exp 1 * ρ + H := by
    nlinarith [Real.exp_one_gt_two]
  have hgap := buffered_long_radius_gap ρ H (J : ℝ) hρ2 hJreal
  obtain ⟨δ, hδ, he⟩ := hh (ρ - H) (Real.exp 1 * ρ + H)
    (Real.exp ((J : ℝ) + 1) * ρ + H) hlarge hab hgap b x hxl hxu
  refine ⟨δ, ?_, ?_⟩
  · exact hδ.trans (div_le_div_of_nonneg_right (show C ≤ C * (H + 1) by nlinarith [mul_nonneg hC.le hH]) ha0.le)
  · rw [hlong]
    exact he

end SRWTightness
