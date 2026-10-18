import SRWTightness.SourceUpperBlockReference
import SRWTightness.GrowingRecordComparison

open Filter MeasureTheory

namespace SRWTightness

/-- The full comparison exponent for one upper reference tree. -/
noncomputable def sourceUpperTreeError {M : Type*} (B W t : ℝ) (n : ℕ)
    (r : FiniteExcursionRecord M n) : ℝ :=
  finiteRecordError
    (fun i ↦ 4 * (B * sourceUpperBuffer t / growingRecordRadius (sourceUpperRadius t) i))
    (fun _ ↦ 2 * (W * (2 * upperTerminalFineRadius (sourceUpperLogRadius t) + 1) /
      sourceUpperRadius t * Real.log (sourceUpperRadius t /
        (2 * upperTerminalFineRadius (sourceUpperLogRadius t))))) n r

/-- Actual upper trees satisfy both sides of the source reference comparison at every depth. -/
theorem source_upper_tree_probability_comparison (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ ∀ᶠ t : ℝ in atTop, ∀ b : Site, ∀ n : ℕ,
      ∀ x : Site, ∀ r : FiniteExcursionRecord (Mark (sourceUpperBlock t b)) n,
      growingRecordRadius (sourceUpperRadius t) n - sourceUpperBuffer t - 1 ≤
        Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤
        growingRecordRadius (sourceUpperRadius t) n - sourceUpperBuffer t →
      let p := pathLaw.real {ω | actualFiniteWordRecord
        (growingRecordEntrance b (sourceUpperRadius t) (sourceUpperBuffer t))
        (growingRecordExit b (sourceUpperRadius t) (sourceUpperBuffer t))
        (wordOccupationMark (sourceUpperBlock t b)) n x
        (killedPathWord (growingRecordExit b (sourceUpperRadius t) (sourceUpperBuffer t) n)
          x ω) = r}
      let q := finiteRecordReferenceWeight (fun v ↦ (sourceUpperBlockMarkLaw t b).real {v}) n r
      Real.exp (-sourceUpperTreeError B W t n r) * q ≤ p ∧
        p ≤ Real.exp (sourceUpperTreeError B W t n r) * q := by
  obtain ⟨B, W, T, M, hB, hW, hT, hM, hh⟩ := growing_record_probability_comparison hinput
  refine ⟨B, W, hB, hW, ?_⟩
  filter_upwards [source_upper_record_scale_conditions B T M hB,
    source_upper_terminal_comparison_small W hW, source_upper_block_capacity_half]
    with t hs he hc
  intro b
  obtain ⟨hH, hm, hTm, hMm, hsmall, hsep⟩ := hs
  have hr : (0 : ℝ) < upperTerminalFineRadius (sourceUpperLogRadius t) := by
    change (0 : ℝ) < (sourceUpperBlockSide t : ℝ)
    exact_mod_cast sourceUpperBlockSide_pos t
  exact hh b (sourceUpperRadius t) (sourceUpperBuffer t)
    (2 * upperTerminalFineRadius (sourceUpperLogRadius t)) (sourceUpperBlock t b)
    hH hm hTm hMm hsmall (by positivity) (by linarith)
    (sourceUpperBlock_subset_observation_ball t b) (hc b) he

end SRWTightness
