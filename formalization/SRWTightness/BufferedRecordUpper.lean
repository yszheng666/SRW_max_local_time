import SRWTightness.BufferedRecordProbability
import SRWTightness.ActualRecordProbabilityUpper

open MeasureTheory
namespace SRWTightness

/-- Buffered records inherit upper bounds from their inner entrance-layer marginals. -/
theorem buffered_record_probability_upper {M : Type*}
    (b : Site) (ρ H : ℝ) (hH : 1 ≤ H) (hρ : 8 * H ≤ ρ)
    (F : Site → PathWord → M) (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 4)
    (hp : ∀ x ∈ bufferedRecordMiddle b ρ H,
      |setHitProbability (translateFinset b (diskFinset (Real.exp 2 * ρ + H)))
        (translateFinset b (diskFinset (ρ - H))) x - 1 / 2| ≤ ε)
    (η Q : M → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hF : ∀ z : Site, ρ - H - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ ρ - H → ∀ r,
      pathLaw.real {ω |
        F z (killedPathWord (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) z ω) = r} ≤
        Real.exp (η r) * Q r) :
    ∀ rs x, x ∈ bufferedRecordMiddle b ρ H →
      pathLaw.real {ω | killedChildRecords
          (translateFinset b (diskFinset (Real.exp 2 * ρ + H)))
          (translateFinset b (diskFinset (ρ - H)))
          (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) x F ω = rs} ≤
        Real.exp (orderedRecordError (4 * ε) η rs) * orderedReferenceWeight Q rs := by
  have hρ0 : 0 ≤ ρ := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he12 : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
  have hmid : ρ ≤ Real.exp 1 * ρ := by nlinarith
  have hout : Real.exp 1 * ρ ≤ Real.exp 2 * ρ := mul_le_mul_of_nonneg_right he12 hρ0
  let B : Set Site := {z | z ∈ translateFinset b (diskFinset (ρ - H)) ∧
    ρ - H - 1 ≤ Real.sqrt (normSq (z - b)) ∧ Real.sqrt (normSq (z - b)) ≤ ρ - H}
  apply actual_supported_record_probability_upper _ _ _
    (Finset.image_subset_image (diskFinset_mono _ _ (by linarith) (by linarith)))
    (Finset.image_subset_image (diskFinset_mono _ _ (by linarith) (by linarith)))
    F (bufferedRecordMiddle b ρ H) B (fun _ hz ↦ hz.1)
  · intro y hy
    exact Or.inr (translated_disk_boundary_radial b _ (by linarith) y hy)
  · intro x hx
    have hx' := buffered_middle_mem_annulus ρ H hH hρ b x
      (middle_boundary_layers_in_buffer _ ρ H hH hx)
    filter_upwards [competingEntranceLaw_supported _ _ x,
      competingEntranceLaw_radial_support b (ρ - H) (Real.exp 2 * ρ + H)
        (by linarith) x hx'] with z hz hr
    exact ⟨hz, hr⟩
  · exact hε
  · exact hsmall
  · exact hp
  · exact hQ
  · intro z hz r
    exact hF z hz.2.1 hz.2.2 r

end SRWTightness
