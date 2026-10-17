import SRWTightness.ProjectedMarkUniformGaussianTail
import SRWTightness.SourceUpperSmallCountEventually
import SRWTightness.SourceUpperPaddedDiagonalVariance
import SRWTightness.LatticeDiameterCount
import SRWTightness.MarkSumZeroMaximum
import SRWTightness.SourceUpperSlopeError

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SRWTightness

/-- Every small terminal count, including zero, contributes only the source Gaussian error. -/
theorem source_upper_small_count_occupation (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (c : ℝ) (hc : 0 < c) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ∀ᶠ t : ℝ in atTop,
      let D := diskFinset (sourceUpperMarkRadius t)
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let r := upperTerminalFineRadius (sourceUpperLogRadius t)
      ∀ (A : Finset Site), A.Nonempty →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤ (c * r) ^ 2) →
      ∀ (K : Finset Site) (hAK : A ⊆ K) (hKD : K ⊆ D),
      sourceUpperIntensity t * capacity D K ≤ 1 →
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ k : ℕ,
      Real.sqrt (2 * (k : ℝ)) ≤ t - 1 →
      (markProductLaw D K (sourceUpperIntensity t) k).real
        {Y | ∃ z : A, sourceUpperVisitCutoff t s ≤ sumMarks K k Y ⟨z, hAK z.property⟩} ≤
      C * r ^ 2 * Real.exp (-ρ * t ^ 2 / d) := by
  obtain ⟨V, hV, hv⟩ := source_upper_padded_diagonal_variance hScale
  obtain ⟨K₀, hK₀, hcount⟩ := lattice_diameter_count hCount c hc
  obtain ⟨B, _, hcond⟩ := source_upper_threshold_conditions hScale
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 10))
  refine ⟨1152 * K₀, (2 / Real.pi) / (200 * V), by positivity, by positivity, ?_⟩
  filter_upwards [hv, hcond, hl] with t hv ht hl
  dsimp only
  intro A hA hdiam K hAK hKD hcap s hs hslog k hk
  obtain ⟨ht0, _, hsize, _, _, hr, hd, _⟩ := ht
  have hd0 : 0 < upperTerminalDepth (sourceUpperLogRadius t) := by linarith
  have hlog : Real.log t ≤ t / 10 := by
    have hh := (div_lt_iff₀ ht0).mp hl
    linarith
  have hy : 0 < sourceUpperHeight t s :=
    ht0.trans_le (source_upper_height_bounds t s ht0 hs hslog).1
  have hcut : 1 ≤ sourceUpperVisitCutoff t s := by
    change 0 < Nat.ceil (sourceUpperHeight t s ^ 2 / Real.pi)
    exact Nat.ceil_pos.mpr (div_pos (sq_pos_of_pos hy) Real.pi_pos)
  by_cases hk0 : k = 0
  · subst k
    rw [markSum_zero_projected_max_probability _ _ _ hAK _ _ hcut]
    positivity
  have hk1 : 1 ≤ k := by omega
  have hH : 0 ≤ sourceUpperBuffer t := by
    unfold sourceUpperBuffer upperTerminalFineRadius
    positivity
  have halpha := sourceReferenceIntensity_error (sourceUpperRadius t) (sourceUpperBuffer t)
    (Real.exp_pos _) hH hsize
  have hα : 0 ≤ sourceUpperIntensity t := by
    change 0 ≤ sourceReferenceIntensity (sourceUpperRadius t) (sourceUpperBuffer t)
    have hg : 0 < (2 / Real.pi : ℝ) := by positivity
    linarith [halpha.1]
  have hb := source_upper_small_count_height t s (Real.sqrt (2 * (k : ℝ)))
    ht0 hs hlog (Real.sqrt_nonneg _) hk hsize
  rw [← gaussian_mark_threshold_normalization k (sourceUpperVisitCutoff t s)
    (sourceUpperIntensity t) (2 / Real.pi) hα] at hb
  have hraw := (le_div_iff₀ (show 0 < Real.sqrt (2 / Real.pi) by positivity)).mp hb
  have hpos : 0 ≤ Real.sqrt (2 * (sourceUpperVisitCutoff t s : ℝ)) -
      Real.sqrt (2 * ((k : ℝ) * sourceUpperIntensity t)) := by
    have hbase : 0 ≤ t / 10 * Real.sqrt (2 / Real.pi) := by positivity
    linarith
  have hprob := projected_fixed_mark_uniform_gaussian_tail
    (diskFinset (sourceUpperMarkRadius t)) A K hAK hKD (sourceUpperIntensity t) hα hcap
    k (sourceUpperVisitCutoff t s) hk1 hcut
    (V * upperTerminalDepth (sourceUpperLogRadius t)) (mul_pos hV hd0)
    (fun z ↦ hv z (hKD (hAK z.property))) hpos
  have he := source_upper_small_count_exponential t s V
    (upperTerminalDepth (sourceUpperLogRadius t)) k ht0 hs hlog hk hsize hV hd0
  have hcard := hcount (upperTerminalFineRadius (sourceUpperLogRadius t)) hr A hA hdiam
  have hbound := mul_le_mul
    (mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 1152)) he
    (Real.exp_pos _).le (by positivity : 0 ≤ 1152 *
      (K₀ * upperTerminalFineRadius (sourceUpperLogRadius t) ^ 2))
  calc
    _ ≤ _ := hprob.trans hbound
    _ = _ := by ring

end SRWTightness
