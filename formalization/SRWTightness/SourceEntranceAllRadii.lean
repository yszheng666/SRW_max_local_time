import SRWTightness.SourceEntranceRelative

namespace SRWTightness

/-- Uniform entrance atom comparison for every positive observation radius, using a fixed enclosure. -/
theorem source_entrance_all_positive_radii (hinput : PotentialKernelAsymptoticInput) :
    ∃ W M : ℝ, 0 ≤ W ∧ 8 ≤ M ∧ ∀ (m H a : ℝ),
      M ≤ m → 0 < a → 0 ≤ H → H ≤ m / 2 → 2 * a < m - H - 2 →
      ∀ (b z : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
        (m - H - 1 ≤ Real.sqrt (normSq (z - b)) ∧
          Real.sqrt (normSq (z - b)) ≤ m - H + 1) → ∀ v ∈ K,
        |(competingEntranceLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K z).real {v} -
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
            equilibriumMeasure (translateFinset b (diskFinset (Real.exp 1 * m + H))) K v| ≤
          (W * (a + 1) / m * Real.log (m / a)) *
            (((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
              equilibriumMeasure (translateFinset b (diskFinset (Real.exp 1 * m + H))) K v) := by
  obtain ⟨W, M, A₀, hW, hM, hA₀, hh⟩ := source_entrance_atom_relative_error hinput
  let V := W * (A₀ + 1)
  let N := max M (4 * A₀ + 8)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  refine ⟨V, N, hV, hM.trans (le_max_left _ _), ?_⟩
  intro m H a hm ha hH hHm hsep b z K hK hz v hv
  have hMm : M ≤ m := (le_max_left _ _).trans hm
  have hAm : 4 * A₀ + 8 ≤ m := (le_max_right _ _).trans hm
  have hm0 : 0 < m := by linarith
  have hlog : 0 ≤ Real.log (m / a) :=
    (Real.log_pos ((one_lt_div ha).mpr (by linarith))).le
  have hα : 0 ≤ (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)) :=
    le_trans (by positivity) (source_terminal_alpha_lower m H hm0 hH (by linarith))
  have he : 0 ≤ ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
      equilibriumMeasure (translateFinset b (diskFinset (Real.exp 1 * m + H))) K v :=
    mul_nonneg hα (equilibriumMeasure_nonneg _ K v)
  by_cases hlarge : A₀ ≤ a
  · refine (hh m H a hMm hlarge hH hHm hsep b z K hK hz v hv).trans ?_
    apply mul_le_mul_of_nonneg_right _ he
    apply mul_le_mul_of_nonneg_right _ hlog
    apply div_le_div_of_nonneg_right _ hm0.le
    apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ a + 1)
    dsimp [V]
    nlinarith [mul_nonneg hW (show 0 ≤ A₀ by linarith)]
  · have haA : a ≤ A₀ := (lt_of_not_ge hlarge).le
    have hA0 : 0 < A₀ := by linarith
    have hKA : K ⊆ translateFinset b (diskFinset A₀) := hK.trans
      (Finset.image_subset_image (diskFinset_mono a A₀ ha.le haA))
    have hp := hh m H A₀ hMm le_rfl hH hHm (by linarith) b z K hKA hz v hv
    refine hp.trans ?_
    apply mul_le_mul_of_nonneg_right _ he
    have hlogs : Real.log (m / A₀) ≤ Real.log (m / a) :=
      Real.log_le_log (div_pos hm0 hA0) (div_le_div_of_nonneg_left hm0.le ha haA)
    calc
      W * (A₀ + 1) / m * Real.log (m / A₀) ≤
          V / m * Real.log (m / a) :=
        mul_le_mul_of_nonneg_left hlogs (div_nonneg hV hm0.le)
      _ ≤ V * (a + 1) / m * Real.log (m / a) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        apply div_le_div_of_nonneg_right _ hm0.le
        nlinarith [mul_nonneg hV ha.le]

end SRWTightness
