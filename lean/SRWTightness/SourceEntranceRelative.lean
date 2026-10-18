import SRWTightness.SourceEntranceAtoms
import SRWTightness.Capacity

namespace SRWTightness

/-- The terminal reference intensity is bounded below by the lattice logarithmic constant. -/
theorem source_terminal_alpha_lower (m H : ℝ) (hm : 0 < m) (hH : 0 ≤ H) (hHm : H < m) :
    (2 / Real.pi : ℝ) ≤ (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)) := by
  have hr : 0 < m - H := by linarith
  have he : Real.exp 1 ≤ (Real.exp 1 * m + H) / (m - H) := by
    apply (le_div_iff₀ hr).mpr
    nlinarith [mul_nonneg (Real.exp_pos (1 : ℝ)).le hH]
  have hl := Real.log_le_log (Real.exp_pos (1 : ℝ)) he
  rw [Real.log_exp] at hl
  have hg : 0 ≤ (2 / Real.pi : ℝ) := by positivity
  nlinarith

/-- Source entrance comparison normalized relative to the complete reference atom αe. -/
theorem source_entrance_atom_relative_error (hinput : PotentialKernelAsymptoticInput) :
    ∃ W M A₀ : ℝ, 0 ≤ W ∧ 8 ≤ M ∧ 2 ≤ A₀ ∧ ∀ (m H a : ℝ),
      M ≤ m → A₀ ≤ a → 0 ≤ H → H ≤ m / 2 → 2 * a < m - H - 2 →
      ∀ (b z : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
        (m - H - 1 ≤ Real.sqrt (normSq (z - b)) ∧
          Real.sqrt (normSq (z - b)) ≤ m - H + 1) → ∀ v ∈ K,
        |(competingEntranceLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K z).real {v} -
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
            equilibriumMeasure (translateFinset b (diskFinset (Real.exp 1 * m + H))) K v| ≤
          (W * (a + 1) / m * Real.log (m / a)) *
            (((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
              equilibriumMeasure (translateFinset b (diskFinset (Real.exp 1 * m + H))) K v) := by
  obtain ⟨W, M, A₀, hW, hM, hA₀, hh⟩ := source_entrance_atom_error hinput
  let g : ℝ := 2 / Real.pi
  have hg : 0 < g := by dsimp [g]; positivity
  refine ⟨W / g, M, A₀, by positivity, hM, hA₀, ?_⟩
  intro m H a hm ha hH hHm hsep b z K hK hz v hv
  have hm0 : 0 < m := by linarith
  have ha0 : 0 < a := by linarith
  have ht : 0 ≤ Real.log (m / a) :=
    (Real.log_pos ((one_lt_div ha0).mpr (by linarith))).le
  let α := (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))
  have hα : g ≤ α := source_terminal_alpha_lower m H hm0 hH (by linarith)
  have hnon : 0 ≤ (W / g) * (a + 1) / m * Real.log (m / a) := by positivity
  have he : ((W / g) * (a + 1) / m * Real.log (m / a)) * g =
      W * (a + 1) / m * Real.log (m / a) := by field_simp
  have hb := mul_le_mul_of_nonneg_left hα hnon
  rw [he] at hb
  have hb' := mul_le_mul_of_nonneg_right hb
    (equilibriumMeasure_nonneg (translateFinset b (diskFinset (Real.exp 1 * m + H))) K v)
  have hp := (hh m H a hm ha hH hHm hsep b z K hK hz v hv).trans hb'
  simpa only [α, mul_assoc] using hp

end SRWTightness
