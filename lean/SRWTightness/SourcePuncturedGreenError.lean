import SRWTightness.PuncturedGreenFlatness
import SRWTightness.SourceTerminalGreenFlatness
import SRWTightness.SourceTerminalEscapeLower

namespace SRWTightness

/-- Source relative punctured Green control on the intermediate outer boundary. -/
theorem source_punctured_green_relative_error (hinput : PotentialKernelAsymptoticInput) :
    ∃ W M A₀ : ℝ, 0 ≤ W ∧ 8 ≤ M ∧ 2 ≤ A₀ ∧ ∀ (m H a : ℝ),
      M ≤ m → A₀ ≤ a → 0 ≤ H → H ≤ m / 2 → 2 * a < m - H - 2 →
      ∀ (b z x : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
        (m - H - 1 ≤ Real.sqrt (normSq (z - b)) ∧
          Real.sqrt (normSq (z - b)) ≤ m - H + 1) →
        (3 * a / 2 ≤ Real.sqrt (normSq (x - b)) ∧
          Real.sqrt (normSq (x - b)) ≤ 3 * a / 2 + 1) →
        |killedGreen (translateFinset b (diskFinset (Real.exp 1 * m + H)) \ K) x z -
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
            (1 - setHitProbability (translateFinset b (diskFinset (Real.exp 1 * m + H))) K x)| ≤
          (W * (a + 1) / m * Real.log (m / a)) *
            (1 - setHitProbability (translateFinset b (diskFinset (Real.exp 1 * m + H))) K x) := by
  obtain ⟨L, M, hL, hM, hflat⟩ := source_terminal_green_flatness hinput
  obtain ⟨c, A₀, hc, hA₀, hesc⟩ := source_terminal_escape_lower hinput
  refine ⟨2 * L / c, M, A₀, by positivity, hM, hA₀, ?_⟩
  intro m H a hm ha hH hHm hsep b z x K hK hz hx
  have hm0 : 0 < m := by linarith
  have ha0 : 0 < a := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hR0 : 0 < Real.exp 1 * m + H := by nlinarith
  let D := translateFinset b (diskFinset (Real.exp 1 * m + H))
  have hzD : z ∈ D := by
    simp only [D, mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq]
    have hs := Real.sq_sqrt (normSq_nonneg (z - b))
    have hn := Real.sqrt_nonneg (normSq (z - b))
    have hupper : Real.sqrt (normSq (z - b)) < Real.exp 1 * m + H := by nlinarith [hz.2]
    nlinarith
  have hKD : K ⊆ D := hK.trans
    (Finset.image_subset_image (diskFinset_mono a _ ha0.le (by nlinarith)))
  have hsym (y : Site) : killedGreen D y z = killedGreen D z y := by
    by_cases hy : y ∈ D
    · exact killedGreen_symm D y z hy hzD
    · rw [killedGreen_zero_of_not_mem D y z hy, killedGreen_zero_of_target_not_mem D z y hy]
  let α := (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))
  have hpoint (y : Site) (hy : Real.sqrt (normSq (y - b)) ≤ 3 * a / 2 + 1) :
      |killedGreen D y z - α| ≤ L * (a + 1) / m := by
    rw [hsym]
    exact hflat m H a hm hH hHm ha0.le hsep b z y hz hy
  have htarget : ∀ y ∈ K, |killedGreen D y z - α| ≤ L * (a + 1) / m := by
    intro y hy
    have hn : normSq (y - b) < a ^ 2 := by
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hK hy
    have hr : Real.sqrt (normSq (y - b)) ≤ a :=
      (Real.sqrt_le_left ha0.le).mpr hn.le
    exact hpoint y (by linarith)
  have ht : 0 < Real.log (m / a) := Real.log_pos ((one_lt_div ha0).mpr (by linarith))
  have hh := punctured_green_relative_from_flatness D K hKD x z α (L * (a + 1) / m)
    c (Real.log (m / a)) (by positivity) hc ht htarget (hpoint x hx.2)
    (hesc m H a ha (by linarith) hH hHm b x K hK hx)
  convert hh using 1 <;> ring

end SRWTightness
