import SRWTightness.SourcePuncturedGreenError
import SRWTightness.PuncturedLocalGeometry
import SRWTightness.EntranceAtomComparison

namespace SRWTightness

/-- Source entrance atoms are uniformly compared with equilibrium measure at large scales. -/
theorem source_entrance_atom_error (hinput : PotentialKernelAsymptoticInput) :
    ∃ W M A₀ : ℝ, 0 ≤ W ∧ 8 ≤ M ∧ 2 ≤ A₀ ∧ ∀ (m H a : ℝ),
      M ≤ m → A₀ ≤ a → 0 ≤ H → H ≤ m / 2 → 2 * a < m - H - 2 →
      ∀ (b z : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
        (m - H - 1 ≤ Real.sqrt (normSq (z - b)) ∧
          Real.sqrt (normSq (z - b)) ≤ m - H + 1) → ∀ v ∈ K,
        |(competingEntranceLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K z).real {v} -
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
            equilibriumMeasure (translateFinset b (diskFinset (Real.exp 1 * m + H))) K v| ≤
          (W * (a + 1) / m * Real.log (m / a)) *
            equilibriumMeasure (translateFinset b (diskFinset (Real.exp 1 * m + H))) K v := by
  obtain ⟨W, M, A₀, hW, hM, hA₀, hh⟩ := source_punctured_green_relative_error hinput
  refine ⟨W, M, A₀, hW, hM, hA₀, ?_⟩
  intro m H a hm ha hH hHm hsep b z K hK hz v hv
  have ha2 : 2 ≤ a := hA₀.trans ha
  have hm0 : 0 < m := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hR0 : 0 < Real.exp 1 * m + H := by nlinarith
  let D := translateFinset b (diskFinset (Real.exp 1 * m + H))
  let B := translateFinset b (diskFinset (3 * a / 2))
  let A := B \ K
  have hKB : K ⊆ B := hK.trans
    (Finset.image_subset_image (diskFinset_mono a _ (by linarith) (by linarith)))
  have hBD : B ⊆ D := Finset.image_subset_image
    (diskFinset_mono _ _ (by linarith) (by nlinarith))
  have hKD : K ⊆ D := hKB.trans hBD
  have hzD : z ∈ D := by
    simp only [D, mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq]
    have hs := Real.sq_sqrt (normSq_nonneg (z - b))
    have hn := Real.sqrt_nonneg (normSq (z - b))
    have hupper : Real.sqrt (normSq (z - b)) < Real.exp 1 * m + H := by nlinarith [hz.2]
    nlinarith
  have hzB : z ∉ B := by
    simp only [B, mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq, not_lt]
    have hs := Real.sq_sqrt (normSq_nonneg (z - b))
    nlinarith [hz.1]
  have hzK : z ∉ K := fun h ↦ hzB (hKB h)
  have hzA : z ∉ A := fun h ↦ hzB (Finset.mem_sdiff.mp h).1
  have hAD : A ⊆ D \ K := by
    intro y hy
    exact Finset.mem_sdiff.mpr ⟨hBD (Finset.mem_sdiff.mp hy).1, (Finset.mem_sdiff.mp hy).2⟩
  let α := (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))
  let δ := W * (a + 1) / m * Real.log (m / a)
  have hb : ∀ y ∈ domainExitBoundary A,
      |killedGreen (D \ K) y z - α * (1 - setHitProbability D K y)| ≤
        δ * (1 - setHitProbability D K y) := by
    intro y hy
    by_cases hyK : y ∈ K
    · have hn : y ∉ D \ K := fun h ↦ (Finset.mem_sdiff.mp h).2 hyK
      simp only [killedGreen_zero_of_not_mem _ y z hn,
        setHitProbability_one D K y (hKD hyK) hyK, sub_self, mul_zero, abs_zero, le_refl]
    · have hyB := punctured_boundary_outside_target B K y hy hyK
      have hr := translated_disk_boundary_radial b (3 * a / 2) (by linarith) y hyB
      exact hh m H a hm ha hH hHm hsep b z y K hK hz hr
  exact entrance_atom_comparison_from_boundary D K A hKD hAD z v
    (Finset.mem_sdiff.mpr ⟨hzD, hzK⟩) hzA hv
    (fun d ↦ hBD (inner_disk_neighbor_mem_intermediate b v a ha2 (hK hv) d))
    (fun y hy hin ↦ incoming_neighbor_mem_local_puncture D K b v y a ha2 hK hv hy hin)
    α δ hb

end SRWTightness
