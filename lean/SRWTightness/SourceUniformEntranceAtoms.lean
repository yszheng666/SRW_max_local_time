import SRWTightness.SourceEntranceBoundaryHarnack
import SRWTightness.TranslatedEquilibriumRadialSupport
import SRWTightness.EntranceAtomEquilibriumSweep
import SRWTightness.BufferedCapacityNormalization
import SRWTightness.NormalizedSweepBounds

open MeasureTheory
namespace SRWTightness

/-- Actual positive entrance atoms have uniform two-sided comparison with the reference charge. -/
theorem source_uniform_entrance_atoms (hP : PotentialKernelAsymptoticInput)
    (hHarm : PositiveHarmonicRelativeInput) :
    ∃ c U T : ℝ, 0 < c ∧ 0 < U ∧ 128 ≤ T ∧ ∀ (m H a : ℝ), T ≤ m →
      0 ≤ H → H ≤ m / 8 → 0 ≤ a → a ≤ m / 2 →
      ∀ (b : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
      ∀ z : Site, m - H - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ m - H + 1 → ∀ v ∈ K,
      let D := translateFinset b (diskFinset (Real.exp 1 * m + H))
      let α := (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))
      c * (α * equilibriumMeasure D K v) ≤ (competingEntranceLaw D K z).real {v} ∧
        (competingEntranceLaw D K z).real {v} ≤ U * (α * equilibriumMeasure D K v) := by
  obtain ⟨C, T₁, hC, hT₁, hh⟩ := source_entrance_boundary_harnack hHarm
  obtain ⟨T₂, hT₂, hc⟩ := buffered_capacity_normalization hP
  refine ⟨Real.exp (-C) / 2, 2 * Real.exp C, max T₁ T₂, by positivity, by positivity,
    hT₁.trans (le_max_left _ _), ?_⟩
  intro m H a hm hH hHm ha ham b K hK z hzlo hzhi v hv
  have hT₁m : T₁ ≤ m := (le_max_left _ _).trans hm
  have hT₂m : T₂ ≤ m := (le_max_right _ _).trans hm
  have hm128 : 128 ≤ m := hT₁.trans hT₁m
  have hm0 : 0 < m := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hrad : m - H ≤ Real.exp 1 * m + H := by nlinarith
  let D := translateFinset b (diskFinset (Real.exp 1 * m + H))
  let L := translateFinset b (diskFinset (m - H))
  let α := (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))
  have hKL : K ⊆ L := hK.trans (Finset.image_subset_image
    (diskFinset_mono a (m - H) ha (by linarith)))
  have hLD : L ⊆ D := Finset.image_subset_image
    (diskFinset_mono (m - H) (Real.exp 1 * m + H) (by linarith) hrad)
  have hs := entrance_atom_sweep_bounds D K L hKL hLD z v hv
    (Real.exp (-C)) (Real.exp C) (fun x hx hxcharge ↦ by
      have hr := translated_equilibrium_radial_support b (m - H)
        (Real.exp 1 * m + H) (by linarith) hrad x hx hxcharge
      exact hh m H a hT₁m hH hHm ha ham b K hK v hv z x hzlo hzhi
        hr.1 (by linarith [hr.2]))
  have hα : 0 ≤ α := by
    have h := source_terminal_alpha_lower m H hm0 hH (by linarith)
    exact (by positivity : 0 ≤ (2 / Real.pi : ℝ)).trans h
  exact normalized_sweep_bounds α (capacity D L) _ _ C hα measureReal_nonneg
    (hc m H hT₂m hH hHm b) hs

end SRWTightness
