import SRWTightness.RadialForestReferenceUpper
import SRWTightness.RootOuterDomainGeometry
import SRWTightness.DiskCapacityLogBound

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Disk-killed forests started at the origin have no separate support assumptions. -/
theorem disk_forest_reference_upper {M : Type*} [Countable M]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace (List M)] [MeasurableSingletonClass (List M)]
    (R : ℝ) (b : Site) (a c : ℝ) (ha : 1 ≤ a) (hac : a ≤ c)
    (hfit : Real.sqrt (normSq b) + c + 1 < R) (hout : a ≤ Real.sqrt (normSq b))
    (F : Site → PathWord → M) (ρ : ℝ) (hρ : 0 ≤ ρ) (η : M → ℝ)
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hp : ∀ y : Site, c ≤ Real.sqrt (normSq (y - b)) →
      Real.sqrt (normSq (y - b)) ≤ c + 1 →
      setHitProbability (diskFinset R) (translateFinset b (diskFinset a)) y ≤ ρ)
    (hF : ∀ z : Site, a - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ a → ∀ r,
      pathLaw.real {ω | F z (killedPathWord (translateFinset b (diskFinset c)) z ω) = r} ≤
        Real.exp (η r) * μ.real {r})
    (j : ℕ) (hj : 1 ≤ j)
    (s : Set (List M)) (E : ℝ) (hlen : ∀ rs ∈ s, rs.length = j)
    (herr : ∀ rs ∈ s, (rs.map η).sum ≤ E) :
    pathLaw {ω | killedChildRecords (diskFinset R) (translateFinset b (diskFinset a))
      (translateFinset b (diskFinset c)) 0 F ω ∈ s} ≤
      ENNReal.ofReal (ρ ^ (j - 1) * Real.exp E) * independentForestLaw μ j s := by
  have hc : 0 ≤ c := by linarith
  have hR : 0 < R := by have hh := Real.sqrt_nonneg (normSq b); linarith
  have hd := root_domain_and_exit_inside b c R hc hfit
  have hKC : translateFinset b (diskFinset a) ⊆ translateFinset b (diskFinset c) := by
    intro y hy
    rw [mem_translateFinset_iff] at hy ⊢
    exact diskFinset_mono a c (by linarith) hac hy
  have hx : (0 : Site) ∈ diskFinset R \ translateFinset b (diskFinset a) := by
    apply Finset.mem_sdiff.mpr
    constructor
    · apply (mem_diskFinset R 0).mpr
      simpa [disk, normSq] using sq_pos_of_pos hR
    · intro hz
      have hz' : normSq b < a ^ 2 := by
        simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq,
          zero_sub, normSq_neg] using hz
      have hs := Real.sq_sqrt (normSq_nonneg b)
      have hn := Real.sqrt_nonneg (normSq b)
      nlinarith
  exact radial_forest_reference_upper (diskFinset R) b a c ha hc hKC hd.1 hd.2
    F ρ hρ η μ hp hF 0 hx j hj s E hlen herr

end SRWTightness
