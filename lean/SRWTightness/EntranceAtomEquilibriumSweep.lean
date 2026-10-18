import SRWTightness.EquilibriumSweep
import SRWTightness.EntranceAtomGreen
import SRWTightness.Capacity

open MeasureTheory
namespace SRWTightness

/-- Sweeping an entrance atom over an enclosing equilibrium measure recovers its own charge. -/
theorem entrance_atom_equilibrium_sweep (D K L : Finset Site)
    (hKL : K ⊆ L) (hLD : L ⊆ D) (v : Site) (hv : v ∈ K) :
    (∑ x ∈ L, equilibriumMeasure D L x * (competingEntranceLaw D K x).real {v}) =
      equilibriumMeasure D K v := by
  classical
  have h := equilibrium_sweep D K L hKL hLD
    (fun x ↦ (competingEntranceLaw D K x).real {v}) ?_ ?_
  · rw [h]
    have he (x : Site) (hx : x ∈ K) :
        (competingEntranceLaw D K x).real {v} = if x = v then 1 else 0 := by
      rw [competingEntranceLaw_atom_payoff D K x v hv,
        exitPayoff_eq_of_not_mem (D \ K) _ x (by simp [hx])]
    simp_rw [Finset.sum_congr rfl (fun x hx ↦ congrArg
      (fun t : ℝ ↦ equilibriumMeasure D K x * t) (he x hx))]
    simp [hv]
  · intro x hx
    rw [competingEntranceLaw_atom_payoff D K x v hv,
      exitPayoff_eq_of_not_mem (D \ K) _ x (by simp [hx])]
    have hxv : x ≠ v := fun he ↦ hx (he ▸ hLD (hKL hv))
    simp [hxv]
  · intro x hx hxK
    simp_rw [competingEntranceLaw_atom_payoff D K _ v hv]
    exact exitPayoff_first_step (D \ K) (fun y ↦ if y = v then 1 else 0) x
      (Finset.mem_sdiff.mpr ⟨hx, hxK⟩)

/-- Uniform comparisons on the equilibrium support control each entrance atom by capacity. -/
theorem entrance_atom_sweep_bounds (D K L : Finset Site)
    (hKL : K ⊆ L) (hLD : L ⊆ D) (z v : Site) (hv : v ∈ K) (c C : ℝ)
    (hb : ∀ x ∈ L, equilibriumMeasure D L x ≠ 0 →
      c * (competingEntranceLaw D K z).real {v} ≤
          (competingEntranceLaw D K x).real {v} ∧
        (competingEntranceLaw D K x).real {v} ≤
          C * (competingEntranceLaw D K z).real {v}) :
    c * capacity D L * (competingEntranceLaw D K z).real {v} ≤
        equilibriumMeasure D K v ∧
      equilibriumMeasure D K v ≤
        C * capacity D L * (competingEntranceLaw D K z).real {v} := by
  rw [← entrance_atom_equilibrium_sweep D K L hKL hLD v hv]
  have hpoint (x : Site) (hx : x ∈ L) :
      equilibriumMeasure D L x * (c * (competingEntranceLaw D K z).real {v}) ≤
          equilibriumMeasure D L x * (competingEntranceLaw D K x).real {v} ∧
        equilibriumMeasure D L x * (competingEntranceLaw D K x).real {v} ≤
          equilibriumMeasure D L x * (C * (competingEntranceLaw D K z).real {v}) := by
    by_cases he : equilibriumMeasure D L x = 0
    · simp [he]
    · exact ⟨mul_le_mul_of_nonneg_left (hb x hx he).1 (equilibriumMeasure_nonneg _ _ _),
        mul_le_mul_of_nonneg_left (hb x hx he).2 (equilibriumMeasure_nonneg _ _ _)⟩
  have hl := Finset.sum_le_sum (fun x hx ↦ (hpoint x hx).1)
  have hu := Finset.sum_le_sum (fun x hx ↦ (hpoint x hx).2)
  rw [← Finset.sum_mul] at hl hu
  constructor
  · simpa only [capacity, mul_assoc, mul_left_comm, mul_comm] using hl
  · simpa only [capacity, mul_assoc, mul_left_comm, mul_comm] using hu

end SRWTightness
