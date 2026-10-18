import SRWTightness.DiskObservationIndex

namespace SRWTightness

/-- Probability weights for the actual equilibrium averages and the center coordinate. -/
noncomputable def observationWeight {n : ℕ} (D M : Finset Site)
    (K : Fin n → Finset Site) (z : M) : Option (Fin n) → M → ℝ
  | none => fun x ↦ if x = z then 1 else 0
  | some i => fun x ↦ equilibriumWeight D (K i) x

theorem observationWeight_nonneg {n : ℕ} (D M : Finset Site)
    (K : Fin n → Finset Site) (z : M) (i : Option (Fin n)) (x : M) :
    0 ≤ observationWeight D M K z i x := by
  cases i with
  | none => simp only [observationWeight]; split <;> norm_num
  | some i => exact equilibriumWeight_nonneg D (K i) x

theorem observationWeight_sum {n : ℕ} (D M : Finset Site)
    (K : Fin n → Finset Site) (z : M) (hKM : ∀ i, K i ⊆ M) (hMD : M ⊆ D)
    (hne : ∀ i, (K i).Nonempty) (i : Option (Fin n)) :
    ∑ x : M, observationWeight D M K z i x = 1 := by
  classical
  cases i with
  | none => simp [observationWeight]
  | some i =>
    simpa only [observationWeight, Finset.sum_coe_sort] using
      equilibriumWeight_sum_over D M (K i) (hKM i) ((hKM i).trans hMD) (hne i)

/-- Weighted coordinates in the normal approximation are exactly the original observations. -/
theorem normalizedWeightedSum_observationWeight {n : ℕ} (D M : Finset Site)
    (K : Fin n → Finset Site) (z : M) (k : ℕ) (α g u : ℝ) (i : Option (Fin n)) :
    normalizedWeightedSum M k α g u (observationWeight D M K z i) =
      normalizedObservation D M K z k α g u i := by
  classical
  cases i with
  | none => funext Y; simp [observationWeight, normalizedWeightedSum, normalizedObservation]
  | some i => rfl

/-- Actual source ordering of the probability weights. -/
noncomputable def orderedObservationWeight {n : ℕ} (D M : Finset Site)
    (K : Fin n → Finset Site) (z : M) (i : Fin (n + 1)) : M → ℝ :=
  observationWeight D M K z (diskObservationIndex n i)

@[simp] theorem orderedObservationWeight_last {n : ℕ} (D M : Finset Site)
    (K : Fin n → Finset Site) (z : M) (x : M) :
    orderedObservationWeight D M K z (Fin.last n) x = if x = z then 1 else 0 := by
  simp [orderedObservationWeight, observationWeight]

theorem orderedObservationWeight_probability {n : ℕ} (D M : Finset Site)
    (K : Fin n → Finset Site) (z : M) (hKM : ∀ i, K i ⊆ M) (hMD : M ⊆ D)
    (hne : ∀ i, (K i).Nonempty) :
    (∀ i x, 0 ≤ orderedObservationWeight D M K z i x) ∧
      ∀ i, ∑ x : M, orderedObservationWeight D M K z i x = 1 := by
  exact ⟨fun i x ↦ observationWeight_nonneg D M K z _ x,
    fun i ↦ observationWeight_sum D M K z hKM hMD hne _⟩

end SRWTightness
