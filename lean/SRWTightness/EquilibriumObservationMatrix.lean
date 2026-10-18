import SRWTightness.EquilibriumEnergyOrder

open MeasureTheory ProbabilityTheory

namespace SRWTightness

noncomputable def normalizedObservation {n : ℕ} (D A : Finset Site) (K : Fin n → Finset Site)
    (z : A) (k : ℕ) (α g u : ℝ) : Option (Fin n) → MarkSamples A k → ℝ
  | none => normalizedMarkSum A k α g u z
  | some i => normalizedEquilibriumAverage D A (K i) k α g u

noncomputable def observationEnergyTime {n : ℕ} (D : Finset Site) (K : Fin n → Finset Site)
    (z : Site) (α g : ℝ) : Option (Fin n) → ℝ
  | none => pointEnergyTime D z α g
  | some i => equilibriumEnergyTime D (K i) α g

noncomputable def observationDiscreteError {n : ℕ} (D : Finset Site) (K : Fin n → Finset Site)
    (g : ℝ) : Option (Fin n) → ℝ
  | none => 0
  | some i => equilibriumDiscreteError D (K i) g

/-- The exact Brownian-minimum covariance minus the discrete diagonal, for actual reference marks. -/
theorem normalizedObservation_covariance {n : ℕ} (D A : Finset Site) (K : Fin n → Finset Site)
    (hKA : ∀ i, K i ⊆ A) (hAD : A ⊆ D) (hmono : Monotone K)
    (hdis : ∀ i j, i ≠ j → ∀ x : Site, equilibriumWeight D (K i) x * equilibriumWeight D (K j) x = 0)
    (z : A) (hz : ∀ i, (z : Site) ∈ K i) (hzero : ∀ i, equilibriumWeight D (K i) z = 0)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D A ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) (i j : Option (Fin n)) :
    covariance (normalizedObservation D A K z k α g u i) (normalizedObservation D A K z k α g u j)
      (markProductLaw D A α k) =
      min (observationEnergyTime D K z α g i) (observationEnergyTime D K z α g j) -
        (if i = j then observationDiscreteError D K g i else 0) := by
  have ht (i : Fin n) : equilibriumEnergyTime D (K i) α g ≤ pointEnergyTime D z α g :=
    equilibriumEnergyTime_le_point D A (K i) (hKA i) hAD z (hz i) (hzero i)
      α g u hα hg hu hcap k hk
  have hc (i : Fin n) : covariance (normalizedMarkSum A k α g u z)
      (normalizedEquilibriumAverage D A (K i) k α g u) (markProductLaw D A α k) =
        equilibriumEnergyTime D (K i) α g := by
    rw [normalizedEquilibriumAverage_coordinate_covariance D A (K i) (hKA i) hAD z (hz i)
      α g u hα hg hu hcap k hk, hzero i, zero_div, sub_zero]
    rfl
  cases i with
  | none =>
    cases j with
    | none =>
      simp only [normalizedObservation, observationEnergyTime, observationDiscreteError, min_self, ite_true, sub_zero]
      rw [normalizedMarkSum_covariance D A hAD α g u hα hg hu hcap k hk]
      simp only [ite_true, pointEnergyTime]
      ring
    | some j =>
      simp only [normalizedObservation, observationEnergyTime, Option.noConfusion, ↓reduceIte, sub_zero]
      rw [hc j, min_eq_right (ht j)]
      simp
  | some i =>
    cases j with
    | none =>
      simp only [normalizedObservation, observationEnergyTime, Option.noConfusion, ↓reduceIte, sub_zero]
      rw [covariance_comm, hc i, min_eq_left (ht i)]
      simp
    | some j =>
      by_cases he : i = j
      · subst j
        simp only [normalizedObservation, observationEnergyTime, observationDiscreteError, min_self, ite_true]
        exact normalizedEquilibriumAverage_covariance_self D A (K i) (hKA i) hAD ⟨z, hz i⟩
          α g u hα hg hu hcap k hk
      · simp only [normalizedObservation, observationEnergyTime, Option.some.injEq, he, ↓reduceIte, sub_zero]
        by_cases hij : i ≤ j
        · exact normalizedEquilibriumAverage_covariance_min D A (K i) (K j) (hmono hij) (hKA j) hAD
            ⟨z, hz i⟩ (hdis i j he) α g u hα hg hu hcap k hk
        · rw [covariance_comm, min_comm]
          exact normalizedEquilibriumAverage_covariance_min D A (K j) (K i) (hmono (le_of_not_ge hij)) (hKA i) hAD
            ⟨z, hz j⟩ (hdis j i (Ne.symm he)) α g u hα hg hu hcap k hk

/-- Matrix form of the source identity Σ = K - E. -/
theorem normalizedObservation_covariance_matrix {n : ℕ} (D A : Finset Site) (K : Fin n → Finset Site)
    (hKA : ∀ i, K i ⊆ A) (hAD : A ⊆ D) (hmono : Monotone K)
    (hdis : ∀ i j, i ≠ j → ∀ x : Site, equilibriumWeight D (K i) x * equilibriumWeight D (K j) x = 0)
    (z : A) (hz : ∀ i, (z : Site) ∈ K i) (hzero : ∀ i, equilibriumWeight D (K i) z = 0)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D A ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    (Matrix.of fun i j : Option (Fin n) ↦ covariance (normalizedObservation D A K z k α g u i)
      (normalizedObservation D A K z k α g u j) (markProductLaw D A α k)) =
    (Matrix.of fun i j ↦ min (observationEnergyTime D K z α g i) (observationEnergyTime D K z α g j)) -
      Matrix.diagonal (observationDiscreteError D K g) := by
  ext i j
  change covariance (normalizedObservation D A K z k α g u i)
    (normalizedObservation D A K z k α g u j) (markProductLaw D A α k) =
    min (observationEnergyTime D K z α g i) (observationEnergyTime D K z α g j) -
      Matrix.diagonal (observationDiscreteError D K g) i j
  rw [normalizedObservation_covariance D A K hKA hAD hmono hdis z hz hzero α g u hα hg hu hcap k hk]
  simp only [Pi.sub_apply, Matrix.diagonal_apply]

end SRWTightness
