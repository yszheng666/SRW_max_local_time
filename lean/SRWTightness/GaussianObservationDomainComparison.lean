import SRWTightness.GaussianSelectedObservation
import SRWTightness.GaussianSelectedDomainMaximum

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Enlarging a killing domain costs at most two on any common observation set. -/
theorem gaussian_observation_domain_comparison (D K A : Finset Site)
    (hAK : A ⊆ K) (hKD : K ⊆ D) (J : Finset A) (t : ℝ) :
    (gaussianGreenLaw K A).real (upperExceedanceOn J t) ≤
      2 * (gaussianGreenLaw D A).real (upperExceedanceOn J t) := by
  classical
  let f : A ↪ K := ⟨fun x ↦ ⟨x.val, hAK x.property⟩, by
    intro x y h
    exact Subtype.ext (congrArg (fun z : K ↦ z.val) h)⟩
  have he : {φ : EuclideanSpace ℝ K | ∃ x ∈ J, t ≤ φ ⟨x.val, hAK x.property⟩} =
      upperExceedanceOn (J.map f) t := by
    ext φ
    constructor
    · rintro ⟨x, hx, ht⟩
      exact ⟨f x, Finset.mem_map.mpr ⟨x, hx, rfl⟩, ht⟩
    · rintro ⟨y, hy, ht⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      exact ⟨x, hx, ht⟩
  rw [gaussian_selected_observation_probability K A K hAK (Finset.Subset.refl K) J t,
    gaussian_selected_observation_probability D A K hAK hKD J t, he]
  exact gaussian_selected_maximum_domain_comparison D K hKD (J.map f) t

/-- The common-observation comparison with a positive field normalization. -/
theorem gaussian_normalized_observation_domain_comparison (D K A : Finset Site)
    (hAK : A ⊆ K) (hKD : K ⊆ D) (J : Finset A) (σ t : ℝ) (hσ : 0 < σ) :
    (gaussianGreenLaw K A).real {φ | ∃ x ∈ J, t ≤ φ x / σ} ≤
      2 * (gaussianGreenLaw D A).real {φ | ∃ x ∈ J, t ≤ φ x / σ} := by
  have he : {φ : EuclideanSpace ℝ A | ∃ x ∈ J, t ≤ φ x / σ} =
      upperExceedanceOn J (t * σ) := by
    ext φ
    simp only [upperExceedanceOn, Set.mem_setOf_eq, le_div_iff₀ hσ]
  rw [he]
  exact gaussian_observation_domain_comparison D K A hAK hKD J (t * σ)

end SRWTightness
