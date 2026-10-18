import SRWTightness.CovarianceCompression
import SRWTightness.DomainRestrictionMatrix

open Matrix

namespace SRWTightness

noncomputable def harmonicRemainderMatrix (D E : Finset Site) (hED : E ⊆ D) : Matrix E D ℝ :=
  domainRestrictionMatrix D E hED -
    greenMatrix E * domainRestrictionMatrix D E hED * (1 - killedTransition D)

/-- The actual Green difference is the covariance of an explicit linear remainder. -/
theorem green_difference_covariance_factorization (D E : Finset Site) (hED : E ⊆ D) :
    harmonicRemainderMatrix D E hED * greenMatrix D * (harmonicRemainderMatrix D E hED)ᵀ =
      observationGreen D E - greenMatrix E := by
  have hQ : (1 - killedTransition D)ᵀ = 1 - killedTransition D := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, killedTransition_transpose]
  have hBC : greenMatrix E * (domainRestrictionMatrix D E hED * (1 - killedTransition D) *
      (domainRestrictionMatrix D E hED)ᵀ) = 1 := by
    rw [domainRestriction_precision]
    exact mul_eq_one_comm.mp (greenMatrix_right_inverse E)
  have he := covariance_compression_remainder (greenMatrix D) (1 - killedTransition D)
    (greenMatrix E) (domainRestrictionMatrix D E hED) hQ (greenMatrix_transpose E)
    (domainRestriction_orthonormal D E hED) (greenMatrix_right_inverse D) hBC
  rw [domainRestriction_compress] at he
  exact he

/-- Domain enlargement increases the actual Green kernel in the positive-semidefinite order. -/
theorem green_difference_posSemidef (D E : Finset Site) (hED : E ⊆ D) :
    (observationGreen D E - greenMatrix E).PosSemidef := by
  have hp := (greenMatrix_posDef D).posSemidef.mul_mul_conjTranspose_same
    (harmonicRemainderMatrix D E hED)
  have ht : (harmonicRemainderMatrix D E hED)ᴴ = (harmonicRemainderMatrix D E hED)ᵀ := by
    ext x y
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
  rw [ht, green_difference_covariance_factorization D E hED] at hp
  exact hp

end SRWTightness
