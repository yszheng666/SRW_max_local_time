import SRWTightness.GreenPositive
import SRWTightness.GreenSymmetry

open Matrix

namespace SRWTightness

noncomputable def domainRestrictionMatrix (D E : Finset Site) (hED : E ⊆ D) : Matrix E D ℝ :=
  fun x y ↦ if (⟨x, hED x.property⟩ : D) = y then 1 else 0

theorem domainRestriction_mul {κ : Type*} (D E : Finset Site) (hED : E ⊆ D)
    (N : Matrix D κ ℝ) (x : E) (y : κ) :
    (domainRestrictionMatrix D E hED * N) x y = N ⟨x, hED x.property⟩ y := by
  simp [Matrix.mul_apply, domainRestrictionMatrix]

theorem mul_domainRestriction_transpose {κ : Type*} (D E : Finset Site) (hED : E ⊆ D)
    (N : Matrix κ D ℝ) (x : κ) (y : E) :
    (N * (domainRestrictionMatrix D E hED)ᵀ) x y = N x ⟨y, hED y.property⟩ := by
  simp [Matrix.mul_apply, domainRestrictionMatrix, Matrix.transpose_apply]

theorem domainRestriction_compress (D E : Finset Site) (hED : E ⊆ D)
    (N : Matrix D D ℝ) :
    domainRestrictionMatrix D E hED * N * (domainRestrictionMatrix D E hED)ᵀ =
      N.submatrix (fun x : E ↦ ⟨x, hED x.property⟩) (fun x : E ↦ ⟨x, hED x.property⟩) := by
  ext x y
  rw [mul_domainRestriction_transpose, domainRestriction_mul]
  rfl

theorem domainRestriction_orthonormal (D E : Finset Site) (hED : E ⊆ D) :
    domainRestrictionMatrix D E hED * (domainRestrictionMatrix D E hED)ᵀ = 1 := by
  ext x y
  rw [domainRestriction_mul]
  simp only [Matrix.transpose_apply, domainRestrictionMatrix, Matrix.one_apply]
  congr 1
  apply propext
  exact ⟨fun h ↦ Subtype.ext (congrArg Subtype.val h).symm,
    fun h ↦ by subst y; rfl⟩

theorem domainRestriction_precision (D E : Finset Site) (hED : E ⊆ D) :
    domainRestrictionMatrix D E hED * (1 - killedTransition D) *
      (domainRestrictionMatrix D E hED)ᵀ = 1 - killedTransition E := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, domainRestriction_orthonormal,
    domainRestriction_compress]
  rfl

end SRWTightness
