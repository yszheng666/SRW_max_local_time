import SRWTightness.ConvexOuterGradient

namespace SRWTightness

/-- Centers whose entire closed ball of the prescribed radius lies in the set. -/
def convexErosion {E : Type*} [NormedAddCommGroup E] (K : Set E) (ε : ℝ) : Set E :=
  {x | ∀ v : E, ‖v‖ ≤ ε → x + v ∈ K}

theorem convexErosion_subset {E : Type*} [NormedAddCommGroup E]
    (K : Set E) (ε : ℝ) (hε : 0 ≤ ε) : convexErosion K ε ⊆ K := by
  intro x hx
  simpa using hx 0 (by simpa using hε)

theorem convexErosion_convex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : Set E) (hK : Convex ℝ K) (ε : ℝ) :
    Convex ℝ (convexErosion K ε) := by
  intro x hx y hy a b ha hb hab v hv
  have hh := hK (hx v hv) (hy v hv) ha hb hab
  have he : a • (x + v) + b • (y + v) = (a • x + b • y) + v := by
    rw [smul_add, smul_add]
    calc
      _ = (a • x + b • y) + (a • v + b • v) := by abel
      _ = _ := by rw [← add_smul, hab, one_smul]
  rwa [he] at hh

theorem convexErosion_isClosed {E : Type*} [NormedAddCommGroup E]
    (K : Set E) (hK : IsClosed K) (ε : ℝ) : IsClosed (convexErosion K ε) := by
  have he : convexErosion K ε = ⋂ (v : E) (_ : ‖v‖ ≤ ε),
      (fun x ↦ x + v) ⁻¹' K := by
    ext x
    simp [convexErosion]
  rw [he]
  exact isClosed_iInter (fun v ↦ isClosed_iInter (fun _ ↦
    hK.preimage (continuous_id.add continuous_const)))

theorem convexErosion_isComplete {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (K : Set E) (hK : IsClosed K) (ε : ℝ) : IsComplete (convexErosion K ε) :=
  (convexErosion_isClosed K hK ε).isComplete

/-- Every point closer than the erosion radius to an eroded center belongs to the original set. -/
theorem convexErosion_near_mem {E : Type*} [NormedAddCommGroup E]
    (K : Set E) (ε : ℝ) (p x : E) (hp : p ∈ convexErosion K ε)
    (hx : ‖x - p‖ ≤ ε) : x ∈ K := by
  simpa only [add_sub_cancel] using hp (x - p) hx

end SRWTightness
