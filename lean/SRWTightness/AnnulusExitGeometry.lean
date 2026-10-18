import SRWTightness.AnnulusBarrierProbability

namespace SRWTightness

theorem mem_annulusFinset (a R : ℝ) (z : Site) :
    z ∈ annulusFinset a R ↔ normSq z < R ^ 2 ∧ a ^ 2 ≤ normSq z := by
  simp only [annulusFinset, Finset.mem_sdiff, mem_diskFinset, disk, Set.mem_setOf_eq, not_lt]

theorem annulusExitRange_normSq_lower (a R : ℝ) (ha : 1 ≤ a) (x : Site)
    (hx : a ^ 2 ≤ normSq x) (y : Site) (hy : y ∈ domainExitRange (annulusFinset a R) x) :
    (a - 1) ^ 2 ≤ normSq y := by
  rcases Finset.mem_insert.mp hy with he | hy
  · rw [he]
    nlinarith
  · obtain ⟨z, hz, hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hy
    exact normSq_step_lower z d a ha ((mem_annulusFinset a R z).mp hz).2

theorem annulusExitRange_normSq_upper (a R : ℝ) (hR : 0 ≤ R) (x : Site)
    (hx : normSq x ≤ R ^ 2) (y : Site) (hy : y ∈ domainExitRange (annulusFinset a R) x) :
    normSq y ≤ (R + 1) ^ 2 := by
  rcases Finset.mem_insert.mp hy with he | hy
  · rw [he]
    nlinarith
  · obtain ⟨z, hz, hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hy
    exact normSq_step_le z d hR ((mem_annulusFinset a R z).mp hz).1.le

end SRWTightness
