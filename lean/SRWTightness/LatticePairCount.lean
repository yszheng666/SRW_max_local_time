import SRWTightness.LatticeCloseNeighbors
import Mathlib.Data.Finset.Prod

namespace SRWTightness

/-- Standard planar lattice disk count, exposed as a foundational input. -/
def LatticeDiskCountInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → ((diskFinset r).card : ℝ) ≤ C * r ^ 2

/-- Ordered candidate pairs at closed distance at most a. -/
noncomputable def latticeNearbyPairs (Z : Finset Site) (a : ℝ) : Finset (Site × Site) := by
  classical
  exact (Z.product Z).filter (fun p ↦ Real.sqrt (normSq (p.2 - p.1)) ≤ a)

/-- Translation of the second endpoint injects nearby pairs into a candidate times a disk. -/
theorem lattice_nearby_pairs_card (Z : Finset Site) (a : ℝ) (ha : 1 ≤ a) :
    (latticeNearbyPairs Z a).card ≤ Z.card * (diskFinset (2 * a)).card := by
  classical
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun p : Site × Site ↦ (p.1, p.2 - p.1))
  · intro p hp
    obtain ⟨hpZ, hpdist⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_product.mpr ⟨(Finset.mem_product.mp hpZ).1, ?_⟩
    rw [mem_diskFinset]
    change normSq (p.2 - p.1) < (2 * a) ^ 2
    have hs := Real.sq_sqrt (normSq_nonneg (p.2 - p.1))
    have hn := Real.sqrt_nonneg (normSq (p.2 - p.1))
    nlinarith
  · intro p hp q hq he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp only at h1 h2
    apply Prod.ext h1
    rw [h1] at h2
    have hh := congrArg (fun x : Site ↦ x + q.1) h2
    simpa only [sub_add_cancel] using hh

/-- The uniform spatial factor needed for every distance shell. -/
theorem lattice_nearby_pairs_quadratic (hCount : LatticeDiskCountInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : Finset Site) (a : ℝ), 1 ≤ a →
      ((latticeNearbyPairs Z a).card : ℝ) ≤ C * Z.card * a ^ 2 := by
  obtain ⟨C, hC, hcount⟩ := hCount
  refine ⟨4 * C, by positivity, ?_⟩
  intro Z a ha
  have hcard : ((latticeNearbyPairs Z a).card : ℝ) ≤
      (Z.card : ℝ) * (diskFinset (2 * a)).card := by
    exact_mod_cast lattice_nearby_pairs_card Z a ha
  have hd := hcount (2 * a) (by linarith)
  calc
    _ ≤ (Z.card : ℝ) * (diskFinset (2 * a)).card := hcard
    _ ≤ (Z.card : ℝ) * (C * (2 * a) ^ 2) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

end SRWTightness
