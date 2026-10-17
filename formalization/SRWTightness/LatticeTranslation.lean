import SRWTightness.Capacity

open MeasureTheory

namespace SRWTightness

def translateFinset (b : Site) (D : Finset Site) : Finset Site := D.image (fun x ↦ b + x)

@[simp] theorem mem_translateFinset_add (b : Site) (D : Finset Site) (x : Site) :
    b + x ∈ translateFinset b D ↔ x ∈ D := by
  simp [translateFinset]

theorem mem_translateFinset_iff (b : Site) (D : Finset Site) (x : Site) :
    x ∈ translateFinset b D ↔ x - b ∈ D := by
  have h := mem_translateFinset_add b D (x - b)
  rwa [show b + (x - b) = x by abel] at h

theorem domainExit_translate (b : Site) (D : Finset Site) (x : Site) :
    domainExit (translateFinset b D) (b + x) = domainExit D x := by
  funext ω
  simp only [domainExit, hittingAfter, add_assoc, Set.mem_compl_iff, Finset.mem_coe, mem_translateFinset_add]
  congr 1
  simp [add_assoc]

theorem setHittingTime_translate (b : Site) (K : Finset Site) (x : Site) (n : ℕ) :
    setHittingTime (translateFinset b K) (b + x) n = setHittingTime K x n := by
  funext ω
  simp only [setHittingTime, hittingAfter, add_assoc, Finset.mem_coe, mem_translateFinset_add]
  congr 1
  simp [add_assoc]

theorem equilibriumMeasure_translate (b : Site) (D K : Finset Site) (x : Site) :
    equilibriumMeasure (translateFinset b D) (translateFinset b K) (b + x) = equilibriumMeasure D K x := by
  simp only [equilibriumMeasure, mem_translateFinset_add, domainExit_translate, setHittingTime_translate]

theorem capacity_translate (b : Site) (D K : Finset Site) :
    capacity (translateFinset b D) (translateFinset b K) = capacity D K := by
  unfold capacity
  conv_lhs => arg 1; rw [translateFinset]
  rw [Finset.sum_image]
  · simp only [equilibriumMeasure_translate]
  · intro x hx y hy he
    exact add_left_cancel he

end SRWTightness
