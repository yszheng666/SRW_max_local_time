import SRWTightness.PathWordSlice
import Mathlib.Data.List.OfFn

namespace SRWTightness

/-- The finite direction list carried by a path word. -/
def pathWordDirections (w : PathWord) : List Direction := List.ofFn w.directions

/-- Package a finite direction list as the original length-indexed path word. -/
def pathWordOfDirections (ds : List Direction) : PathWord :=
  ⟨ds.length, fun i ↦ ds[i.val]⟩

/-- Direction-list packaging loses no increment. -/
theorem pathWordDirections_ofDirections (ds : List Direction) :
    pathWordDirections (pathWordOfDirections ds) = ds := by
  exact List.ofFn_getElem

/-- Extracting and repackaging directions preserves the entire path word. -/
theorem pathWordOfDirections_directions (w : PathWord) :
    pathWordOfDirections (pathWordDirections w) = w := by
  rcases w with ⟨n, ds⟩
  unfold pathWordOfDirections pathWordDirections
  congr 1
  · exact List.length_ofFn
  · apply (Fin.heq_fun_iff (by simp)).mpr
    intro i
    simp only [List.getElem_ofFn]

/-- Direction lists distinguish the complete original finite path words. -/
theorem pathWordDirections_injective : Function.Injective pathWordDirections := by
  intro u v he
  rw [← pathWordOfDirections_directions u, ← pathWordOfDirections_directions v, he]

/-- Chronological concatenation of two finite direction words. -/
def pathWordAppend (u v : PathWord) : PathWord :=
  pathWordOfDirections (pathWordDirections u ++ pathWordDirections v)

/-- Concatenation keeps the exact concatenated direction lists. -/
theorem pathWordDirections_append (u v : PathWord) :
    pathWordDirections (pathWordAppend u v) = pathWordDirections u ++ pathWordDirections v :=
  pathWordDirections_ofDirections _

/-- The concatenated word has the sum of the two original lengths. -/
theorem pathWordAppend_length (u v : PathWord) :
    (pathWordAppend u v).length = u.length + v.length := by
  simp [pathWordAppend, pathWordOfDirections, pathWordDirections]

end SRWTightness
