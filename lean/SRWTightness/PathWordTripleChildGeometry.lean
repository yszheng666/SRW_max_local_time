import SRWTightness.PathWordTriplePositions
import SRWTightness.AdmissibleWordPositiveLength

namespace SRWTightness

/-- A legal inserted exit word is precisely the first complete child after its exterior prefix. -/
theorem pathWordTriple_child_geometry (K C : Finset Site) (hKC : K ⊆ C)
    (x a e : Site) (p u v : PathWord)
    (hpre : ∀ i < p.length, x + position (wordPath p) i ∉ K)
    (hp : x + position (wordPath p) p.length = a) (ha : a ∈ K)
    (hu : AdmissibleExitWord C a e u) :
    let w := pathWordAppend p (pathWordAppend u v)
    p.length < p.length + u.length ∧ p.length + u.length ≤ w.length ∧
      (∀ i < p.length, x + position (wordPath w) i ∉ K) ∧
      x + position (wordPath w) p.length = a ∧
      (∀ i, p.length < i → i < p.length + u.length →
        x + position (wordPath w) i ∈ C) ∧
      x + position (wordPath w) (p.length + u.length) = e := by
  intro w
  have huPos := admissibleExitWord_length_pos C a e u (hKC ha) hu
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [w]
    rw [pathWordAppend_length, pathWordAppend_length]
    omega
  · intro i hi
    rw [pathWordAppend_position_left p (pathWordAppend u v) i hi.le]
    exact hpre i hi
  · rw [pathWordAppend_position_left p (pathWordAppend u v) p.length le_rfl]
    exact hp
  · intro i hai hib
    have he : i = p.length + (i - p.length) := by omega
    have hj : i - p.length < u.length := by omega
    rw [he, pathWordAppend_position_middle p u v _ hj.le, ← add_assoc, hp]
    exact hu.1 _ hj
  · rw [pathWordAppend_position_middle p u v u.length le_rfl, ← add_assoc, hp]
    exact hu.2.1

end SRWTightness
