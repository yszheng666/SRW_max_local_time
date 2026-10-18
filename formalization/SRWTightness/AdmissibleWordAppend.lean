import SRWTightness.PathWordAppendPositions
import SRWTightness.ExternalStoppedWordMass

namespace SRWTightness

/-- A retained interior prefix followed by an admissible exit word is itself admissible. -/
theorem admissibleExitWord_append (D : Finset Site) (x y e : Site) (u v : PathWord)
    (hpre : ∀ i < u.length, x + position (wordPath u) i ∈ D)
    (hy : x + position (wordPath u) u.length = y)
    (hv : AdmissibleExitWord D y e v) :
    AdmissibleExitWord D x e (pathWordAppend u v) := by
  refine ⟨?_, ?_, hv.2.2⟩
  · intro i hi
    rw [pathWordAppend_length] at hi
    by_cases hu : i < u.length
    · rw [pathWordAppend_position_left u v i hu.le]
      exact hpre i hu
    · have he : i = u.length + (i - u.length) := by omega
      have hj : i - u.length < v.length := by omega
      rw [he, pathWordAppend_position_right u v _ hj.le, ← add_assoc, hy]
      exact hv.1 _ hj
  · rw [pathWordAppend_length, pathWordAppend_position_right u v v.length le_rfl,
      ← add_assoc, hy]
    exact hv.2.1

end SRWTightness
