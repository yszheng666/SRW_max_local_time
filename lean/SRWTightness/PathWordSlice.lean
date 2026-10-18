import SRWTightness.ChildShiftedOccupation

namespace SRWTightness

/-- The direction word between two times, for recursive child extraction. -/
def slicePathWord (w : PathWord) (a b : ℕ) : PathWord :=
  ⟨b - a, fun k ↦ wordPath w (a + k)⟩

theorem slicePathWord_position (w : PathWord) (a b i : ℕ) (hi : i ≤ b - a) :
    position (wordPath (slicePathWord w a b)) i = position (shift a (wordPath w)) i := by
  apply position_congr
  intro k hk
  simp [wordPath, slicePathWord, extendWord, shift, hk.trans_le hi]

theorem slicePathWord_localTime (w : PathWord) (a b : ℕ) (y : Site) :
    localTime (wordPath (slicePathWord w a b)) (b - a) y =
      localTime (shift a (wordPath w)) (b - a) y := by
  apply localTime_congr
  intro k hk
  simp [wordPath, slicePathWord, extendWord, shift, hk]

/-- A child sliced from the actual parent word has the same occupation as the original path segment. -/
theorem slice_killedPathWord_localTime (D : Finset Site) (x : Site) (ω : Sample)
    (a b : ℕ) (hb : b ≤ domainSteps D x ω) (y : Site) :
    localTime (wordPath (slicePathWord (killedPathWord D x ω) a b)) (b - a) y =
      localTime (shift a ω) (b - a) y := by
  rw [slicePathWord_localTime]
  apply localTime_congr
  intro k hk
  have hk' : a + k < domainSteps D x ω := by omega
  simp [shift, wordPath, killedPathWord, extendWord, hk']

/-- Single-level occupation partition expressed entirely through finite child words. -/
theorem domainLocalTime_child_words (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (x y : Site) (hy : y ∈ K) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    domainLocalTime D x y ω =
      ∑ q ∈ (killedChildIntervals D K C x ω).toFinset,
        localTime (wordPath (slicePathWord (killedPathWord D x ω) q.1 q.2)) (q.2 - q.1)
          (y - (x + position ω q.1)) := by
  rw [domainLocalTime_shifted_children D K C hKC hCD x y hy ω hfin]
  apply Finset.sum_congr rfl
  intro q hq
  have ht := wordChildIntervals_endpoint_le K C x (killedPathWord D x ω) q
    (List.mem_toFinset.mp hq)
  exact (slice_killedPathWord_localTime D x ω q.1 q.2 ht.2 _).symm

end SRWTightness
