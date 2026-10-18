import SRWTightness.WordLongSegmentCount
import SRWTightness.ChildIntervalOrder
import SRWTightness.ExternalStoppedWordMass

namespace SRWTightness

/-- A complete child cannot start when the target is avoided at every preterminal time. -/
theorem word_child_records_empty_of_avoids {M : Type*} (K C : Finset Site)
    (x : Site) (w : PathWord) (F : Site → PathWord → M)
    (havoid : ∀ i < w.length, x + position (wordPath w) i ∉ K) :
    wordChildRecords K C x F w = [] := by
  have he : wordChildIntervals K C x w = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro q hq
    have hlt := scanChildIntervals_start_lt_end K C x (wordPath w) _
      List.pairwise_lt_range none (by intro a h; cases h) q hq
    have hend := (wordChildIntervals_endpoint_le K C x w q hq).2
    exact havoid q.1 (by omega) (wordChildIntervals_endpoints K C x w q hq).1
  simp only [wordChildRecords, he, List.map_nil]

/-- A word stopped in one component has no complete short roots in a disjoint component. -/
theorem admissible_word_opposite_records_empty {M : Type*}
    (D E K C : Finset Site) (hdisj : Disjoint D E) (hK : K ⊆ E)
    (x e : Site) (w : PathWord) (hw : AdmissibleExitWord D x e w)
    (F : Site → PathWord → M) : wordChildRecords K C x F w = [] := by
  apply word_child_records_empty_of_avoids K C x w F
  intro i hi hin
  exact Finset.disjoint_left.mp hdisj (hw.1 i hi) (hK hin)

/-- A component bridge started in its short target has a nonempty complete short-root list. -/
theorem admissible_word_own_records_nonempty {M : Type*}
    (K C D : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (x e : Site) (w : PathWord) (hx : x ∈ K) (hw : AdmissibleExitWord D x e w)
    (F : Site → PathWord → M) : wordChildRecords K C x F w ≠ [] := by
  apply word_child_records_nonempty K C hKC x w hx _ F
  rw [hw.2.1]
  exact fun h ↦ hw.2.2 (hCD h)

end SRWTightness
