import SRWTightness.ExternalKilledTraceFactorization
import Mathlib.Data.List.OfFn

namespace SRWTightness

/-- The chronological visits to the observation set strictly before a deterministic horizon. -/
def visitTraceRange (K : Finset Site) (x : Site) (ω : Sample) (N : ℕ) : List Site :=
  ((List.range N).map (fun i ↦ x + position ω i)).filter (fun z ↦ z ∈ K)

/-- The original finite-word trace is exactly the range-indexed chronological visit list. -/
theorem word_visit_trace_eq_range (K : Finset Site) (x : Site) (w : PathWord) :
    wordVisitTrace K x w = visitTraceRange K x (wordPath w) w.length := by
  classical
  unfold wordVisitTrace visitTraceRange
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- The actual killed-word trace agrees with the actual walk up to its exit horizon. -/
theorem killed_visit_trace_eq_range (D K : Finset Site) (x : Site) (ω : Sample) :
    killedVisitTrace D K x ω = visitTraceRange K x ω (domainSteps D x ω) := by
  rw [killedVisitTrace, word_visit_trace_eq_range]
  unfold visitTraceRange
  change ((List.range (domainSteps D x ω)).map
    (fun i ↦ x + position (wordPath (killedPathWord D x ω)) i)).filter _ = _
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [killedPathWord_position D x ω i (List.mem_range.mp hi).le]

/-- Agreement of all inspected positions preserves the entire chronological trace. -/
theorem visit_trace_range_congr (K : Finset Site) (x : Site) (ω υ : Sample) (N : ℕ)
    (h : ∀ i < N, position ω i = position υ i) :
    visitTraceRange K x ω N = visitTraceRange K x υ N := by
  unfold visitTraceRange
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

/-- Cutting the time range gives its prefix followed by the shifted future trace. -/
theorem visit_trace_range_add (K : Finset Site) (x : Site) (ω : Sample) (n m : ℕ) :
    visitTraceRange K x ω (n + m) = visitTraceRange K x ω n ++
      visitTraceRange K (x + position ω n) (shift n ω) m := by
  unfold visitTraceRange
  rw [List.range_add, List.map_append, List.map_map, List.filter_append]
  congr 1
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, position_add, add_assoc]

/-- Inspecting one more time appends precisely that time's visit when it lies in the set. -/
theorem visit_trace_range_succ (K : Finset Site) (x : Site) (ω : Sample) (n : ℕ) :
    visitTraceRange K x ω (n + 1) = visitTraceRange K x ω n ++
      (if x + position ω n ∈ K then [x + position ω n] else []) := by
  by_cases h : x + position ω n ∈ K <;>
    simp [visitTraceRange, List.range_succ, List.filter_append, h]

/-- An empty chronological trace is exactly absence of visits at every inspected time. -/
theorem visit_trace_range_eq_nil_iff (K : Finset Site) (x : Site) (ω : Sample) (N : ℕ) :
    visitTraceRange K x ω N = [] ↔ ∀ i < N, x + position ω i ∉ K := by
  unfold visitTraceRange
  rw [List.filter_eq_nil_iff]
  constructor
  · intro h i hi
    simpa using h (x + position ω i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · intro h z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    simpa using h i (List.mem_range.mp hi)

end SRWTightness
