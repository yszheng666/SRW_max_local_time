import SRWTightness.BufferedLongRecordEstimate

namespace SRWTightness

/-- Constant records retain exactly the actual number of complete short roots. -/
theorem killed_child_records_unit_event (D K C : Finset Site) (x : Site) (k : ℕ) :
    {ω | killedChildRecords D K C x (fun _ _ ↦ ()) ω = () :: List.replicate k ()} =
      {ω | (killedChildIntervals D K C x ω).length = k + 1} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [← List.replicate_succ, List.eq_replicate_iff, killedChildRecords_length]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, fun u _ ↦ Subsingleton.elim u ()⟩

/-- Integrating out all fine records gives the geometric root-count law with no fine-record error. -/
theorem buffered_long_root_count (hP : PotentialKernelAsymptoticInput) :
    ∃ C T : ℝ, 0 < C ∧ 2 ≤ T ∧ ∀ ρ H J : ℝ, 1 ≤ H → 8 * H ≤ ρ →
      T * (H + 1) ≤ ρ - H → 3 ≤ J → ∀ b x : Site,
      x ∈ translateFinset b (diskFinset (ρ - H)) →
      ρ - H - 1 ≤ Real.sqrt (normSq (x - b)) → Real.sqrt (normSq (x - b)) ≤ ρ - H →
      ∀ k : ℕ,
      let p := bufferedLongEscapeParameter ρ H J
      let E := C * (H + 1) / (ρ - H) * ((k : ℝ) + 1)
      let event := {ω | (killedChildIntervals
        (translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H)))
        (translateFinset b (diskFinset (ρ - H)))
        (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) x ω).length = k + 1}
      Real.exp (-E) * (p * (1 - p) ^ k) ≤ pathLaw.real event ∧
        pathLaw.real event ≤ Real.exp E * (p * (1 - p) ^ k) := by
  obtain ⟨C, T, hC, hT, hh⟩ := buffered_long_record_estimate hP
  refine ⟨C, T, hC, hT, ?_⟩
  intro ρ H J hH hρ hlarge hJ b x hx hxlo hxhi k
  have hf : ∀ z : Site, ρ - H - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ ρ - H → ∀ u : Unit,
      Real.exp (-(0 : ℝ)) * 1 ≤ pathLaw.real {ω |
        (fun (_ : Site) (_ : PathWord) ↦ ()) z
          (killedPathWord (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) z ω) = u} ∧
      pathLaw.real {ω | (fun (_ : Site) (_ : PathWord) ↦ ()) z
        (killedPathWord (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) z ω) = u} ≤
        Real.exp (0 : ℝ) * 1 := by
    intro z _ _ u
    cases u
    simp
  have hb := hh ρ H J hH hρ hlarge hJ Unit b (fun _ _ ↦ ()) (fun _ ↦ 0) (fun _ ↦ 1)
    (fun _ ↦ by norm_num) hf x hx hxlo hxhi () (List.replicate k ())
  dsimp only at hb ⊢
  rw [killed_child_records_unit_event] at hb
  simpa using hb

end SRWTightness
