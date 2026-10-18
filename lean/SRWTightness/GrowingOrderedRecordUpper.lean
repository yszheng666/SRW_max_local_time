import SRWTightness.GrowingRecordDomains
import SRWTightness.ActualFiniteRecordKernel
import SRWTightness.SourceTerminalOrderedWordUpper
import SRWTightness.BufferedRecordUpper
import SRWTightness.FirstEntranceWordFunctionalLaw
import SRWTightness.SourceBufferedHalf

open MeasureTheory

namespace SRWTightness

/-- Ordered trees obey upper bounds without a terminal relative-error smallness condition. -/
theorem growing_ordered_record_probability_upper (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W T M : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 2 ≤ T ∧ 8 ≤ M ∧
      ∀ (b : Site) (m H a : ℝ) (K : Finset Site),
      1 ≤ H → 8 * H ≤ m → T ≤ m - H → M ≤ m →
      B * H / m ≤ 1 / 4 → 0 < a → 2 * a < m - H - 2 →
      K ⊆ translateFinset b (diskFinset a) →
      ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
        capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
      let η : WordMark → ℝ := fun _ ↦ W * (a + 1) / m * Real.log (m / a)
      let Q : WordMark → ℝ := fun v ↦
        (referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))).real {v}
      ∀ n x (r : FiniteExcursionRecord (WordMark) n),
      growingRecordRadius m n - H - 1 ≤ Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤ growingRecordRadius m n - H →
      pathLaw.real {ω | actualFiniteWordRecord (growingRecordEntrance b m H)
          (growingRecordExit b m H) (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n x
          (killedPathWord (growingRecordExit b m H n) x ω) = r} ≤
        Real.exp (finiteRecordError (fun j ↦ 4 * (B * H / growingRecordRadius m j)) η n r) *
          finiteRecordReferenceWeight Q n r := by
  obtain ⟨W, M, hW, hM, hmark⟩ := source_terminal_ordered_word_upper hinput
  obtain ⟨B, T, hB, hT, hhalf⟩ := source_buffered_half_probabilities hinput
  refine ⟨B, W, T, M, hB, hW, hT, hM, ?_⟩
  intro b m H a K hH hm hTm hMm hsmall ha hsep hK hcap
  dsimp only
  let η : WordMark → ℝ := fun _ ↦ W * (a + 1) / m * Real.log (m / a)
  let Q : WordMark → ℝ := fun v ↦
    (referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
      ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))).real {v}
  let δ : ℕ → ℝ := fun j ↦ 4 * (B * H / growingRecordRadius m j)
  have hm0 : 0 < m := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hQ : ∀ v, 0 ≤ Q v := fun _ ↦ measureReal_nonneg
  intro n
  induction n with
  | zero =>
    intro x v hxl hxu
    change WordMark at v
    simp only [growingRecordRadius_zero] at hxl hxu
    have hh := hmark m H a hMm ha hH0 (by linarith) hsep b x K hK
      ⟨hxl, by linarith⟩ hcap {v} (measurableSet_singleton (α := WordMark) v)
    rw [← firstEntranceWordOfWord_event _ K x {v} (measurableSet_singleton v)] at hh
    simp only [Set.mem_singleton_iff] at hh
    dsimp only [FiniteExcursionRecord]
    simpa only [growingRecordExit, growingRecordRadius_zero, finiteRecordError,
      finiteRecordReferenceWeight, actualFiniteWordRecord] using hh
  | succ n ih =>
    intro x rs hxl hxu
    change List (FiniteExcursionRecord WordMark n) at rs
    have hbase := growingRecordRadius_ge_base m hm0.le n
    have hρ : 8 * H ≤ growingRecordRadius m n := hm.trans hbase
    have hTρ : T ≤ growingRecordRadius m n - H := by linarith
    have hε : 0 ≤ B * H / growingRecordRadius m n :=
      div_nonneg (mul_nonneg hB hH0) (by linarith)
    have hεsmall : B * H / growingRecordRadius m n ≤ 1 / 4 :=
      (div_le_div_of_nonneg_left (mul_nonneg hB hH0) hm0 hbase).trans hsmall
    have hx : x ∈ bufferedRecordMiddle b (growingRecordRadius m n) H := by
      apply Or.inl
      rw [growingRecordRadius_succ] at hxl hxu
      exact ⟨hxl, hxu⟩
    have hh := buffered_record_probability_upper b (growingRecordRadius m n) H hH hρ
      (actualFiniteWordRecord (growingRecordEntrance b m H) (growingRecordExit b m H)
        (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n)
      (B * H / growingRecordRadius m n) hε hεsmall
      (fun z hz ↦ (hhalf _ H hH hρ hTρ b z hz).2)
      (finiteRecordError δ η n) (finiteRecordReferenceWeight Q n)
      (finiteRecordReferenceWeight_nonneg Q hQ n)
      (fun z hzl hzu v ↦ ih z v hzl hzu) rs x hx
    simp only [growingRecordExit_succ]
    exact hh

end SRWTightness
