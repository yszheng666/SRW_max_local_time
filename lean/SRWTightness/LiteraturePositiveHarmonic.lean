import SRWTightness.ExternalPositiveHarmonic
import SRWTightness.AxisChainOrientation
import SRWTightness.TranslatedDiskGeometry

namespace SRWTightness

/-- Lawler--Limic Theorem 6.3.8(b), (6.19), specialized to simple SRW and r=1.
The integer cutoff explicitly records "n sufficiently large" in the source.
Only the first-difference clause is needed. -/
def LLPositiveHarmonicDifferenceInput : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n →
    ∀ f : Site → ℝ, (∀ y, 0 ≤ f y) →
    (∀ y ∈ diskFinset (n : ℝ),
      f y = (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d)) →
    ∀ y : Site, normSq y ≤ 1 → |f y - f 0| ≤ c / n * f 0

private theorem unit_displacement_cases (z : Site) (hz : normSq z ≤ 1) :
    z = 0 ∨ ∃ d : Direction, z = step d := by
  have h1 := abs_fst_le_normSq_bound z (by norm_num : (0 : ℝ) ≤ 1) (by simpa using hz)
  have h2 := abs_snd_le_normSq_bound z (by norm_num : (0 : ℝ) ≤ 1) (by simpa using hz)
  have h1' : -1 ≤ z.1 ∧ z.1 ≤ 1 := by exact_mod_cast abs_le.mp h1
  have h2' : -1 ≤ z.2 ∧ z.2 ≤ 1 := by exact_mod_cast abs_le.mp h2
  rcases z with ⟨a,b⟩
  dsimp at h1' h2'
  obtain ⟨ha, ha'⟩ := h1'
  obtain ⟨hb, hb'⟩ := h2'
  interval_cases a <;> interval_cases b <;> norm_num [normSq] at hz
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr ⟨0, by decide⟩
    | exact Or.inr ⟨1, by decide⟩
    | exact Or.inr ⟨2, by decide⟩
    | exact Or.inr ⟨3, by decide⟩

private theorem harmonic_unit_bound (f : Site → ℝ) (hf : ∀ y, 0 ≤ f y) (v z : Site)
    (hv : f v = (1 / 4 : ℝ) * ∑ d : Direction, f (v + step d))
    (hz : normSq z ≤ 1) : |f (v + z) - f v| ≤ 3 * f v := by
  rcases unit_displacement_cases z hz with rfl | ⟨d, rfl⟩
  · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (hf v)
  · have hd : f (v + step d) ≤ ∑ e : Direction, f (v + step e) :=
      Finset.single_le_sum (f := fun e : Direction ↦ f (v + step e))
        (fun e _ ↦ hf _) (Finset.mem_univ d)
    rw [abs_le]
    constructor <;> nlinarith [hf (v + step d), hf v]

/-- A real-radius local estimate, including all bounded scales, derived from (6.19). -/
theorem ll_positive_harmonic_local (hLL : LLPositiveHarmonicDifferenceInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ B : ℝ, 8 ≤ B → ∀ f : Site → ℝ,
      (∀ y, 0 ≤ f y) →
      (∀ y ∈ diskFinset B, f y = (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d)) →
      ∀ v z : Site, normSq v ≤ (B / 2) ^ 2 → normSq z ≤ 1 →
        |f (v + z) - f v| ≤ K / B * f v := by
  obtain ⟨c, hc, N, hsource⟩ := hLL
  let K : ℝ := 4 * c + 6 * ((N : ℝ) + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro B hB f hf hh v z hv hz
  have hB0 : 0 < B := by linarith
  let n := ⌊B / 2⌋₊
  have hnle : (n : ℝ) ≤ B / 2 := Nat.floor_le (by positivity)
  have hnlt : B / 2 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast this.le
  have hnB : B / 4 ≤ (n : ℝ) := by linarith
  have hvB : v ∈ diskFinset B := by
    apply (mem_diskFinset B v).mpr
    change normSq v < B ^ 2
    nlinarith
  by_cases hN : N ≤ n
  · have ht := hsource n hN hn1 (fun y ↦ f (v + y)) (fun y ↦ hf _) (by
      intro y hy
      have hy' : normSq y < (n : ℝ) ^ 2 := (mem_diskFinset _ _).mp hy
      have hyn : normSq y < (B / 2) ^ 2 :=
        hy'.trans_le ((sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr hnle)
      have hsum := normSq_add_lt_of_le_of_lt v y (by positivity : 0 ≤ B / 2)
        (by positivity : 0 ≤ B / 2) hv hyn
      have hm : v + y ∈ diskFinset B := by
        apply (mem_diskFinset B _).mpr
        simpa only [disk, Set.mem_setOf_eq, show B / 2 + B / 2 = B by ring] using hsum
      simpa only [add_assoc] using hh (v + y) hm) z hz
    simp only [add_zero] at ht
    have hcK : c / (n : ℝ) ≤ K / B := by
      apply (div_le_div_iff₀ (by exact_mod_cast (show 0 < n by omega))
        hB0).mpr
      have hcn := mul_le_mul_of_nonneg_left hnB hc.le
      have hkc : 4 * c ≤ K := by
        dsimp [K]
        linarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N]
      have hkn := mul_le_mul_of_nonneg_right hkc
        (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
      nlinarith
    exact ht.trans (mul_le_mul_of_nonneg_right hcK (hf v))
  · have hNB : B ≤ 2 * ((N : ℝ) + 1) := by
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by omega)
      linarith
    have h3 : 3 ≤ K / B := (le_div_iff₀ hB0).mpr (by dsimp [K]; nlinarith)
    exact (harmonic_unit_bound f hf v z (hh v hvB) hz).trans
      (mul_le_mul_of_nonneg_right h3 (hf v))

private theorem relative_chain_upper (F : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hF : ∀ i, 0 ≤ F i) (m : ℕ)
    (hstep : ∀ i < m, |F (i + 1) - F i| ≤ q * F i) :
    F m ≤ Real.exp (q * m) * F 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm := ih (fun i hi ↦ hstep i (by omega))
    have hs := (abs_le.mp (hstep m (by omega))).2
    calc
      F (m + 1) ≤ (q + 1) * F m := by linarith
      _ ≤ (q + 1) * (Real.exp (q * m) * F 0) :=
        mul_le_mul_of_nonneg_left hm (by linarith)
      _ ≤ Real.exp q * (Real.exp (q * m) * F 0) :=
        mul_le_mul_of_nonneg_right (Real.add_one_le_exp q) (mul_nonneg (Real.exp_nonneg _) (hF 0))
      _ = Real.exp (q * ((m + 1 : ℕ) : ℝ)) * F 0 := by
        rw [← mul_assoc, ← Real.exp_add]
        push_cast
        congr 2
        ring

private theorem relative_chain_difference (F : ℕ → ℝ) (q K : ℝ) (hq : 0 ≤ q)
    (hF : ∀ i, 0 ≤ F i) (m : ℕ) (hm : q * m ≤ K)
    (hstep : ∀ i < m, |F (i + 1) - F i| ≤ q * F i) :
    |F m - F 0| ≤ (m : ℝ) * q * Real.exp K * F 0 := by
  have hub (i : ℕ) (hi : i ≤ m) : F i ≤ Real.exp K * F 0 := by
    apply (relative_chain_upper F q hq hF i (fun j hj ↦ hstep j (by omega))).trans
    apply mul_le_mul_of_nonneg_right ?_ (hF 0)
    apply Real.exp_le_exp.mpr
    have him : (i : ℝ) ≤ m := by exact_mod_cast hi
    exact (mul_le_mul_of_nonneg_left him hq).trans hm
  have htel : ∀ i ≤ m, |F i - F 0| ≤ (i : ℝ) * q * Real.exp K * F 0 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hs := (hstep i (by omega)).trans
        (mul_le_mul_of_nonneg_left (hub i (by omega)) hq)
      calc
        _ ≤ |F (i + 1) - F i| + |F i - F 0| := abs_sub_le _ _ _
        _ ≤ q * (Real.exp K * F 0) + (i : ℝ) * q * Real.exp K * F 0 :=
          add_le_add hs hprev
        _ = _ := by rw [Nat.cast_succ]; ring
  exact htel m le_rfl

private def coordinatePath (x : Site) (i : ℕ) : Site :=
  (integerUnitChain 0 x.1 i, integerUnitChain 0 x.2 (i - x.1.natAbs))

private theorem coordinatePath_zero (x : Site) : coordinatePath x 0 = 0 := by
  simp [coordinatePath, integerUnitChain_zero]

private theorem coordinatePath_end (x : Site) :
    coordinatePath x (x.1.natAbs + x.2.natAbs) = x := by
  have hsat : integerUnitChain 0 x.1 (x.1.natAbs + x.2.natAbs) = x.1 := by
    simp only [integerUnitChain]
    push_cast
    have h1 := le_abs_self x.1
    have h2 := neg_le_abs x.1
    have h3 := abs_nonneg x.2
    split_ifs <;> omega
  simp only [coordinatePath, hsat, Nat.add_sub_cancel_left]
  have he := integerUnitChain_end 0 x.2
  simpa using congrArg (fun z ↦ (x.1,z)) he

private theorem coordinatePath_box (x : Site) (M : ℝ) (hM : 0 ≤ M)
    (h1 : |(x.1 : ℝ)| ≤ M) (h2 : |(x.2 : ℝ)| ≤ M) (i : ℕ) :
    normSq (coordinatePath x i) ≤ 2 * M ^ 2 := by
  have hcoord (a : ℤ) (ha : |(a : ℝ)| ≤ M) (j : ℕ) :
      |(integerUnitChain 0 a j : ℝ)| ≤ M := by
    have hh := integerUnitChain_between 0 a j
    have hh' : min (0 : ℝ) a ≤ (integerUnitChain 0 a j : ℝ) ∧
        (integerUnitChain 0 a j : ℝ) ≤ max (0 : ℝ) a := by exact_mod_cast hh
    rw [abs_le] at ha ⊢
    exact ⟨(le_min (by linarith) ha.1).trans hh'.1,
      hh'.2.trans (max_le hM ha.2)⟩
  have ha := (sq_le_sq₀ (abs_nonneg _) hM).mpr (hcoord x.1 h1 i)
  have hb := (sq_le_sq₀ (abs_nonneg _) hM).mpr (hcoord x.2 h2 (i - x.1.natAbs))
  simp only [sq_abs] at ha hb
  dsimp [normSq, coordinatePath]
  linarith

private theorem coordinatePath_step (x : Site) (i : ℕ) :
    normSq (coordinatePath x (i + 1) - coordinatePath x i) ≤ 1 := by
  have hsat (j : ℕ) (hj : x.1.natAbs ≤ j) : integerUnitChain 0 x.1 j = x.1 := by
    unfold integerUnitChain
    have hj' : (x.1.natAbs : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
    rw [Int.natCast_natAbs] at hj'
    split_ifs <;> omega
  by_cases hi : i < x.1.natAbs
  · have h1 := integerUnitChain_step 0 x.1 i
    have hreal :
        |((integerUnitChain 0 x.1 (i + 1) - integerUnitChain 0 x.1 i : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast h1
    have hs := (sq_le_one_iff_abs_le_one _).mpr hreal
    simpa [coordinatePath, show i + 1 - x.1.natAbs = 0 by omega,
      show i - x.1.natAbs = 0 by omega, normSq] using hs
  · have h1 := integerUnitChain_step 0 x.2 (i - x.1.natAbs)
    have hreal : |((integerUnitChain 0 x.2 (i - x.1.natAbs + 1) -
        integerUnitChain 0 x.2 (i - x.1.natAbs) : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h1
    have hs := (sq_le_one_iff_abs_le_one _).mpr hreal
    simpa [coordinatePath, hsat i (by omega), hsat (i + 1) (by omega),
      show i + 1 - x.1.natAbs = i - x.1.natAbs + 1 by omega, normSq] using hs

/-- The article's relative estimate follows from the literal large-integer-radius
first-difference theorem. Harnack is not an additional premise: exponential
control along the same coordinate path supplies the required comparison. -/
theorem positive_harmonic_relative_of_literature
    (hLL : LLPositiveHarmonicDifferenceInput) : PositiveHarmonicRelativeInput := by
  obtain ⟨K, hK, hlocal⟩ := ll_positive_harmonic_local hLL
  refine ⟨4 * K * Real.exp K, by positivity, ?_⟩
  intro b A B hA hAB f hf hh x hx
  have hB : 8 ≤ B := by linarith
  have hB0 : 0 < B := by linarith
  let z := x - b
  let g := fun y ↦ f (b + y)
  have hg : ∀ y, 0 ≤ g y := fun y ↦ hf _
  have hgh : ∀ y ∈ diskFinset B,
      g y = (1 / 4 : ℝ) * ∑ d : Direction, g (y + step d) := by
    intro y hy
    simpa only [g, add_assoc] using hh (b + y) ((mem_translateFinset_add b _ y).mpr hy)
  have hz : normSq z < (2 * A) ^ 2 := by
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hx
  have h1 := abs_fst_le_normSq_bound z (by linarith : 0 ≤ 2 * A) hz.le
  have h2 := abs_snd_le_normSq_bound z (by linarith : 0 ≤ 2 * A) hz.le
  let m := z.1.natAbs + z.2.natAbs
  have hm : (m : ℝ) ≤ 4 * A := by
    dsimp [m]
    simp only [Nat.cast_add, Nat.cast_natAbs, Int.cast_abs]
    linarith
  have hq : 0 ≤ K / B := div_nonneg hK.le hB0.le
  have hqm : K / B * (m : ℝ) ≤ K := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hB0).mpr
    have ht := mul_le_mul_of_nonneg_left (hm.trans (by linarith : 4 * A ≤ B)) hK.le
    nlinarith
  have hsteps (i : ℕ) (hi : i < m) :
      |g (coordinatePath z (i + 1)) - g (coordinatePath z i)| ≤
        K / B * g (coordinatePath z i) := by
    have hp := coordinatePath_box z (2 * A) (by linarith) h1 h2 i
    have hpB : normSq (coordinatePath z i) ≤ (B / 2) ^ 2 := by
      have hab : 0 ≤ B - 8 * A := by linarith
      nlinarith [sq_nonneg (B - 8 * A)]
    have ht := hlocal B hB g hg hgh (coordinatePath z i)
      (coordinatePath z (i + 1) - coordinatePath z i) hpB (coordinatePath_step z i)
    simpa only [add_sub_cancel] using ht
  have hd := relative_chain_difference (fun i ↦ g (coordinatePath z i)) (K / B) K hq
    (fun i ↦ hg _) m hqm hsteps
  rw [coordinatePath_zero] at hd
  have hend : coordinatePath z m = z := coordinatePath_end z
  rw [hend] at hd
  have hc : (m : ℝ) * (K / B) * Real.exp K * g 0 ≤
      (4 * K * Real.exp K) * (A / B) * g 0 := by
    have ht := mul_le_mul_of_nonneg_right hm
      (mul_nonneg (mul_nonneg hq (Real.exp_nonneg K)) (hg 0))
    calc
      _ = (m : ℝ) * (K / B * Real.exp K * g 0) := by ring
      _ ≤ (4 * A) * (K / B * Real.exp K * g 0) := ht
      _ = _ := by ring
  have hout := hd.trans hc
  simpa only [g, z, add_zero, add_sub_cancel] using hout

end SRWTightness
