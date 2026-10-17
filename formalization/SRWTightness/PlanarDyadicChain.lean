import SRWTightness.PlanarDyadicRepresentatives

namespace SRWTightness

/-- A dyadic representative chain starts at the prescribed anchor. -/
noncomputable def planarDyadicChain {ι : Type*}
    (J : Finset ι) (p : ι → ℝ × ℝ) (o : ι) (R : ℝ) : ℕ → ι → ι
  | 0, _ => o
  | n + 1, x => planarDyadicRepresentative J p o R n x

/-- Every link stays in the actual observation set. -/
theorem planarDyadicChain_mem {ι : Type*}
    (J : Finset ι) (p : ι → ℝ × ℝ) (o : ι) (ho : o ∈ J) (R : ℝ)
    (n : ℕ) (x : ι) (hx : x ∈ J) : planarDyadicChain J p o R n x ∈ J := by
  cases n with
  | zero => exact ho
  | succ n => exact (planarDyadicRepresentative_spec J p o R n x hx).1

/-- Each successive link has a uniform geometrically decreasing squared displacement. -/
theorem planarDyadicChain_increment_bound {ι : Type*}
    (J : Finset ι) (p : ι → ℝ × ℝ) (o : ι) (ho : o ∈ J) (R : ℝ) (hR : 0 < R)
    (hp : ∀ x ∈ J, (p x).1 ^ 2 + (p x).2 ^ 2 ≤ R ^ 2)
    (n : ℕ) (x : ι) (hx : x ∈ J) :
    let a := p (planarDyadicChain J p o R (n + 1) x)
    let b := p (planarDyadicChain J p o R n x)
    (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 ≤ 32 * (R / 2 ^ n) ^ 2 := by
  cases n with
  | zero =>
      have ha := hp _ (planarDyadicRepresentative_spec J p o R 0 x hx).1
      have hb := hp o ho
      dsimp [planarDyadicChain]
      simp only [pow_zero, div_one]
      nlinarith [sq_nonneg ((p (planarDyadicRepresentative J p o R 0 x)).1 + (p o).1),
        sq_nonneg ((p (planarDyadicRepresentative J p o R 0 x)).2 + (p o).2),
        sq_nonneg R]
  | succ n =>
      let a := p (planarDyadicRepresentative J p o R (n + 1) x)
      let b := p (planarDyadicRepresentative J p o R n x)
      have ha := planarDyadicCell_distance R hR (n + 1) a (p x)
        (planarDyadicRepresentative_spec J p o R (n + 1) x hx).2
      have hb := planarDyadicCell_distance R hR n b (p x)
        (planarDyadicRepresentative_spec J p o R n x hx).2
      have hw : 0 ≤ R / (2 : ℝ) ^ (n + 1) := by positivity
      have hww : R / (2 : ℝ) ^ (n + 1) ≤ R / (2 : ℝ) ^ n := by
        rw [pow_succ, div_mul_eq_div_div]
        exact div_le_self (by positivity) (by norm_num)
      have hsq := (sq_le_sq₀ hw (by positivity)).mpr hww
      have he : 32 * (R / (2 : ℝ) ^ (n + 1)) ^ 2 = 8 * (R / (2 : ℝ) ^ n) ^ 2 := by
        rw [pow_succ]
        field_simp
        ring
      change (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 ≤ _
      rw [he]
      nlinarith [sq_nonneg (a.1 + b.1 - 2 * (p x).1),
        sq_nonneg (a.2 + b.2 - 2 * (p x).2)]

/-- The possible edges at each dyadic level have a uniform finite entropy bound. -/
theorem planarDyadicChain_edge_card {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (p : ι → ℝ × ℝ) (o : ι) (R : ℝ) (hR : 0 < R)
    (hp : ∀ x ∈ J, (p x).1 ^ 2 + (p x).2 ^ 2 ≤ R ^ 2) (n : ℕ) :
    (J.image (fun x ↦ (planarDyadicChain J p o R (n + 1) x,
      planarDyadicChain J p o R n x))).card ≤ 81 * 16 ^ n := by
  have hsub (f g : ι → ι) : J.image (fun x ↦ (f x, g x)) ⊆ (J.image f).product (J.image g) := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hh := Finset.card_le_card (hsub (planarDyadicChain J p o R (n + 1))
    (planarDyadicChain J p o R n))
  rw [Finset.product_eq_sprod, Finset.card_product] at hh
  cases n with
  | zero =>
      have ha := planarDyadicRepresentative_card J p o R hR 0 hp
      have hb : (J.image (fun _ ↦ o)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
        rfl
      change (J.image (fun x ↦ (planarDyadicRepresentative J p o R 0 x, o))).card ≤
        (J.image (planarDyadicRepresentative J p o R 0)).card *
        (J.image (fun _ ↦ o)).card at hh
      simp only [planarDyadicChain, pow_zero, mul_one] at ha ⊢
      exact hh.trans ((Nat.mul_le_mul ha hb).trans (by norm_num))
  | succ n =>
      have ha := planarDyadicRepresentative_card J p o R hR (n + 1) hp
      have hb := planarDyadicRepresentative_card J p o R hR n hp
      have hm := mul_le_mul ha hb (Nat.zero_le _) (Nat.zero_le _)
      have hpow : (4 : ℕ) ^ (n + 1) * 4 ^ n ≤ 16 ^ (n + 1) := by
        rw [pow_succ, pow_succ]
        have he : (4 : ℕ) ^ n * 4 ^ n = 16 ^ n := by rw [← mul_pow]; norm_num
        nlinarith
      change _ ≤ _ at hh
      exact hh.trans (hm.trans (by nlinarith))

end SRWTightness
