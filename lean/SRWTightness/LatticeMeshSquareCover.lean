import SRWTightness.LatticeSquareShell
import SRWTightness.DiskFiniteDomain

namespace SRWTightness

/-- Integer coordinate scaling for the actual lattice mesh. -/
def latticeScale (a : ℕ) (z : Site) : Site := ((a : ℤ) * z.1, (a : ℤ) * z.2)

theorem normSq_latticeScale (a : ℕ) (z : Site) :
    normSq (latticeScale a z) = (a : ℝ) ^ 2 * normSq z := by
  simp only [latticeScale, normSq, Int.cast_mul, Int.cast_natCast]
  ring

theorem latticeScale_injective (a : ℕ) (ha : 0 < a) : Function.Injective (latticeScale a) := by
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  exact Prod.ext (mul_left_cancel₀ ha0 h₁) (mul_left_cancel₀ ha0 h₂)

/-- Every mesh point in a disk is the scaling of a point in a finite integer square. -/
theorem lattice_mesh_square_cover (R : ℝ) (hR : 0 < R) (a : ℕ) (ha : 0 < a)
    (Z : Finset Site)
    (hZ : ∀ z ∈ Z, z ∈ diskFinset R ∧ (a : ℤ) ∣ z.1 ∧ (a : ℤ) ∣ z.2) :
    Z ⊆ (centeredLatticeSquare ⌈R / (a : ℝ)⌉₊).image (latticeScale a) := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  intro z hz
  obtain ⟨hzR, ⟨u, hu⟩, ⟨v, hv⟩⟩ := hZ z hz
  let w : Site := (u, v)
  have he : latticeScale a w = z := Prod.ext hu.symm hv.symm
  have hn : (a : ℝ) ^ 2 * normSq w < R ^ 2 := by
    rw [← normSq_latticeScale, he]
    exact (mem_diskFinset _ _).mp hzR
  have hw : normSq w ≤ (R / (a : ℝ)) ^ 2 := by
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos ha')).mpr
    nlinarith
  have hceil : R / (a : ℝ) ≤ (⌈R / (a : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hx := (abs_fst_le_normSq_bound w (by positivity) hw).trans hceil
  have hy := (abs_snd_le_normSq_bound w (by positivity) hw).trans hceil
  have hx' : -(⌈R / (a : ℝ)⌉₊ : ℤ) ≤ w.1 ∧ w.1 ≤ (⌈R / (a : ℝ)⌉₊ : ℤ) := by
    exact_mod_cast abs_le.mp hx
  have hy' : -(⌈R / (a : ℝ)⌉₊ : ℤ) ≤ w.2 ∧ w.2 ≤ (⌈R / (a : ℝ)⌉₊ : ℤ) := by
    exact_mod_cast abs_le.mp hy
  exact Finset.mem_image.mpr ⟨w,
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hx', Finset.mem_Icc.mpr hy'⟩, he⟩

end SRWTightness
