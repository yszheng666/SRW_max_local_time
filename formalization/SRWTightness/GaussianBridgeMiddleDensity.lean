import SRWTightness.GaussianDensityProductIdentity
import SRWTightness.GaussianDensitySymmetry

open ProbabilityTheory
namespace SRWTightness

/-- The bridge's Gaussian middle density is the normalized product of Brownian densities. -/
theorem gaussian_bridge_middle_density (T r b z : ℝ) (hr : 0 < r) (hrT : r < T) :
    gaussianPDFReal (r / T * b) (r * (T - r) / T).toNNReal z =
      gaussianPDFReal 0 r.toNNReal z * gaussianPDFReal z (T - r).toNNReal b /
        gaussianPDFReal 0 T.toNNReal b := by
  have hT : 0 < T := hr.trans hrT
  have he := gaussian_density_product_identity r (T - r) 0 b z hr (sub_pos.mpr hrT)
  have hs : r + (T - r) = T := by ring
  have hm : ((T - r) * 0 + r * b) / T = r / T * b := by ring
  rw [hs, hm, gaussian_density_spatial_symmetry b z] at he
  have hp : gaussianPDFReal 0 T.toNNReal b ≠ 0 :=
    ne_of_gt (gaussianPDFReal_pos _ _ _ (ne_of_gt (Real.toNNReal_pos.mpr hT)))
  rw [he, mul_div_cancel_left₀ _ hp]

end SRWTightness
