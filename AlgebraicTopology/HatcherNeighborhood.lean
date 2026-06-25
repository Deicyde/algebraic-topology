import Mathlib

/-!
# Hatcher Appendix: the `N_ε(A)` neighborhood construction (towards Proposition A.3)

Hatcher proves that CW complexes are normal (Proposition A.3) by an inductive
construction, over the skeleta, of an open neighborhood `N_ε(A)` of a subset `A`.
On each characteristic disk `Dⁿ⁺¹` the neighborhood is described in *spherical
coordinates* `(r, θ)` with `r = ‖x‖` the radial coordinate and `θ = x / ‖x‖` the
angular coordinate on the sphere.

Mathlib's CW characteristic maps have domain `closedBall 0 1 ⊆ (Fin n → ℝ)` with
the **sup** norm, so the "disk" is a cube and the "sphere" its boundary; the
radial decomposition nonetheless works verbatim.  This file collects the
foundational, reusable geometric lemmas about these coordinates.  The full
inductive `N_ε` construction and the normality proof are built on top of them;
see the run notes for the decomposition.
-/

open Metric Set
open scoped Topology

namespace HatcherNeighborhood

variable {n : ℕ}

/-- The angular coordinate: radial projection of the punctured disk onto the unit
sphere, `x ↦ ‖x‖⁻¹ • x`, is continuous away from the origin. -/
theorem continuousOn_radialProj :
    ContinuousOn (fun x : Fin n → ℝ => (‖x‖)⁻¹ • x) {x | x ≠ 0} := by
  have hinv : ContinuousOn (fun x : Fin n → ℝ => (‖x‖)⁻¹) {x | x ≠ 0} :=
    continuous_norm.continuousOn.inv₀ (fun x hx => norm_ne_zero_iff.mpr hx)
  exact hinv.smul continuousOn_id

/-- The radial projection lands on the unit sphere. -/
theorem radialProj_mem_sphere {x : Fin n → ℝ} (hx : x ≠ 0) :
    (‖x‖)⁻¹ • x ∈ sphere (0 : Fin n → ℝ) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

/-- Radial projection followed by scaling back recovers the point. -/
theorem norm_smul_radialProj {x : Fin n → ℝ} (hx : x ≠ 0) :
    ‖x‖ • ((‖x‖)⁻¹ • x) = x := by
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

/-- The outer collar `1 - ε < ‖x‖` of the disk is open: this is the region in
which Hatcher's product `(1-ε, 1] × …` collar lives. -/
theorem isOpen_collar (ε : ℝ) : IsOpen {x : Fin n → ℝ | 1 - ε < ‖x‖} :=
  isOpen_lt continuous_const continuous_norm

/-- The open `δ`-core `‖x‖ < δ` of the disk is open; together with the collar it
covers the punctured disk for suitable parameters. -/
theorem isOpen_core (δ : ℝ) : IsOpen {x : Fin n → ℝ | ‖x‖ < δ} :=
  isOpen_lt continuous_norm continuous_const

/-- **Collar slice is open.** For `ε < 1` and an open ambient set `U`, the
"collar slice" of disk points with radius `> 1 - ε` whose angular coordinate lies
in `U` is open.  This is the geometric core of why each stage of Hatcher's
`N_ε(A)` construction is open: the product collar `(1-ε, 1] × Φ⁻¹(N_ε^n)` pulls
back to exactly such a slice. -/
theorem isOpen_collarSlice {ε : ℝ} (hε : ε < 1) {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) :
    IsOpen {x : Fin n → ℝ | 1 - ε < ‖x‖ ∧ (‖x‖)⁻¹ • x ∈ U} := by
  have hsub : {x : Fin n → ℝ | 1 - ε < ‖x‖} ⊆ {x | x ≠ 0} := by
    intro x hx h0
    rw [mem_setOf_eq, h0, norm_zero] at hx
    linarith
  have heq : {x : Fin n → ℝ | 1 - ε < ‖x‖ ∧ (‖x‖)⁻¹ • x ∈ U}
      = {x | 1 - ε < ‖x‖} ∩ (fun x : Fin n → ℝ => (‖x‖)⁻¹ • x) ⁻¹' U := rfl
  rw [heq]
  exact (continuousOn_radialProj.mono hsub).isOpen_inter_preimage (isOpen_collar ε) hU

/-- **Analytic core of "small enough `ε`".** Two disjoint compact sets in a
metric space admit a common positive thickening radius keeping their open
thickenings disjoint. This is exactly Hatcher's step: on each disk the preimages
of the disjoint closed sets are compact and a positive distance apart, so a small
enough cell-wise `ε_α` keeps the cell neighborhoods disjoint. -/
theorem exists_eps_separating_thickenings {α : Type*} [MetricSpace α]
    {s t : Set α} (hs : IsCompact s) (ht : IsCompact t) (hst : Disjoint s t) :
    ∃ ε > 0, Disjoint (Metric.thickening ε s) (Metric.thickening ε t) :=
  hst.exists_thickenings hs ht.isClosed

/-- A separating thickening radius that keeps working for all smaller positive
radii. Useful for the radius recursion, where a cell's radius may be forced smaller
by several constraints simultaneously. -/
theorem exists_eps_thickenings_subset {α : Type*} [MetricSpace α]
    {P Q : Set α} (hP : IsCompact P) (hQ : IsCompact Q) (hPQ : Disjoint P Q) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε ≤ δ →
      Disjoint (Metric.thickening ε P) (Metric.thickening ε Q) := by
  obtain ⟨δ, hδ, hd⟩ := exists_eps_separating_thickenings hP hQ hPQ
  exact ⟨δ, hδ, fun ε _ hεδ =>
    hd.mono (Metric.thickening_mono hεδ P) (Metric.thickening_mono hεδ Q)⟩

end HatcherNeighborhood
