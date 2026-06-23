import Mathlib

/-!
# Hatcher Appendix: Topology of Cell Complexes (CW complexes)

Formalization of point-set results about CW complexes from the Appendix of
Hatcher's *Algebraic Topology*, over Mathlib's CW-complex API
(`Topology.CWComplex`).
-/

open Topology

namespace HatcherCW

/-! ## Compactness (Proposition A.1) -/

/-- **Compact subspace lies in a finite subcomplex.** Let `C` be a CW complex in a
Hausdorff space `X`, and let `K ⊆ C` be compact. Then there is a finite subcomplex
`E` of `C` with `K ⊆ E`. -/
theorem compact_subset_finite_subcomplex {X : Type*} [TopologicalSpace X] [T2Space X]
    {C : Set X} [CWComplex C] {K : Set X} (hKC : K ⊆ C) (hK : IsCompact K) :
    ∃ E : CWComplex.Subcomplex C, CWComplex.Finite (E : Set X) ∧ K ⊆ (E : Set X) :=
  sorry

end HatcherCW
