import Mathlib

/-!
# Hatcher Appendix, Proposition A.3 (CW complexes are normal)

Hatcher's Proposition A.3 states that every CW complex is a normal space (and in
particular Hausdorff). Over Mathlib's `Topology.CWComplex` API a CW structure is
a predicate on a set `C` in an ambient Hausdorff space `X`, so the mathematical
content is the normality of the *subspace* `C`, i.e. `NormalSpace ↥C`.

The proof builds separating open neighborhoods `Nε(A)` and `Nε(B)` of disjoint
closed sets by an inductive construction over the skeleta: starting from the
empty neighborhood on the `0`-skeleton, one extends across each cell by adjoining
an open `ε`-neighborhood of the preimage together with a spherical collar, with
the cell-wise radii chosen small enough to keep the two neighborhoods disjoint.
-/

open Topology

namespace HatcherNormal

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C : Set X}

/-- **Separating neighborhoods of disjoint closed sets.** For any two disjoint
subsets `A, B` of the subspace `C` that are closed in `C`, there exist disjoint
open neighborhoods, i.e. `SeparatedNhds A B`. This is the inductive
neighborhood construction `Nε(A)`, `Nε(B)` over the skeleta of the CW complex. -/
theorem exists_disjoint_nhds [CWComplex C] {A B : Set ↥C}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    SeparatedNhds A B := by
  sorry

/-- **CW complexes are normal.** The subspace `C` of a CW complex in a Hausdorff
space `X` is a normal topological space. -/
theorem normalSpace [CWComplex C] : NormalSpace ↥C :=
  ⟨fun _ _ hA hB hAB => exists_disjoint_nhds hA hB hAB⟩

end HatcherNormal
