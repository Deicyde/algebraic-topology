import Mathlib

/-!
# Hatcher Appendix: Topology of Cell Complexes (CW complexes)

Formalization of point-set results about CW complexes from the Appendix of
Hatcher's *Algebraic Topology*, over Mathlib's CW-complex API
(`Topology.CWComplex`).
-/

open Topology

namespace HatcherCW

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C : Set X}

/-! ## Compactness (Proposition A.1)

The proof is decomposed into four reusable steps over Mathlib's subcomplex API.
-/

/-- **Finite union of finite subcomplexes.** Given a finite family of finite
subcomplexes of `C`, there is a single finite subcomplex containing all of them. -/
theorem iUnion_subcomplex_finite [CWComplex C] {ι : Type*} (s : Finset ι)
    (E : ι → CWComplex.Subcomplex C)
    (hfin : ∀ i ∈ s, CWComplex.Finite (E i : Set X)) :
    ∃ G : CWComplex.Subcomplex C, CWComplex.Finite (G : Set X) ∧
      ∀ i ∈ s, (E i : Set X) ⊆ (G : Set X) :=
  sorry

/-- **Enlarging a subcomplex by one cell.** If the frontier of an `n`-cell is
contained in a subcomplex `E`, then `E` extends to a subcomplex `F` containing
the whole closed cell, and `F` is finite whenever `E` is. -/
theorem subcomplex_insert_cell [CWComplex C] (E : CWComplex.Subcomplex C)
    (n : ℕ) (i : CWComplex.cell C n)
    (hfront : CWComplex.cellFrontier n i ⊆ (E : Set X)) :
    ∃ F : CWComplex.Subcomplex C, (E : Set X) ⊆ (F : Set X) ∧
      CWComplex.closedCell n i ⊆ (F : Set X) ∧
      (CWComplex.Finite (E : Set X) → CWComplex.Finite (F : Set X)) :=
  sorry

/-- **Each closed cell lies in a finite subcomplex.** Proved by strong induction
on the dimension, using that a cell's frontier is covered by finitely many closed
cells of lower dimension. -/
theorem closedCell_subset_finite_subcomplex [CWComplex C] (n : ℕ)
    (i : CWComplex.cell C n) :
    ∃ F : CWComplex.Subcomplex C, CWComplex.Finite (F : Set X) ∧
      CWComplex.closedCell n i ⊆ (F : Set X) :=
  sorry

/-- **Compact subsets meet finitely many cells.** The set of cells of `C` whose
open cell meets a compact `K ⊆ C` is finite. -/
theorem finite_cells_meeting_compact [CWComplex C] {K : Set X} (hKC : K ⊆ C)
    (hK : IsCompact K) :
    {p : Σ n, CWComplex.cell C n | (CWComplex.openCell p.1 p.2 ∩ K).Nonempty}.Finite :=
  sorry

/-- **Compact subspace lies in a finite subcomplex.** Let `C` be a CW complex in a
Hausdorff space `X`, and let `K ⊆ C` be compact. Then there is a finite subcomplex
`E` of `C` with `K ⊆ E`. -/
theorem compact_subset_finite_subcomplex [CWComplex C] {K : Set X} (hKC : K ⊆ C)
    (hK : IsCompact K) :
    ∃ E : CWComplex.Subcomplex C, CWComplex.Finite (E : Set X) ∧ K ⊆ (E : Set X) :=
  sorry

end HatcherCW
