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
      ∀ i ∈ s, (E i : Set X) ⊆ (G : Set X) := by
  classical
  set U : Set X := ⋃ i ∈ s, ((E i : CWComplex.Subcomplex C) : Set X) with hU
  set Idx : Π n, Set (Topology.CWComplex.cell C n) := fun n => ⋃ i ∈ s, (E i).I n with hIdx
  have cs : ∀ (n : ℕ) (c : ↥(Idx n)),
      Topology.CWComplex.closedCell (C := C) n ↑c ⊆ U := by
    rintro n ⟨c, hc⟩
    rw [hIdx] at hc
    simp only [Set.mem_iUnion] at hc
    obtain ⟨i, hi, hci⟩ := hc
    refine (CWComplex.Subcomplex.closedCell_subset_of_mem (E i) hci).trans ?_
    rw [hU]
    exact fun x hx => Set.mem_biUnion hi hx
  have un : ⋃ n, ⋃ (j : ↥(Idx n)), Topology.CWComplex.openCell (C := C) n ↑j = U := by
    rw [hU]
    simp_rw [← CWComplex.Subcomplex.union (C := C)]
    ext x
    simp only [hIdx, Set.iUnion_subtype, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨n, c, ⟨i, hi, hc⟩, hx⟩
      exact ⟨i, hi, n, c, hc, hx⟩
    · rintro ⟨i, hi, n, c, hc, hx⟩
      exact ⟨n, c, ⟨i, hi, hc⟩, hx⟩
  refine ⟨CWComplex.Subcomplex.mk' C U Idx cs un, ?_, ?_⟩
  · rw [CWComplex.finite_iff_finite_cells]
    simp only [CWComplex.Subcomplex.cell_def, CWComplex.Subcomplex.mk'_I, hIdx]
    have hcell : ∀ i ∈ s, Finite (Σ n, ↥((E i).I n)) := by
      intro i hi
      have h := (CWComplex.finite_iff_finite_cells (C := (E i : Set X))).mp (hfin i hi)
      simpa only [CWComplex.Subcomplex.cell_def] using h
    haveI : ∀ i : {i // i ∈ s}, Finite (Σ n, ↥((E (i : ι)).I n)) := fun i => hcell i i.2
    apply Finite.of_surjective
      (f := fun p : Σ (i : {i // i ∈ s}), Σ n, ↥((E (i : ι)).I n) =>
        (⟨p.2.1, ⟨↑p.2.2, by
          simp only [Set.mem_iUnion]
          exact ⟨↑p.1, p.1.2, p.2.2.2⟩⟩⟩ : Σ n, ↥(⋃ i ∈ s, (E i).I n)))
    rintro ⟨n, ⟨c, hc⟩⟩
    simp only [Set.mem_iUnion] at hc
    obtain ⟨i, hi, hci⟩ := hc
    exact ⟨⟨⟨i, hi⟩, ⟨n, ⟨c, hci⟩⟩⟩, rfl⟩
  · intro i hi
    rw [CWComplex.Subcomplex.coe_mk', hU]
    exact fun x hx => Set.mem_biUnion hi hx

/-- **Enlarging a subcomplex by one cell.** If the frontier of an `n`-cell is
contained in a subcomplex `E`, then `E` extends to a subcomplex `F` containing
the whole closed cell, and `F` is finite whenever `E` is. -/
theorem subcomplex_insert_cell [CWComplex C] (E : CWComplex.Subcomplex C)
    (n : ℕ) (i : Topology.CWComplex.cell C n)
    (hfront : CWComplex.cellFrontier (C := C) n i ⊆ (E : Set X)) :
    ∃ F : CWComplex.Subcomplex C, (E : Set X) ⊆ (F : Set X) ∧
      CWComplex.closedCell (C := C) n i ⊆ (F : Set X) ∧
      (CWComplex.Finite (E : Set X) → CWComplex.Finite (F : Set X)) :=
  sorry

/-- **Each closed cell lies in a finite subcomplex.** Proved by strong induction
on the dimension, using that a cell's frontier is covered by finitely many closed
cells of lower dimension. -/
theorem closedCell_subset_finite_subcomplex [CWComplex C] (n : ℕ)
    (i : Topology.CWComplex.cell C n) :
    ∃ F : CWComplex.Subcomplex C, CWComplex.Finite (F : Set X) ∧
      CWComplex.closedCell (C := C) n i ⊆ (F : Set X) :=
  sorry

/-- **Compact subsets meet finitely many cells.** The set of cells of `C` whose
open cell meets a compact `K ⊆ C` is finite. -/
theorem finite_cells_meeting_compact [CWComplex C] {K : Set X} (hKC : K ⊆ C)
    (hK : IsCompact K) :
    {p : Σ n, Topology.CWComplex.cell C n | (CWComplex.openCell (C := C) p.1 p.2 ∩ K).Nonempty}.Finite :=
  sorry

/-- **Compact subspace lies in a finite subcomplex.** Let `C` be a CW complex in a
Hausdorff space `X`, and let `K ⊆ C` be compact. Then there is a finite subcomplex
`E` of `C` with `K ⊆ E`. -/
theorem compact_subset_finite_subcomplex [CWComplex C] {K : Set X} (hKC : K ⊆ C)
    (hK : IsCompact K) :
    ∃ E : CWComplex.Subcomplex C, CWComplex.Finite (E : Set X) ∧ K ⊆ (E : Set X) :=
  sorry

end HatcherCW
