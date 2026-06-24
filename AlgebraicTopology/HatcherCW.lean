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
      (CWComplex.Finite (E : Set X) → CWComplex.Finite (F : Set X)) := by
  classical
  set J : Π m, Set (Topology.CWComplex.cell C m) :=
    Function.update E.I n (insert i (E.I n)) with hJ
  set Fset : Set X := (E : Set X) ∪ CWComplex.closedCell (C := C) n i with hFset
  have hJmem : ∀ (m) (c : Topology.CWComplex.cell C m), c ∈ E.I m → c ∈ J m := by
    intro m c hc
    rw [hJ]
    by_cases hm : m = n
    · subst hm; rw [Function.update_self]; exact Set.mem_insert_of_mem _ hc
    · rw [Function.update_of_ne hm]; exact hc
  have hJi : i ∈ J n := by rw [hJ, Function.update_self]; exact Set.mem_insert _ _
  have cs : ∀ (m : ℕ) (c : ↥(J m)),
      CWComplex.closedCell (C := C) m ↑c ⊆ Fset := by
    rintro m ⟨c, hc⟩
    rw [hJ] at hc
    by_cases hm : m = n
    · subst hm
      rw [Function.update_self] at hc
      rcases hc with hc | hc
      · subst hc; exact Set.subset_union_right
      · exact (CWComplex.Subcomplex.closedCell_subset_of_mem E hc).trans Set.subset_union_left
    · rw [Function.update_of_ne hm] at hc
      exact (CWComplex.Subcomplex.closedCell_subset_of_mem E hc).trans Set.subset_union_left
  have un : ⋃ m, ⋃ (j : ↥(J m)), CWComplex.openCell (C := C) m ↑j = Fset := by
    apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun m => Set.iUnion_subset fun j => ?_
      exact (CWComplex.openCell_subset_closedCell (C := C) m j.1).trans (cs m j)
    · have hE_sub : (E : Set X) ⊆
          ⋃ m, ⋃ (j : ↥(J m)), CWComplex.openCell (C := C) m ↑j := by
        conv_lhs => rw [← CWComplex.Subcomplex.union (C := C) (E := E)]
        refine Set.iUnion_subset fun m => Set.iUnion_subset fun j => ?_
        exact Set.subset_iUnion_of_subset m
          (Set.subset_iUnion_of_subset ⟨j.1, hJmem m j.1 j.2⟩ Set.Subset.rfl)
      have hi_sub : CWComplex.openCell (C := C) n i ⊆
          ⋃ m, ⋃ (j : ↥(J m)), CWComplex.openCell (C := C) m ↑j :=
        Set.subset_iUnion_of_subset n
          (Set.subset_iUnion_of_subset ⟨i, hJi⟩ Set.Subset.rfl)
      have hcc : CWComplex.closedCell (C := C) n i ⊆
          (E : Set X) ∪ CWComplex.openCell (C := C) n i := by
        rw [← CWComplex.cellFrontier_union_openCell_eq_closedCell (C := C) n i]
        exact Set.union_subset_union_left _ hfront
      rw [hFset]
      exact Set.union_subset hE_sub (hcc.trans (Set.union_subset hE_sub hi_sub))
  refine ⟨CWComplex.Subcomplex.mk' C Fset J cs un, ?_, ?_, ?_⟩
  · rw [CWComplex.Subcomplex.coe_mk', hFset]; exact Set.subset_union_left
  · rw [CWComplex.Subcomplex.coe_mk', hFset]; exact Set.subset_union_right
  · intro hEfin
    rw [CWComplex.finite_iff_finite_cells]
    simp only [CWComplex.Subcomplex.cell_def, CWComplex.Subcomplex.mk'_I]
    haveI hE : Finite (Σ m, ↥(E.I m)) := by
      have h := (CWComplex.finite_iff_finite_cells (C := (E : Set X))).mp hEfin
      simpa only [CWComplex.Subcomplex.cell_def] using h
    apply Finite.of_surjective
      (f := fun (o : Option (Σ m, ↥(E.I m))) =>
        (match o with
          | none => ⟨n, ⟨i, hJi⟩⟩
          | some p => ⟨p.1, ⟨p.2.1, hJmem p.1 p.2.1 p.2.2⟩⟩ : Σ m, ↥(J m)))
    rintro ⟨m, ⟨c, hc⟩⟩
    by_cases hmn : m = n
    · subst hmn
      rw [hJ, Function.update_self] at hc
      rcases hc with hc | hc
      · subst hc; exact ⟨none, rfl⟩
      · exact ⟨some ⟨m, ⟨c, hc⟩⟩, rfl⟩
    · rw [hJ, Function.update_of_ne hmn] at hc
      exact ⟨some ⟨m, ⟨c, hc⟩⟩, rfl⟩

/-- **Each closed cell lies in a finite subcomplex.** Proved by strong induction
on the dimension, using that a cell's frontier is covered by finitely many closed
cells of lower dimension. -/
theorem closedCell_subset_finite_subcomplex [CWComplex C] (n : ℕ)
    (i : Topology.CWComplex.cell C n) :
    ∃ F : CWComplex.Subcomplex C, CWComplex.Finite (F : Set X) ∧
      CWComplex.closedCell (C := C) n i ⊆ (F : Set X) := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell (C := C) n i
    set s : Finset (Σ m, Topology.CWComplex.cell C m) := (Finset.range n).sigma I with hs
    have key : ∀ p ∈ s, ∃ F : CWComplex.Subcomplex C,
        CWComplex.Finite (F : Set X) ∧
          CWComplex.closedCell (C := C) p.1 p.2 ⊆ (F : Set X) := by
      rintro ⟨m, j⟩ hp
      rw [hs, Finset.mem_sigma, Finset.mem_range] at hp
      exact IH m hp.1 j
    let Ef : ↥s → CWComplex.Subcomplex C := fun p => Classical.choose (key p.1 p.2)
    have hEf : ∀ p : ↥s, CWComplex.Finite (Ef p : Set X) ∧
        CWComplex.closedCell (C := C) p.1.1 p.1.2 ⊆ (Ef p : Set X) :=
      fun p => Classical.choose_spec (key p.1 p.2)
    obtain ⟨G, hGfin, hGsub⟩ :=
      iUnion_subcomplex_finite s.attach Ef (fun p _ => (hEf p).1)
    have hfrontG : CWComplex.cellFrontier (C := C) n i ⊆ (G : Set X) := by
      refine hI.trans ?_
      refine Set.iUnion_subset fun m => Set.iUnion_subset fun hm =>
        Set.iUnion_subset fun j => Set.iUnion_subset fun hj => ?_
      have hp : (⟨m, j⟩ : Σ m, Topology.CWComplex.cell C m) ∈ s := by
        rw [hs, Finset.mem_sigma, Finset.mem_range]; exact ⟨hm, hj⟩
      exact (hEf ⟨⟨m, j⟩, hp⟩).2.trans (hGsub ⟨⟨m, j⟩, hp⟩ (Finset.mem_attach _ _))
    obtain ⟨F, _, hccF, hFfin⟩ := subcomplex_insert_cell G n i hfrontG
    exact ⟨F, hFfin hGfin, hccF⟩

/-- Each closed cell meets only finitely many open cells: the set of cells whose
open cell meets a fixed closed cell is finite. Follows from
`closedCell_subset_finite_subcomplex` and disjointness of open cells. -/
theorem finite_cells_meeting_closedCell [CWComplex C] (n : ℕ)
    (j : Topology.CWComplex.cell C n) :
    {p : Σ m, Topology.CWComplex.cell C m |
      (CWComplex.openCell (C := C) p.1 p.2 ∩
        CWComplex.closedCell (C := C) n j).Nonempty}.Finite := by
  classical
  obtain ⟨F, hFfin, hFsub⟩ := closedCell_subset_finite_subcomplex (C := C) n j
  haveI : Finite (Σ m, ↥(F.I m)) := by
    have h := (CWComplex.finite_iff_finite_cells (C := (F : Set X))).mp hFfin
    simpa only [CWComplex.Subcomplex.cell_def] using h
  have hTfin : {p : Σ m, Topology.CWComplex.cell C m | p.2 ∈ F.I p.1}.Finite := by
    rw [← Set.finite_coe_iff]
    apply Finite.of_surjective
      (f := fun q : Σ m, ↥(F.I m) =>
        (⟨⟨q.1, q.2.1⟩, q.2.2⟩ :
          {p : Σ m, Topology.CWComplex.cell C m | p.2 ∈ F.I p.1}))
    rintro ⟨⟨m, c⟩, hc⟩
    exact ⟨⟨m, ⟨c, hc⟩⟩, rfl⟩
  apply hTfin.subset
  rintro ⟨m, c⟩ ⟨y, hy_oc, hy_cc⟩
  have hyF : y ∈ (F : Set X) := hFsub hy_cc
  rw [← CWComplex.Subcomplex.union (C := C) (E := F)] at hyF
  simp only [Set.mem_iUnion] at hyF
  obtain ⟨m', l, hyl⟩ := hyF
  have heq : (⟨m, c⟩ : Σ k, Topology.CWComplex.cell C k) = ⟨m', ↑l⟩ :=
    CWComplex.eq_of_not_disjoint_openCell (Set.not_disjoint_iff.mpr ⟨y, hy_oc, hyl⟩)
  simp only [Set.mem_setOf_eq]
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp heq
  rw [eq_of_heq h2]; exact l.2

/-- **Compact subsets meet finitely many cells.** The set of cells of `C` whose
open cell meets a compact `K ⊆ C` is finite. -/
theorem finite_cells_meeting_compact [CWComplex C] {K : Set X} (hKC : K ⊆ C)
    (hK : IsCompact K) :
    {p : Σ n, Topology.CWComplex.cell C n | (CWComplex.openCell (C := C) p.1 p.2 ∩ K).Nonempty}.Finite := by
  classical
  set S : Set (Σ n, Topology.CWComplex.cell C n) :=
    {p | (CWComplex.openCell (C := C) p.1 p.2 ∩ K).Nonempty} with hS
  choose x hx using fun p : ↥S => p.2
  have hxinj : Function.Injective x := by
    intro p q hpq
    have hd : ¬ Disjoint (CWComplex.openCell (C := C) p.1.1 p.1.2)
        (CWComplex.openCell (C := C) q.1.1 q.1.2) := by
      rw [Set.not_disjoint_iff]; exact ⟨x p, (hx p).1, hpq ▸ (hx q).1⟩
    have heq := CWComplex.eq_of_not_disjoint_openCell hd
    exact Subtype.ext ((Sigma.eta p.1).symm.trans (heq.trans (Sigma.eta q.1)))
  set T : Set X := Set.range x with hT
  have hTK : T ⊆ K := by rintro _ ⟨p, rfl⟩; exact (hx p).2
  have hTC : T ⊆ C := hTK.trans hKC
  have hTcc : ∀ (m : ℕ) (l : Topology.CWComplex.cell C m),
      (T ∩ CWComplex.closedCell (C := C) m l).Finite := by
    intro m l
    have hPfin : {p : ↥S | x p ∈ CWComplex.closedCell (C := C) m l}.Finite := by
      apply Set.Finite.of_finite_image
        (f := fun p : ↥S => (p : Σ k, Topology.CWComplex.cell C k))
      · apply (finite_cells_meeting_closedCell (C := C) m l).subset
        rintro _ ⟨p, hp, rfl⟩
        exact ⟨x p, (hx p).1, hp⟩
      · exact Subtype.val_injective.injOn
    apply (hPfin.image x).subset
    rintro y ⟨⟨p, rfl⟩, hcc⟩
    exact ⟨p, hcc, rfl⟩
  have hAllClosed : ∀ A : Set X, A ⊆ T → IsClosed A := by
    intro A hAT
    rw [CWComplex.closed C A (hAT.trans hTC)]
    intro m l
    exact ((hTcc m l).subset (Set.inter_subset_inter_left _ hAT)).isClosed
  have hTclosed : IsClosed T := hAllClosed T (le_refl _)
  have hTcompact : IsCompact T := hK.of_isClosed_subset hTclosed hTK
  haveI hTdisc : DiscreteTopology ↥T := by
    rw [discreteTopology_iff_forall_isClosed]
    intro A
    have hImg : IsClosed (Subtype.val '' A : Set X) :=
      hAllClosed _ (by rintro _ ⟨a, -, rfl⟩; exact a.2)
    rw [show A = Subtype.val ⁻¹' (Subtype.val '' A) from
      (Set.preimage_image_eq A Subtype.val_injective).symm]
    exact hImg.preimage continuous_subtype_val
  haveI : CompactSpace ↥T := isCompact_iff_compactSpace.mp hTcompact
  haveI : Finite ↥T := finite_of_compact_of_discrete
  have hSfin : Finite ↥S :=
    Finite.of_injective (fun p => (⟨x p, by rw [hT]; exact Set.mem_range_self p⟩ : ↥T))
      (fun p q hpq => hxinj (congrArg Subtype.val hpq))
  exact Set.finite_coe_iff.mp hSfin

/-- **Compact subspace lies in a finite subcomplex.** Let `C` be a CW complex in a
Hausdorff space `X`, and let `K ⊆ C` be compact. Then there is a finite subcomplex
`E` of `C` with `K ⊆ E`. -/
theorem compact_subset_finite_subcomplex [CWComplex C] {K : Set X} (hKC : K ⊆ C)
    (hK : IsCompact K) :
    ∃ E : CWComplex.Subcomplex C, CWComplex.Finite (E : Set X) ∧ K ⊆ (E : Set X) := by
  classical
  set S : Set (Σ n, Topology.CWComplex.cell C n) :=
    {p | (CWComplex.openCell (C := C) p.1 p.2 ∩ K).Nonempty} with hS
  have hSfin : S.Finite := finite_cells_meeting_compact (C := C) hKC hK
  set sf : Finset (Σ n, Topology.CWComplex.cell C n) := hSfin.toFinset with hsf
  have key : ∀ p ∈ sf, ∃ F : CWComplex.Subcomplex C,
      CWComplex.Finite (F : Set X) ∧
        CWComplex.closedCell (C := C) p.1 p.2 ⊆ (F : Set X) :=
    fun p _ => closedCell_subset_finite_subcomplex (C := C) p.1 p.2
  let Ef : ↥sf → CWComplex.Subcomplex C := fun p => Classical.choose (key p.1 p.2)
  have hEf : ∀ p : ↥sf, CWComplex.Finite (Ef p : Set X) ∧
      CWComplex.closedCell (C := C) p.1.1 p.1.2 ⊆ (Ef p : Set X) :=
    fun p => Classical.choose_spec (key p.1 p.2)
  obtain ⟨G, hGfin, hGsub⟩ :=
    iUnion_subcomplex_finite sf.attach Ef (fun p _ => (hEf p).1)
  refine ⟨G, hGfin, ?_⟩
  intro x hx
  have hxC : x ∈ C := hKC hx
  rw [← CWComplex.iUnion_openCell_eq_complex (C := C)] at hxC
  simp only [Set.mem_iUnion] at hxC
  obtain ⟨n, j, hxnj⟩ := hxC
  have hpsf : (⟨n, j⟩ : Σ n, Topology.CWComplex.cell C n) ∈ sf := by
    rw [hsf, Set.Finite.mem_toFinset, hS]
    exact ⟨x, hxnj, hx⟩
  have hx_cc : x ∈ CWComplex.closedCell (C := C) n j :=
    CWComplex.openCell_subset_closedCell n j hxnj
  exact (hGsub ⟨⟨n, j⟩, hpsf⟩ (Finset.mem_attach _ _)) ((hEf ⟨⟨n, j⟩, hpsf⟩).2 hx_cc)

end HatcherCW
