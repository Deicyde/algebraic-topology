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

open Topology Metric Set

namespace HatcherNormal

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C : Set X}

/-- **Hatcher's `N_ε(A)` construction, skeleton by skeleton.**
Given a subset `A` and a positive radius `ε n i` for each cell, `Nbhd A ε n` is
the neighborhood built on the `n`-skeleton. It starts as `A ∩ X⁰` on the
`0`-skeleton and, at stage `n+1`, adjoins on each `(n+1)`-cell the image under the
characteristic map of the union of an open `ε`-thickening of the preimage of `A`
and the spherical collar `1 - ε < ‖y‖` whose angular coordinate `‖y‖⁻¹ • y` is
sent by the attaching map into the previous-stage neighborhood. The full
neighborhood is `⋃ n, Nbhd A ε n` (see `Nbhd_iUnion`). -/
def Nbhd [CWComplex C] (A : Set X) (ε : ∀ n, Topology.CWComplex.cell C n → ℝ) :
    ℕ → Set X
  | 0 => A ∩ Topology.CWComplex.skeleton C 0
  | (n + 1) =>
      Nbhd A ε n ∪ ⋃ i : Topology.CWComplex.cell C (n + 1),
        Topology.CWComplex.map (n + 1) i ''
          { y : Fin (n + 1) → ℝ | y ∈ ball 0 1 ∧
              (y ∈ thickening (ε (n + 1) i)
                    ((Topology.CWComplex.map (n + 1) i ⁻¹' A) ∩ ball 0 1)
               ∨ (1 - ε (n + 1) i < ‖y‖ ∧
                    Topology.CWComplex.map (n + 1) i (‖y‖⁻¹ • y) ∈ Nbhd A ε n)) }

/-- The full Hatcher neighborhood `N_ε(A) = ⋃ₙ N_ε^n(A)`. -/
def NbhdUnion [CWComplex C] (A : Set X) (ε : ∀ n, Topology.CWComplex.cell C n → ℝ) :
    Set X :=
  ⋃ n, Nbhd A ε n

/-- Each stage of the construction lies in the corresponding skeleton: the image
of a subset of the open ball lands in the open cell, hence in the `(n+1)`-skeleton,
while the previous stage lies in the `n`-skeleton. -/
theorem Nbhd_subset_skeleton [CWComplex C] (A : Set X)
    (ε : ∀ n, Topology.CWComplex.cell C n → ℝ) (n : ℕ) :
    Nbhd A ε n ⊆ Topology.CWComplex.skeleton C n := by
  induction n with
  | zero => exact inter_subset_right
  | succ n ih =>
    simp only [Nbhd]
    refine union_subset
      (ih.trans (Topology.CWComplex.skeleton_monotone (by exact_mod_cast n.le_succ)))
      (iUnion_subset fun i => ?_)
    exact (Set.image_mono fun y hy => hy.1).trans
      (Topology.CWComplex.openCell_subset_skeleton (C := C) (n + 1) i)

/-- The construction contains `A`: every point of `A` lies in some open cell, and
the corresponding ball preimage sits in the `ε`-thickening of `map ⁻¹' A` (for
positive `ε`), hence in that stage of the construction. -/
theorem subset_NbhdUnion [CWComplex C] {A : Set X} (hAC : A ⊆ C)
    (ε : ∀ n, Topology.CWComplex.cell C n → ℝ) (hε : ∀ n i, 0 < ε n i) :
    A ⊆ NbhdUnion A ε := by
  intro a ha
  have haC : a ∈ C := hAC ha
  rw [← Topology.CWComplex.iUnion_openCell_eq_complex (C := C)] at haC
  simp only [mem_iUnion] at haC
  obtain ⟨n, i, hni⟩ := haC
  refine mem_iUnion.mpr ?_
  rcases n with _ | m
  · exact ⟨0, ha, Topology.CWComplex.openCell_subset_skeleton (C := C) 0 i hni⟩
  · obtain ⟨p, hp_ball, rfl⟩ := hni
    refine ⟨m + 1, ?_⟩
    simp only [Nbhd]
    refine Set.mem_union_right _ (mem_iUnion.mpr ⟨i, ⟨p, ⟨hp_ball, Or.inl ?_⟩, rfl⟩⟩)
    exact Metric.self_subset_thickening (hε (m + 1) i) _ ⟨ha, hp_ball⟩

/-- **Openness of the neighborhood.** `N_ε(A)` is open as a subset of the subspace
`C`: by the weak topology it suffices that it pulls back to an open set under each
characteristic map, and the cell-wise description is an open `ε`-thickening unioned
with the open spherical collar (`HatcherNeighborhood.isOpen_collarSlice`). The
inductive openness over the skeleta is the remaining work. -/
theorem isOpen_NbhdUnion [CWComplex C] (A : Set X)
    (ε : ∀ n, Topology.CWComplex.cell C n → ℝ) :
    IsOpen (Subtype.val ⁻¹' NbhdUnion A ε : Set C) := by
  sorry

/-- **Separation by small radii.** For disjoint sets `A, B` that are closed in `C`,
the cell-wise radii can be chosen positive and small enough that the two
neighborhoods are disjoint. The choice is made by induction over the skeleta:
assuming `N_ε^n(A)` and `N_ε^n(B)` disjoint, on each `(n+1)`-cell the preimages of
`N_ε^n(A)` and of `B` (and symmetrically), and of `A` and `B`, are disjoint compact
sets, so `HatcherNeighborhood.exists_eps_separating_thickenings` supplies a positive
`ε_{n+1,i}` keeping the next stage disjoint. -/
theorem exists_eps_disjoint [CWComplex C] {A B : Set X}
    (hA : IsClosed (Subtype.val ⁻¹' A : Set C))
    (hB : IsClosed (Subtype.val ⁻¹' B : Set C)) (hAB : Disjoint A B) :
    ∃ ε : ∀ n, Topology.CWComplex.cell C n → ℝ,
      (∀ n i, 0 < ε n i) ∧ Disjoint (NbhdUnion A ε) (NbhdUnion B ε) := by
  sorry

/-- **Separating neighborhoods of disjoint closed sets.** For any two disjoint
subsets `A, B` of the subspace `C` that are closed in `C`, there exist disjoint
open neighborhoods, i.e. `SeparatedNhds A B`. This is the inductive
neighborhood construction `Nε(A)`, `Nε(B)` over the skeleta of the CW complex. -/
theorem exists_disjoint_nhds [CWComplex C] {A B : Set ↥C}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    SeparatedNhds A B := by
  set A' : Set X := Subtype.val '' A with hA'def
  set B' : Set X := Subtype.val '' B with hB'def
  have hA'C : A' ⊆ C := Subtype.coe_image_subset C A
  have hB'C : B' ⊆ C := Subtype.coe_image_subset C B
  have hpreA : Subtype.val ⁻¹' A' = A := Set.preimage_image_eq A Subtype.val_injective
  have hpreB : Subtype.val ⁻¹' B' = B := Set.preimage_image_eq B Subtype.val_injective
  have hclA : IsClosed (Subtype.val ⁻¹' A' : Set C) := by rw [hpreA]; exact hA
  have hclB : IsClosed (Subtype.val ⁻¹' B' : Set C) := by rw [hpreB]; exact hB
  have hdisjAB : Disjoint A' B' :=
    Set.disjoint_image_of_injective Subtype.val_injective hAB
  obtain ⟨ε, hεpos, hεdisj⟩ := exists_eps_disjoint hclA hclB hdisjAB
  refine ⟨Subtype.val ⁻¹' NbhdUnion A' ε, Subtype.val ⁻¹' NbhdUnion B' ε,
    isOpen_NbhdUnion A' ε, isOpen_NbhdUnion B' ε, ?_, ?_, hεdisj.preimage Subtype.val⟩
  · rw [← hpreA]; exact Set.preimage_mono (subset_NbhdUnion hA'C ε hεpos)
  · rw [← hpreB]; exact Set.preimage_mono (subset_NbhdUnion hB'C ε hεpos)

/-- **CW complexes are normal.** The subspace `C` of a CW complex in a Hausdorff
space `X` is a normal topological space. -/
theorem normalSpace [CWComplex C] : NormalSpace ↥C :=
  ⟨fun _ _ hA hB hAB => exists_disjoint_nhds hA hB hAB⟩

end HatcherNormal
