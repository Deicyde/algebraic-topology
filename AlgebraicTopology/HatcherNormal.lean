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

/-- The stages of the construction are monotone in the skeleton index. -/
theorem Nbhd_mono [CWComplex C] (A : Set X)
    (ε : ∀ n, Topology.CWComplex.cell C n → ℝ) : Monotone (Nbhd A ε) :=
  monotone_nat_of_le_succ fun n x hx => by
    simp only [Nbhd]; exact Set.mem_union_left _ hx

/-- **Locality of the construction.** The stage `Nbhd A ε k` only consults `ε` at
dimensions `≤ k`: two radius assignments agreeing up to dimension `k` give the same
stage. This breaks the circularity when building `ε` by recursion over the skeleta. -/
theorem Nbhd_congr [CWComplex C] (A : Set X)
    {ε ε' : ∀ n, Topology.CWComplex.cell C n → ℝ} :
    ∀ k, (∀ n, n ≤ k → ε n = ε' n) → Nbhd A ε k = Nbhd A ε' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    have hNbhd : Nbhd A ε k = Nbhd A ε' k :=
      ih fun n hn => h n (hn.trans (Nat.le_succ k))
    have hek1 : ε (k + 1) = ε' (k + 1) := h (k + 1) le_rfl
    simp only [Nbhd]
    rw [hNbhd, hek1]

/-- Disjointness of the full neighborhoods reduces to disjointness at every stage,
using monotonicity: any two stages are dominated by their maximum. -/
theorem disjoint_NbhdUnion_of_forall [CWComplex C] {A B : Set X}
    {ε : ∀ n, Topology.CWComplex.cell C n → ℝ}
    (h : ∀ k, Disjoint (Nbhd A ε k) (Nbhd B ε k)) :
    Disjoint (NbhdUnion A ε) (NbhdUnion B ε) := by
  rw [NbhdUnion, NbhdUnion, Set.disjoint_iUnion_left]
  intro n
  rw [Set.disjoint_iUnion_right]
  intro m
  rcases le_total n m with hnm | hmn
  · exact (h m).mono_left (Nbhd_mono A ε hnm)
  · exact (h n).mono_right (Nbhd_mono B ε hmn)

/-- A lower stage (living in the `k`-skeleton) is disjoint from any image of a
subset of the open ball under a `(k+1)`-cell characteristic map (which lives in the
open `(k+1)`-cell, disjoint from the `k`-skeleton). This is the `ε`-free part of the
inductive disjointness step. -/
theorem Nbhd_disjoint_image_succ [CWComplex C] (A : Set X)
    (ε : ∀ n, Topology.CWComplex.cell C n → ℝ) (k : ℕ)
    {S : Set (Fin (k + 1) → ℝ)} (hS : S ⊆ ball 0 1)
    (i : Topology.CWComplex.cell C (k + 1)) :
    Disjoint (Nbhd A ε k) (Topology.CWComplex.map (k + 1) i '' S) := by
  have himg : Topology.CWComplex.map (k + 1) i '' S
      ⊆ Topology.CWComplex.map (k + 1) i '' ball 0 1 := Set.image_mono hS
  have hdisj : Disjoint (↑(Topology.CWComplex.skeleton C (k : ℕ∞)) : Set X)
      (Topology.CWComplex.map (k + 1) i '' ball 0 1) :=
    Topology.CWComplex.disjoint_skeleton_openCell (C := C) (n := (k : ℕ∞)) (j := i)
      (by exact_mod_cast Nat.lt_succ_self k)
  exact hdisj.mono (Nbhd_subset_skeleton A ε k) himg

/-- The per-cell source set adjoined on an `(k+1)`-cell at stage `k+1`: the open
`ε`-thickening of `map ⁻¹' A` together with the spherical collar referring to the
previous stage. -/
def cellSource [CWComplex C] (A : Set X) (ε : ∀ n, Topology.CWComplex.cell C n → ℝ)
    (k : ℕ) (i : Topology.CWComplex.cell C (k + 1)) : Set (Fin (k + 1) → ℝ) :=
  { y : Fin (k + 1) → ℝ | y ∈ ball 0 1 ∧
      (y ∈ thickening (ε (k + 1) i)
            ((Topology.CWComplex.map (k + 1) i ⁻¹' A) ∩ ball 0 1)
       ∨ (1 - ε (k + 1) i < ‖y‖ ∧
            Topology.CWComplex.map (k + 1) i (‖y‖⁻¹ • y) ∈ Nbhd A ε k)) }

theorem cellSource_subset_ball [CWComplex C] (A : Set X)
    (ε : ∀ n, Topology.CWComplex.cell C n → ℝ) (k : ℕ)
    (i : Topology.CWComplex.cell C (k + 1)) : cellSource A ε k i ⊆ ball 0 1 :=
  fun _ hy => hy.1

theorem Nbhd_succ_eq [CWComplex C] (A : Set X)
    (ε : ∀ n, Topology.CWComplex.cell C n → ℝ) (k : ℕ) :
    Nbhd A ε (k + 1) = Nbhd A ε k ∪
      ⋃ i, Topology.CWComplex.map (k + 1) i '' cellSource A ε k i := rfl

/-- **Inductive disjointness step, modulo the per-cell condition.** Given the
previous stages disjoint and, on each `(k+1)`-cell, the two in-disk source sets
disjoint, the next stages are disjoint. The proof splits the four cross-terms:
the previous stages (hypothesis), a previous stage against new cells (disjoint
skeleton vs open cells), and new cells against new cells — equal cells via
injectivity of the characteristic map on the ball, distinct cells via
disjointness of open cells. The remaining work is to choose `ε` realizing the
per-cell hypothesis. -/
theorem disjoint_Nbhd_succ [CWComplex C] {A B : Set X}
    {ε : ∀ n, Topology.CWComplex.cell C n → ℝ} {k : ℕ}
    (ih : Disjoint (Nbhd A ε k) (Nbhd B ε k))
    (hcell : ∀ i, Disjoint (cellSource A ε k i) (cellSource B ε k i)) :
    Disjoint (Nbhd A ε (k + 1)) (Nbhd B ε (k + 1)) := by
  rw [Nbhd_succ_eq, Nbhd_succ_eq, Set.disjoint_union_left, Set.disjoint_union_right,
    Set.disjoint_union_right]
  refine ⟨⟨ih, ?_⟩, ?_, ?_⟩
  · rw [Set.disjoint_iUnion_right]
    exact fun i => Nbhd_disjoint_image_succ A ε k (cellSource_subset_ball B ε k i) i
  · rw [Set.disjoint_iUnion_left]
    exact fun i => (Nbhd_disjoint_image_succ B ε k (cellSource_subset_ball A ε k i) i).symm
  · rw [Set.disjoint_iUnion_left]
    intro i
    rw [Set.disjoint_iUnion_right]
    intro j
    rcases eq_or_ne i j with rfl | hij
    · have hinj : Set.InjOn (Topology.CWComplex.map (k + 1) i) (ball 0 1) :=
        Topology.CWComplex.source_eq (k + 1) i ▸ (Topology.CWComplex.map (k + 1) i).injOn
      rw [Set.disjoint_left]
      rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have hab' : a = b :=
        hinj (cellSource_subset_ball A ε k i ha) (cellSource_subset_ball B ε k i hb) hab.symm
      exact (Set.disjoint_left.mp (hcell i)) ha (hab' ▸ hb)
    · have hne : (⟨k + 1, i⟩ : Σ n, Topology.CWComplex.cell C n) ≠ ⟨k + 1, j⟩ := by
        rintro h; exact hij (by simpa using h)
      have hd : Disjoint (Topology.CWComplex.map (k + 1) i '' ball 0 1)
          (Topology.CWComplex.map (k + 1) j '' ball 0 1) :=
        Topology.CWComplex.disjoint_openCell_of_ne (C := C) hne
      exact hd.mono (Set.image_mono (cellSource_subset_ball A ε k i))
        (Set.image_mono (cellSource_subset_ball B ε k j))

/-- **Openness of the neighborhood.** `N_ε(A)` is open as a subset of the subspace
`C`: by the weak topology it suffices that it pulls back to an open set under each
characteristic map, and the cell-wise description is an open `ε`-thickening unioned
with the open spherical collar (`HatcherNeighborhood.isOpen_collarSlice`). The
inductive openness over the skeleta is the remaining work. -/
theorem isOpen_NbhdUnion [CWComplex C] (A : Set X)
    (ε : ∀ n, Topology.CWComplex.cell C n → ℝ) :
    IsOpen (Subtype.val ⁻¹' NbhdUnion A ε : Set C) := by
  sorry

/-- The collar parts of the two cell source sets are disjoint, purely because the
previous stage is disjoint: a point in both collars has the same angular coordinate
`‖y‖⁻¹ • y`, which would then be mapped into both `Nbhd A ε k` and `Nbhd B ε k`. -/
theorem disjoint_collar [CWComplex C] {A B : Set X}
    {ε : ∀ n, Topology.CWComplex.cell C n → ℝ} {k : ℕ}
    (ih : Disjoint (Nbhd A ε k) (Nbhd B ε k))
    (i : Topology.CWComplex.cell C (k + 1)) :
    Disjoint
      {y : Fin (k + 1) → ℝ | 1 - ε (k + 1) i < ‖y‖ ∧
        Topology.CWComplex.map (k + 1) i (‖y‖⁻¹ • y) ∈ Nbhd A ε k}
      {y : Fin (k + 1) → ℝ | 1 - ε (k + 1) i < ‖y‖ ∧
        Topology.CWComplex.map (k + 1) i (‖y‖⁻¹ • y) ∈ Nbhd B ε k} := by
  rw [Set.disjoint_left]
  rintro y ⟨_, hyA⟩ ⟨_, hyB⟩
  exact Set.disjoint_left.mp ih hyA hyB

/-- The preimage of a set closed in `C` intersected with the closed ball is
compact: `C` is closed in the Hausdorff space `X`, so the set is closed in `X`,
and its intersection with the (compact) closed ball is a closed subset. This
provides the disjoint compact sets that feed the thickening-separation engine. -/
theorem isCompact_preimage_inter_closedBall [CWComplex C] {A : Set X}
    (hA : IsClosed (Subtype.val ⁻¹' A : Set C)) (k : ℕ)
    (i : Topology.CWComplex.cell C (k + 1)) :
    IsCompact (Topology.CWComplex.map (k + 1) i ⁻¹' A ∩ closedBall 0 1) := by
  obtain ⟨F, hFcl, hFA⟩ := isClosed_induced_iff.mp hA
  have hmapC : ∀ x ∈ closedBall (0 : Fin (k + 1) → ℝ) 1,
      Topology.CWComplex.map (k + 1) i x ∈ C :=
    fun x hx => Topology.CWComplex.closedCell_subset_complex (k + 1) i ⟨x, hx, rfl⟩
  have heq : Topology.CWComplex.map (k + 1) i ⁻¹' A ∩ closedBall 0 1
      = closedBall 0 1 ∩ Topology.CWComplex.map (k + 1) i ⁻¹' F := by
    ext x
    refine ⟨fun hx => ⟨hx.2, (Set.ext_iff.mp hFA ⟨_, hmapC x hx.2⟩).mpr hx.1⟩,
      fun hx => ⟨(Set.ext_iff.mp hFA ⟨_, hmapC x hx.1⟩).mp hx.2, hx.1⟩⟩
  rw [heq]
  have hcl : IsClosed (closedBall (0 : Fin (k + 1) → ℝ) 1
      ∩ Topology.CWComplex.map (k + 1) i ⁻¹' F) :=
    (Topology.CWComplex.continuousOn (k + 1) i).preimage_isClosed_of_isClosed
      isClosed_closedBall hFcl
  exact (isCompact_closedBall 0 1).of_isClosed_subset hcl Set.inter_subset_left

/-- **The remaining crux: choosing the radii.** For disjoint sets closed in `C`
there is a positive cell-wise radius assignment making, at every stage and every
cell, the two in-disk source sets disjoint. This is Hatcher's "small enough
`ε_α`", constructed by recursion over the skeleta: on each cell the radius is chosen
via `HatcherNeighborhood.exists_eps_separating_thickenings` applied to the disjoint
compact preimages, the collar parts being disjoint by the previous stage. This is
the one analytic/recursive obligation left in the normality proof. -/
theorem exists_eps_cellwise_disjoint [CWComplex C] {A B : Set X}
    (hA : IsClosed (Subtype.val ⁻¹' A : Set C))
    (hB : IsClosed (Subtype.val ⁻¹' B : Set C)) (hAB : Disjoint A B) :
    ∃ ε : ∀ n, Topology.CWComplex.cell C n → ℝ, (∀ n i, 0 < ε n i) ∧
      ∀ k i, Disjoint (cellSource A ε k i) (cellSource B ε k i) := by
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
  -- Reduce to a positive `ε` realizing the per-cell, in-disk disjointness at every
  -- stage; the global disjointness then follows by the stagewise induction
  -- (`disjoint_Nbhd_succ`) and `disjoint_NbhdUnion_of_forall`.
  obtain ⟨ε, hpos, hcell⟩ :
      ∃ ε : ∀ n, Topology.CWComplex.cell C n → ℝ, (∀ n i, 0 < ε n i) ∧
        ∀ k i, Disjoint (cellSource A ε k i) (cellSource B ε k i) :=
    exists_eps_cellwise_disjoint hA hB hAB
  refine ⟨ε, hpos, disjoint_NbhdUnion_of_forall (fun k => ?_)⟩
  induction k with
  | zero => simp only [Nbhd]; exact hAB.mono inter_subset_left inter_subset_left
  | succ k ih => exact disjoint_Nbhd_succ ih (hcell k)

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
