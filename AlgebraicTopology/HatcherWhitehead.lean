import Mathlib

/-!
# Hatcher Appendix, Proposition A.2 (Whitehead's characterization of CW complexes)

Hatcher's Proposition A.2 characterizes when a family of maps
`Φ_α : Dⁿ_α → X` into a Hausdorff space are the characteristic maps of a CW
structure: (i) each is injective on the open ball with disjoint open cells whose
union is `X`; (ii) each sphere image lies in finitely many lower-dimensional
cells; (iii) `X` carries the weak topology.

Mathlib's `Topology.CWComplex` class is *defined* by exactly these axioms
(`pairwiseDisjoint'`/`union'` = (i), `mapsTo'` = (ii), `closed'` = (iii)), plus
the data of the characteristic maps as `PartialEquiv`s.  The one place where
Mathlib's class asks for *more* than Hatcher's hypotheses is `continuousOn_symm`:
continuity of the inverse characteristic map.  Hatcher derives this (the "hence a
homeomorphism" in (i)) from compactness of `Dⁿ` and Hausdorffness of `X`.  This
file formalizes that derivation, which is the mathematical content of A.2's
`if` direction over Mathlib's API.
-/

open Metric Set Function Topology

namespace HatcherWhitehead

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- **Hatcher's "hence a homeomorphism".** A characteristic map `f` that is
continuous on the closed unit ball and injective on the open ball, whose open
cell `f '' ball` is disjoint from the image `f '' sphere` of the bounding sphere,
has a continuous inverse on the open cell `f '' ball`.  This is the fact that
Mathlib's CW-complex API takes as the hypothesis `continuousOn_symm`. -/
theorem continuousOn_invFunOn_ball {n : ℕ} (f : (Fin n → ℝ) → X)
    (hcont : ContinuousOn f (closedBall 0 1))
    (hinj : InjOn f (ball 0 1))
    (hdisj : Disjoint (f '' ball 0 1) (f '' sphere 0 1)) :
    ContinuousOn (invFunOn f (ball 0 1)) (f '' ball 0 1) := by
  have : Nonempty (Fin n → ℝ) := ⟨0⟩
  rw [continuousOn_iff_isClosed]
  intro C hC
  refine ⟨f '' (closedBall 0 1 ∩ C), ?_, ?_⟩
  · exact (((isCompact_closedBall 0 1).inter_right hC).image_of_continuousOn
      (hcont.mono inter_subset_left)).isClosed
  · have hL : invFunOn f (ball 0 1) ⁻¹' C ∩ f '' ball 0 1 = f '' (ball 0 1 ∩ C) := by
      ext y
      constructor
      · rintro ⟨hyC, x, hx, rfl⟩
        exact ⟨x, ⟨hx, by rwa [mem_preimage, hinj.leftInvOn_invFunOn hx] at hyC⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hxC⟩, rfl⟩
        exact ⟨by rw [mem_preimage, hinj.leftInvOn_invFunOn hx]; exact hxC, x, hx, rfl⟩
    have hR : f '' (closedBall 0 1 ∩ C) ∩ f '' ball 0 1 = f '' (ball 0 1 ∩ C) := by
      apply subset_antisymm
      · rintro y ⟨⟨x, ⟨hx_cb, hxC⟩, rfl⟩, hyball⟩
        have hxball : x ∈ ball (0 : Fin n → ℝ) 1 := by
          rcases lt_or_eq_of_le (mem_closedBall.mp hx_cb) with h | h
          · exact mem_ball.mpr h
          · exact absurd ⟨x, mem_sphere.mpr h, rfl⟩ (Set.disjoint_left.mp hdisj hyball)
        exact ⟨x, ⟨hxball, hxC⟩, rfl⟩
      · rintro y ⟨x, ⟨hx, hxC⟩, rfl⟩
        exact ⟨⟨x, ⟨ball_subset_closedBall hx, hxC⟩, rfl⟩, ⟨x, hx, rfl⟩⟩
    rw [hL, hR]

/-- **Proposition A.2 (Whitehead's characterization), `if` direction.**
Given a Hausdorff space `X` and a family of characteristic maps `map n i`
(as `PartialEquiv`s with source the open ball) such that:
* `source_eq`/`continuousOn` : each map has source the open ball and is
  continuous on the closed ball;
* `pairwiseDisjoint'` : the open cells are pairwise disjoint;
* `mapsToOpen` : the image of each bounding sphere lies in a finite union of
  open cells of strictly lower dimension (Hatcher's condition (ii));
* `closed'` : `X` has the weak topology (Hatcher's condition (iii));
* `union'` : the closed cells cover `C`;

these maps are the characteristic maps of a CW structure on `C`.  The inverse
continuity `continuousOn_symm` — the only axiom of `CWComplex` not literally
among Hatcher's hypotheses — is *derived* here from Hausdorffness via
`continuousOn_invFunOn_ball`, exactly as in Hatcher's proof. -/
@[reducible]
def mkWhitehead {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X)
    (cell : (n : ℕ) → Type u)
    (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsToOpen : ∀ (n : ℕ) (i : cell n), ∃ I : Π m, Finset (cell m),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), map m j '' ball 0 1))
    (closed' : ∀ (A : Set X), A ⊆ C →
      (∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) → IsClosed A)
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    Topology.CWComplex C where
  cell := cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm n i := by
    have hinj : InjOn (map n i) (ball 0 1) := source_eq n i ▸ (map n i).injOn
    have hdisj : Disjoint (map n i '' ball 0 1) (map n i '' sphere 0 1) := by
      obtain ⟨I, hI⟩ := mapsToOpen n i
      rw [Set.disjoint_left]
      rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzy⟩
      have hmem : map n i z ∈ ⋃ (m < n) (j ∈ I m), map m j '' ball 0 1 := hI hz
      simp only [mem_iUnion] at hmem
      obtain ⟨m, hm, j, _, hyj⟩ := hmem
      have hne : (⟨n, i⟩ : Σ k, cell k) ≠ ⟨m, j⟩ := by
        rintro h; exact absurd (congrArg Sigma.fst h).symm (Nat.ne_of_lt hm)
      exact Set.disjoint_left.mp (pairwiseDisjoint' (mem_univ _) (mem_univ _) hne)
        ⟨x, hx, rfl⟩ (hzy ▸ hyj)
    have hcs := continuousOn_invFunOn_ball (map n i) (continuousOn n i) hinj hdisj
    have htarget : (map n i).target = map n i '' ball 0 1 := by
      rw [← source_eq n i]; exact ((map n i).image_source_eq_target).symm
    have heq : EqOn (map n i).symm (invFunOn (map n i) (ball 0 1))
        (map n i '' ball 0 1) := by
      rintro y ⟨x, hx, rfl⟩
      rw [(map n i).left_inv (by rw [source_eq]; exact hx), hinj.leftInvOn_invFunOn hx]
    rw [htarget]
    exact hcs.congr heq
  pairwiseDisjoint' := pairwiseDisjoint'
  mapsTo' n i := by
    obtain ⟨I, hI⟩ := mapsToOpen n i
    refine ⟨I, hI.mono_right ?_⟩
    gcongr with m hm j hj
    exact ball_subset_closedBall
  closed' := closed'
  union' := union'

end HatcherWhitehead
