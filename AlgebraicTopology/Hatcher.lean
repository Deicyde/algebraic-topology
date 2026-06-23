import Mathlib

/-!
# Hatcher Appendix: The Compact-Open Topology

Formalization of the core point-set results about the compact-open topology
from the Appendix of Hatcher's *Algebraic Topology* (Propositions A.13, A.14,
A.16).

Throughout, `C(Y, X)` denotes the space of continuous maps `Y → X` equipped with
the compact-open topology (`ContinuousMap.compactOpen`).

Most of these statements already exist in Mathlib in some form; the declarations
below restate them faithfully to the blueprint phrasing. See the per-declaration
notes recorded in the blueprint metadata for the corresponding Mathlib results.
-/

open scoped Topology

namespace Hatcher

/-! ## Uniform convergence (Proposition A.13) -/

/-- **Pointwise bound on distance.** For a compact domain `X` and metric codomain
`Y`, the distance between `f, g : C(X, Y)` is `≤ C` (for `0 ≤ C`) iff every
pointwise distance is `≤ C`. (Mathlib: `ContinuousMap.dist_le`.) -/
theorem dist_le {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MetricSpace Y]
    (f g : C(X, Y)) {C : ℝ} (hC : 0 ≤ C) :
    dist f g ≤ C ↔ ∀ x : X, dist (f x) (g x) ≤ C :=
  ContinuousMap.dist_le hC

/-- **Compact-open topology is uniform convergence.** For a compact domain `X`
and metric codomain `Y`, the metric on `C(X, Y)` (which induces the compact-open
topology) is the pointwise supremum distance. (Mathlib: `ContinuousMap.dist_eq_iSup`.)

Note: the blueprint assumes `X` nonempty, but the supremum formulation holds
unconditionally (both sides are `0` when `X` is empty), so we omit that hypothesis. -/
theorem dist_eq_iSup {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MetricSpace Y]
    (f g : C(X, Y)) : dist f g = ⨆ x : X, dist (f x) (g x) :=
  ContinuousMap.dist_eq_iSup

/-! ## Evaluation and the exponential law (Proposition A.14) -/

/-- **Continuity of evaluation.** If `Y` is locally compact, the evaluation map
`C(Y, X) × Y → X`, `(f, y) ↦ f y`, is continuous. (Mathlib provides this through
the `ContinuousEval` instance `ContinuousMap.instContinuousEvalOfLocallyCompactPair`.) -/
theorem eval_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace Y] : Continuous fun p : C(Y, X) × Y => p.1 p.2 :=
  continuous_eval

/-- **Uncurrying a continuous map is continuous.** If `Y` is locally compact and
`F : Z → C(Y, X)` is continuous, then the uncurried map `(z, y) ↦ F z y` is
continuous. (Compare `ContinuousMap.continuous_uncurry_of_continuous`.) -/
theorem uncurry_continuous {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [LocallyCompactSpace Y] (F : Z → C(Y, X)) (hF : Continuous F) :
    Continuous (Function.uncurry fun z y => F z y) := by
  let f : C(Z, C(Y, X)) := ⟨F, hF⟩
  simpa [f] using ContinuousMap.continuous_uncurry_of_continuous f

/-- **Currying a continuous map is continuous.** To prove a map `F : Z → C(Y, X)`
is continuous it suffices that its uncurried form `(z, y) ↦ F z y` is continuous;
no local compactness hypothesis is needed.
(Mathlib: `ContinuousMap.continuous_of_continuous_uncurry`.) -/
theorem curry_continuous {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (F : Z → C(Y, X))
    (hF : Continuous (Function.uncurry fun z y => F z y)) : Continuous F :=
  ContinuousMap.continuous_of_continuous_uncurry F hF

/-- **Exponential law.** If `Y` is locally compact, a map `F : Z → C(Y, X)` is
continuous iff its uncurried form `(z, y) ↦ F z y` is continuous. -/
theorem exponential_law {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [LocallyCompactSpace Y] (F : Z → C(Y, X)) :
    Continuous (Function.uncurry fun z y => F z y) ↔ Continuous F :=
  ⟨curry_continuous F, uncurry_continuous F⟩

/-! ## Currying as a homeomorphism (Proposition A.16) -/

/-- **Currying is continuous.** If `Y` and `Z` are locally compact, the currying
map `C(Y × Z, X) → C(Y, C(Z, X))` is continuous.
(Compare `ContinuousMap.continuous_curry`.) -/
theorem continuous_curry {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [LocallyCompactSpace Y] [LocallyCompactSpace Z] :
    Continuous (ContinuousMap.curry : C(Y × Z, X) → C(Y, C(Z, X))) :=
  ContinuousMap.continuous_curry

/-- **Uncurrying is continuous.** If `Y` and `Z` are locally compact, the
uncurrying map `C(Y, C(Z, X)) → C(Y × Z, X)` is continuous.
(Mathlib: `ContinuousMap.continuous_uncurry`.) -/
theorem continuous_uncurry {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [LocallyCompactSpace Y] [LocallyCompactSpace Z] :
    Continuous (ContinuousMap.uncurry : C(Y, C(Z, X)) → C(Y × Z, X)) :=
  ContinuousMap.continuous_uncurry

/-- **Currying homeomorphism.** If `Y` and `Z` are locally compact, currying is a
homeomorphism `C(Y × Z, X) ≃ₜ C(Y, C(Z, X))`, with inverse uncurrying.
(Mathlib: `Homeomorph.curry`.) -/
noncomputable def curryHomeo {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [LocallyCompactSpace Y] [LocallyCompactSpace Z] :
    C(Y × Z, X) ≃ₜ C(Y, C(Z, X)) :=
  Homeomorph.curry (X := Y) (Y := Z) (Z := X)

end Hatcher
