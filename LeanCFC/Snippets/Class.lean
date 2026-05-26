module

public import Mathlib.Topology.ContinuousMap.StarOrdered
public import Mathlib.Analysis.CStarAlgebra.Classes

/-! # Developing the `class`

This file hosts the code snippets which appear in the section concerning
the development of the continuous functional calculus as a `class` in Lean.
-/

namespace LeanCFC

namespace Naive

open StarAlgebra elemental in
class ContinuousFunctionalCalculus (R A : Type*) [CStarAlgebra A]
    [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
    [ContinuousStar R] [Algebra R A] [StarModule R A] (a : A) where
  /-- The ⋆-isomorphism underlying the continuous functional calculus for `a : A`. -/
  toStarAlgEquiv : C(spectrum R a, R) ≃⋆ₐ[R] StarAlgebra.elemental R a
  /-- The ⋆-isommorphism sends the identity function on `spectrum R a` to `a`. -/
  map_id : toStarAlgEquiv (.restrict (spectrum R a) (.id R)) = ⟨a, self_mem R a⟩

end Naive


namespace AvoidIsomorphism

open Topology in
class ContinuousFunctionalCalculus (R A : Type*) [CStarAlgebra A]
    [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
    [ContinuousStar R] [Algebra R A] (a : A) where
  /-- The ⋆-homomorphism underlying the continuous functional calculus for `a : A`. -/
  toStarAlgHom : C(spectrum R a, R) →⋆ₐ[R] A
  /-- The ⋆-homomorphism sends the identity function on `spectrum R a` to `a`. -/
  map_id : toStarAlgHom (.restrict (spectrum R a) (.id R)) = a
  /-- The ⋆-homomorphism is a closed embedding. -/
  closedEmbedding : IsClosedEmbedding toStarAlgHom
  /-- The spectrum of the image of any function under the $*$-homomorphism is just
  the range of that function. -/
  map_spectrum (f : C(spectrum R a, R)) : spectrum R (toStarAlgHom f) = Set.range f

end AvoidIsomorphism

namespace BundledPredicate

open Topology in
class ContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Type*))
    [CStarAlgebra A] [CommSemiring R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Algebra R A] where
  toStarAlgHom {a} (ha : p a) : C(spectrum R a, R) →⋆ₐ[R] A
  map_id {a} (ha : p a) : toStarAlgHom ha (.restrict (spectrum R a) (.id R)) = a
  closedEmbedding {a} (ha : p a) : IsClosedEmbedding (toStarAlgHom ha)
  map_spectrum {a} (ha : p a) (f : C(spectrum R a, R)) :
    spectrum R (toStarAlgHom ha f) = Set.range f
  predicate_preserving {a} (ha : p a) (f : C(spectrum R a, R)) : p (toStarAlgHom ha f)

end BundledPredicate

namespace RemoveCStarAlgebra

open Topology in
class ContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Type*))
    [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
    [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A] where
  toStarAlgHom {a} (ha : p a) : C(spectrum R a, R) →⋆ₐ[R] A
  map_id {a} (ha : p a) : toStarAlgHom ha (.restrict (spectrum R a) (.id R)) = a
  closedEmbedding {a} (ha : p a) : IsClosedEmbedding (toStarAlgHom ha)
  map_spectrum {a} (ha : p a) (f : C(spectrum R a, R)) :
    spectrum R (toStarAlgHom ha f) = Set.range f
  predicate_preserving {a} (ha : p a) (f : C(spectrum R a, R)) : p (toStarAlgHom ha f)

end RemoveCStarAlgebra

namespace OmitData

open Topology in
class ContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Prop))
    [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
    [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] : Prop where
  predicate_zero : p 0
  [compactSpace_spectrum (a : A) : CompactSpace (spectrum R a)]
  spectrum_nonempty [Nontrivial A] (a : A) (ha : p a) : (spectrum R a).Nonempty
  exists_cfc_of_predicate : ∀ a, p a → ∃ φ : C(spectrum R a, R) →⋆ₐ[R] A,
    IsClosedEmbedding φ ∧ φ ((ContinuousMap.id R).restrict <| spectrum R a) = a ∧
      (∀ f, spectrum R (φ f) = Set.range f) ∧ ∀ f, p (φ f)

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
variable [Algebra R A] [ContinuousFunctionalCalculus R A p]

noncomputable def cfcHom {a : A} (ha : p a) : C(spectrum R a, R) →⋆ₐ[R] A :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose

open scoped Classical in
noncomputable irreducible_def cfc (f : R → R) (a : A) : A :=
  if h : p a ∧ ContinuousOn f (spectrum R a)
    then cfcHom h.1 ⟨_, h.2.restrict⟩
    else 0

end OmitData

end LeanCFC
