import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital

namespace LeanCFC

/-- If `A` is a non-unital `R`-algebra, the `R`-quasispectrum of `a : A` consists of those
`r : R` such that if `r` is invertible (in `R`), then `-(r⁻¹ • a)` is not quasiregular.

The quasispectrum is precisely the spectrum in the unitization when `R` is a
commutative ring. -/
def quasispectrum (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A] [Module R A]
    (a : A) : Set R :=
  {r : R | (hr : IsUnit r) → ¬ IsQuasiregular (-(hr.unit⁻¹ • a))}

local notation "σₙ" => _root_.quasispectrum
open Topology ContinuousMapZero

class NonUnitalContinuousFunctionalCalculus (R : Type*) {A : Type*} (p : outParam (A → Prop))
    [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [TopologicalSemiring R]
    [ContinuousStar R] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  predicate_zero : p 0
  [compactSpace_quasispectrum : ∀ a : A, CompactSpace (σₙ R a)]
  exists_cfc_of_predicate : ∀ a, p a → ∃ φ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A,
    IsClosedEmbedding φ ∧ φ ⟨(ContinuousMap.id R).restrict <| σₙ R a, rfl⟩ = a ∧
      (∀ f, σₙ R (φ f) = Set.range f) ∧ ∀ f, p (φ f)

class ContinuousMapZero.UniqueHom (R A : Type*) [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  eq_of_continuous_of_map_id (s : Set R) [CompactSpace s] [Zero s] (h0 : (0 : s) = (0 : R))
    (φ ψ : C(s, R)₀ →⋆ₙₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (⟨.restrict s <| .id R, h0⟩) = ψ (⟨.restrict s <| .id R, h0⟩)) :
    φ = ψ

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [NonUnitalContinuousFunctionalCalculus R p]

noncomputable def cfcₙHom {a : A} (ha : p a) : C((σₙ R a), R)₀ →⋆ₙₐ[R] A :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose

open scoped Classical in
noncomputable irreducible_def cfcₙ (f : R → R) (a : A) : A :=
  if h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
    then cfcₙHom h.1 ⟨⟨_, h.2.1.restrict⟩, h.2.2⟩
    else 0

end LeanCFC
