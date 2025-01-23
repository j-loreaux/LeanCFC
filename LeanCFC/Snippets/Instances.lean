import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Restrict

namespace LeanCFC

/-- Given an element `a : A` of an `S`-algebra, where `S` is itself an `R`-algebra, we say
that the spectrum of `a` restricts via a function `f : S → R` if `f` is a left inverse of
`algebraMap R S`, and `f` is a right inverse of `algebraMap R S` on `spectrum S a`.

For example, when `f = Complex.re` (so `S := ℂ` and `R := ℝ`), `SpectrumRestricts a f`
means that the `ℂ`-spectrum of `a` is contained within `ℝ`. This arises naturally when
`a` is selfadjoint and `A` is a C⋆-algebra.  -/
structure QuasispectrumRestricts {R S A : Type*} [CommSemiring R] [CommSemiring S]
    [NonUnitalRing A] [Module R A] [Module S A] [Algebra R S] (a : A) (f : S → R) : Prop where
  /-- `f` is a right inverse of `algebraMap R S` when restricted to `quasispectrum S a`. -/
  rightInvOn : (quasispectrum S a).RightInvOn f (algebraMap R S)
  /-- `f` is a left inverse of `algebraMap R S`. -/
  left_inv : Function.LeftInverse f (algebraMap R S)

/-- Given a `ContinuousFunctionalCalculus S q`. If we form the predicate `p` for `a : A`
characterized by: `q a` and the spectrum of `a` restricts to the scalar subring `R` via
`f : C(S, R)`, then we can get a restricted functional calculus
`ContinuousFunctionalCalculus R p`. -/
theorem SpectrumRestricts.cfc {R S A : Type*} {p q : A → Prop} [Semifield R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [Semifield S] [StarRing S]
    [MetricSpace S] [TopologicalSemiring S] [ContinuousStar S] [Ring A] [StarRing A]
    [Algebra S A] [Algebra R S] [Algebra R A] [IsScalarTower R S A] [StarModule R S]
    [ContinuousSMul R S] [TopologicalSpace A] [ContinuousFunctionalCalculus S q]
    [CompleteSpace R] (f : C(S, R)) (halg : IsUniformEmbedding ⇑(algebraMap R S))
    (h0 : p 0) (h : ∀ (a : A), p a ↔ q a ∧ SpectrumRestricts a ⇑f) :
    ContinuousFunctionalCalculus R p :=
  sorry

end LeanCFC
