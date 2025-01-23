import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

namespace LeanCFC

theorem cfc_le_iff {R : Type u} {A : Type*} {p : A → Prop} [OrderedCommRing R]
    [StarRing R] [MetricSpace R] [TopologicalRing R] [ContinuousStar R]
    [∀ (α : Type u) [TopologicalSpace α], StarOrderedRing C(α, R)]
    [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Algebra R A] [ContinuousFunctionalCalculus R p]
    [NonnegSpectrumClass R A] (f g : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) :
    cfc f a ≤ cfc g a ↔ ∀ x ∈ spectrum R a, f x ≤ g x :=
  _root_.cfc_le_iff f g a hf hg ha

end LeanCFC
