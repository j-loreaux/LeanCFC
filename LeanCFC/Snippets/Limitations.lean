module public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

namespace LeanCFC

theorem cfc_le_iff {R A : Type*} {p : A → Prop} [CommRing R] [PartialOrder R]
    [StarRing R] [MetricSpace R] [IsTopologicalRing R] [ContinuousStar R]
    [ContinuousSqrt R] [StarOrderedRing R] [TopologicalSpace A]
    [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra R A]
    [instCFC : ContinuousFunctionalCalculus R A p] [NonnegSpectrumClass R A]
    (f g : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) :
    cfc f a ≤ cfc g a ↔ ∀ x ∈ spectrum R a, f x ≤ g x :=
  _root_.cfc_le_iff f g a hf hg ha

end LeanCFC
