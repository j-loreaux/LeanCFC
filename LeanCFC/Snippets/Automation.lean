module public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

local notation "σₙ" => quasispectrum

namespace LeanCFC

theorem cfcₙ_map_quasispectrum {R A : Type*} {p : A → Prop} [CommSemiring R]
    [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
    [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [instCFCₙ : NonUnitalContinuousFunctionalCalculus R A p]
    (f : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    σₙ R (cfcₙ f a) = f '' σₙ R a := by
  simp [cfcₙ_apply f a, cfcₙHom_map_quasispectrum (p := p)]


open NNReal in
example {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {b : A} (hb : IsSelfAdjoint b) :
    σₙ ℝ≥0 (cfcₙ sqrt (b * b)) = sqrt '' σₙ ℝ≥0 (b * b) :=
  cfcₙ_map_quasispectrum _ _

lemma IsSelfAdjoint.mul_self_nonneg {R : Type*} [NonUnitalSemiring R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] {a : R} (ha : IsSelfAdjoint a) : 0 ≤ a * a :=
  _root_.IsSelfAdjoint.mul_self_nonneg ha

open NNReal in
lemma NNReal.sqrt_zero : sqrt 0 = 0 :=
  _root_.NNReal.sqrt_zero

example {A : Type*} [CStarAlgebra A] {a : A} [IsStarNormal a]
    (f g : ℂ → ℂ) (hf : Continuous f) (hf : Continuous g) :
    cfc f (cfc g a) + cfc ((2 : ℂ) * ·) (cfc g a) * cfc (f ∘ g) a =
      cfc (fun x ↦ f (g x) + 2 * (g x) * f (g x)) a := by
  rw [← cfc_comp _ _ _, ← cfc_comp _ _ _, ← cfc_mul _ _ _, ← cfc_add _ _ _]
  congr! 1

end LeanCFC
