import Mathlib
open scoped NNReal
noncomputable section

/-! # Litmus test for square roots of nonnegative elements

There is already a `CFC.sqrt` declaration in Mathlib, but we don't copy the relevant
file here because that file contains many other declarations about real powers of
nonnegative elements. Although we could do this with more general type class
assumptions (as is done in Mathlib), here we opt for `NonUnitalCStarAlgebra` for
simplicity and readability, and to show that it indeed works!

Goal: For a nonnegative element `a` in a non-unital C⋆-algebra, there is a unique
nonnegative element `sqrt a` so that `sqrt a * sqrt a = a`.
-/

namespace LeanCFC

variable {A : Type*}

section NonUnital

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/- Because of the junk values for `cfcₙ`, if `a` is not nonnegative, then `sqrt a = 0`. -/
def sqrt (a : A) : A := cfcₙ NNReal.sqrt a

/- Note that we don't need to assume `0 ≤ a` here, again because of junk values. -/
lemma sqrt_nonneg (a : A) : 0 ≤ sqrt a := cfcₙ_nonneg_of_predicate

/- When `0 ≤ a`, then `sqrt a` is indeed a square root. -/
lemma sqrt_mul_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) :
    sqrt a * sqrt a = a := by
  simp [sqrt, ← cfcₙ_mul NNReal.sqrt NNReal.sqrt a, cfcₙ_id' ℝ≥0 a]

/- Uniqueness of the square root. If `0 ≤ b` is any other square root of `a`, then
`sqrt a = b`. -/
lemma sqrt_eq_of_mul_self_eq (a b : A) (hab : b * b = a) (hb : 0 ≤ b := by cfc_tac) :
    sqrt a = b := by
  rw [← cfcₙ_id' ℝ≥0 b, ← cfcₙ_mul ..] at hab
  rw [sqrt, ← hab, ← cfcₙ_comp' ..]
  simp [cfcₙ_id' ℝ≥0 b]

/- The square root of a square of a nonnegative element is itself. -/
lemma sqrt_mul_self (a : A) (ha : 0 ≤ a := by cfc_tac) :
    sqrt (a * a) = a :=
  sqrt_eq_of_mul_self_eq _ _ rfl

/- The square root was defined using the `ℝ≥0` functional calculus with the `NNReal.sqrt`
function. This shows that we could have instead used the `ℝ`-functional calculus and
the `Real.sqrt` function. -/
lemma sqrt_eq_cfcₙ_real_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) :
    sqrt a = cfcₙ (√·) a := by
  refine sqrt_eq_of_mul_self_eq _ _ ?_ <| cfcₙ_nonneg fun x _ ↦ x.sqrt_nonneg
  rw [← cfcₙ_mul ..]
  nth_rw 2 [← cfcₙ_id' ℝ a]
  refine cfcₙ_congr fun x hx ↦ Real.mul_self_sqrt ?_
  exact quasispectrum_nonneg_of_nonneg a ha x hx

lemma sqrt_zero : sqrt (0 : A) = 0 := by simp [sqrt]

end NonUnital

section Unital

/- Because of the instance of the non-unital functional calculus for unital algebras, we
can use the exact same `sqrt` function for unital C⋆-algebras. -/
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma sqrt_one : sqrt (1 : A) = 1 := by
  rw [sqrt, cfcₙ_eq_cfc]
  simp

end Unital

end LeanCFC
