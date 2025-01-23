import Mathlib

/-! # Litmus test for working with inverses

Goal: For an invertible element `a` in a unital C⋆-algebra, and a function `f`
which is nonzero on the spectrum of `a⁻¹`, show that:
`cfc f a⁻¹ = cfc (fun x ↦ f x⁻¹) a`.
-/

noncomputable section

namespace LeanCFC.Litmus

variable {A : Type*} [CStarAlgebra A]

/-- `cfc (fun x ↦ x⁻¹) a = a⁻¹` when `a` is normal and invertible. -/
lemma cfc_inv (a : Aˣ) (ha : IsStarNormal (a : A) := by cfc_tac) :
    cfc (·⁻¹ : ℂ → ℂ) (a : A) = ↑a⁻¹ := by
  refine a.eq_inv_of_mul_eq_one_left ?_
  nth_rw 1 [← cfc_id' ℂ (a : A), ← cfc_mul .., ← cfc_one ℂ (a : A)]
  exact cfc_congr fun _ _ ↦ mul_inv_cancel₀ <| by aesop

/-- When `a` is normal and invertible and `f` is continuous on the spectrum
of `a⁻¹`, then `cfc f a⁻¹ = cfc (fun x ↦ f x⁻¹) a`. -/
lemma cfc_comp_inv (f : ℂ → ℂ) (a : Aˣ)
    (hf : ContinuousOn f (spectrum ℂ (↑a⁻¹ : A)))
    (ha : IsStarNormal (a : A)) :
    cfc f (↑a⁻¹ : A) = cfc (f ·⁻¹) (a : A) := by
  rw [← cfc_inv a, cfc_map_spectrum (·⁻¹) (a : A)] at hf
  rw [← cfc_inv a, ← cfc_comp' ..]

end LeanCFC.Litmus
