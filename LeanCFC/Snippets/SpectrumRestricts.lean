module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-! # Friction from working only over `ℂ`

This file gives a comparison between using the continuous functional calculus only
over `ℂ` versus our approach of allowing it to be defined over `ℝ` as well (or even `ℝ≥0`).
We present an example problem which is a key stepping stone on the way to proving that
in a complex C⋆-algebra, the spectrum of an element of the form `star a * a` is nonnegative.

The first approach uses the `ℂ`-spectrum and the continuous functional calculus over `ℂ`,
and the second approach uses the `ℝ`-spectrum and the continuous functional calculus over `ℝ`.
We keep the arguments as similar as possible so that the added friction from working only
over `ℂ` is clear.

However, since one hypothesis in these statements is *slightly* different, we prove
additionally that the differing hypothesis is equivalent in the presence of the other
hypotheses. We note that the combined proof lengths of the second example and the
equivalence of the two hypotheses is still shorter than the first example, and we are
in fact proving more.
-/

open scoped NNReal ComplexOrder

namespace LeanCFC

variable {A : Type*} [CStarAlgebra A]

example [Nontrivial A] {a : A} (ha : IsSelfAdjoint a) {t : ℝ} (ht : ‖a‖ ≤ t)
    (h : ∀ x ∈ spectrum ℂ a, 0 ≤ x) : ‖algebraMap ℝ A t - a‖ ≤ t := by
  rw [IsScalarTower.algebraMap_apply ℝ ℂ A, Complex.coe_algebraMap]
  rw [← cfc_id' ℂ a, ← cfc_const (t : ℂ) a, ← cfc_sub ..]
  refine IsGreatest.norm_cfc (t - · : ℂ → ℂ) a |>.isLUB.2 ?_
  rintro - ⟨x, hx, rfl⟩
  simp only
  lift x to ℝ using (h x hx).2.symm
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hx' : 0 ≤ x := by simpa using h x hx
  have hxt : x ≤ t := by
    simpa [abs_of_nonneg hx'] using (spectrum.norm_le_norm_of_mem hx |>.trans ht)
  grind

example [Nontrivial A] {a : A} (ha : IsSelfAdjoint a) {t : ℝ} (ht : ‖a‖ ≤ t)
    (h : ∀ x ∈ spectrum ℝ a, 0 ≤ x) : ‖algebraMap ℝ A t - a‖ ≤ t := by
  rw [← cfc_id' ℝ a, ← cfc_const t a, ← cfc_sub ..]
  refine IsGreatest.norm_cfc (t - ·) a |>.isLUB.2 ?_
  rintro - ⟨x, hx, rfl⟩
  have := spectrum.norm_le_norm_of_mem hx |>.trans ht
  grind [Real.norm_eq_abs, h x hx]

example {a : A} (ha : IsSelfAdjoint a) :
    (∀ x ∈ spectrum ℂ a, 0 ≤ x) ↔ (∀ x ∈ spectrum ℝ a, 0 ≤ x) := by
  have := ha.spectrumRestricts
  have h_map : Set.MapsTo Complex.reCLM (spectrum ℂ a) (spectrum ℝ a) := by
    simpa [← this.image] using Set.mapsTo_image ..
  simp [this.rightInvOn.surjOn h_map |>.forall (fun _ _ ↦ by simpa)]

-- in fact, the previous example can be generalized to any predicates `pC : ℂ → Prop`
-- and `pR : ℝ → Prop` such that `pC (x : ℂ) ↔ pR x` for all `x : ℝ`.
lemma _root_.IsSelfAdjoint.forall_mem_spectrum_iff {a : A} (ha : IsSelfAdjoint a)
    {pC : ℂ → Prop} {pR : ℝ → Prop} (hp : ∀ x : ℝ, pC x ↔ pR x) :
    (∀ x ∈ spectrum ℂ a, pC x) ↔ (∀ x ∈ spectrum ℝ a, pR x) := by
  have := ha.spectrumRestricts
  have h_map : Set.MapsTo Complex.reCLM (spectrum ℂ a) (spectrum ℝ a) := by
    simpa [← this.image] using Set.mapsTo_image ..
  simp [this.rightInvOn.surjOn h_map |>.forall (fun _ _ ↦ by simpa), hp]

-- then we can reprove the prior example in one line as:
example {a : A} (ha : IsSelfAdjoint a) :
    (∀ x ∈ spectrum ℂ a, 0 ≤ x) ↔ (∀ x ∈ spectrum ℝ a, 0 ≤ x) :=
  ha.forall_mem_spectrum_iff <| by simp

-- or one with strict inequality
example {a : A} (ha : IsSelfAdjoint a) :
    (∀ x ∈ spectrum ℂ a, 0 < x) ↔ (∀ x ∈ spectrum ℝ a, 0 < x) :=
  ha.forall_mem_spectrum_iff <| by simp

end LeanCFC
