import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
noncomputable section
open Set
namespace LeanCFC

variable {A : Type*} [CStarAlgebra A]

def cfc (f : ℂ → ℂ) (a : A) : A :=
  letI := Classical.propDecidable
  if h : IsStarNormal a ∧ Continuous ((spectrum ℂ a).restrict f)
  then
    letI := h.1
    continuousFunctionalCalculus a ⟨(spectrum ℂ a).restrict f, h.2⟩
  else 0

lemma cfc_def {f : ℂ → ℂ} {a : A} [ha : IsStarNormal a] (hf : ContinuousOn f (spectrum ℂ a)) :
    cfc f a = continuousFunctionalCalculus a ⟨_, hf.restrict⟩ := by
  rw [continuousOn_iff_continuous_restrict] at hf
  simp [cfc, ha, hf]

lemma cfc_id (a : A) [ha : IsStarNormal a] :
    cfc id a = a := by
  rw [cfc_def continuousOn_id]
  exact congrArg _ (continuousFunctionalCalculus_map_id a)

example {a : unitary A} {f : C(Metric.sphere (0 : ℂ) 1, ℂ)} : A :=
  cfc (Function.extend f (↑) 0) (a : A)

example {a : unitary A} {f : C(Metric.sphere (0 : ℂ) 1, ℂ)} : A :=
  cfc (Function.extend f (↑) 0) (a : A)

lemma cfc_not_continuous {f : ℂ → ℂ} {a : A} (hf : ¬ContinuousOn f (spectrum ℂ a)) :
    cfc f a = 0 := by
  rw [continuousOn_iff_continuous_restrict] at hf
  simp [cfc, hf]

lemma cfc_not_normal {f : ℂ → ℂ} {a : A} (ha : ¬IsStarNormal a) :
    cfc f a = 0 := by
  simp [cfc, ha]

lemma cfc_add {f g : ℂ → ℂ} {a : A} [ha : IsStarNormal a]
    (hf : ContinuousOn f (spectrum ℂ a)) (hg : ContinuousOn g (spectrum ℂ a)) :
    cfc (f + g) a = cfc f a + cfc g a := by
  rw [Pi.add_def, cfc_def (hf.add hg), cfc_def hf, cfc_def hg]
  norm_cast
  exact map_add (continuousFunctionalCalculus a) ⟨_, hf.restrict⟩ ⟨_, hg.restrict⟩

lemma cfc_neg {f : ℂ → ℂ} {a : A} [ha : IsStarNormal a]
    (hf : ContinuousOn f (spectrum ℂ a)) :
    cfc (-f) a = -(cfc f a) := by
  rw [Pi.neg_def, cfc_def hf, cfc_def hf.neg]
  norm_cast
  exact map_neg (continuousFunctionalCalculus a) ⟨_, hf.restrict⟩

-- Similarly, we prove `cfc_mul`, `cfc_sub`, `cfc_const`...

lemma cfc_eq_iff {f g : ℂ → ℂ} {a : A} [ha : IsStarNormal a]
    (hf : ContinuousOn f (spectrum ℂ a))
    (hg : ContinuousOn g (spectrum ℂ a)) :
    cfc f a = cfc g a ↔ ∀ x ∈ spectrum ℂ a, f x = g x := by
  simp [cfc_def hf, cfc_def hg, ContinuousMap.ext_iff]

lemma range_cfc_eq {a : A} [ha : IsStarNormal a] :
    Set.range (fun f ↦ cfc f a) = StarAlgebra.elemental ℂ a :=
  sorry

lemma norm_cfc_eq {f : ℂ → ℂ} {a : A} [ha : IsStarNormal a] :
    ‖cfc f a‖ = sInf {C : ℝ | 0 ≤ C ∧ ∀ x ∈ spectrum ℂ a, ‖f x‖ ≤ C} :=
  sorry

example {a b : A} [IsStarNormal a] [IsStarNormal b] (hab : a = b) {f : ℂ → ℂ}
    (H : cfc f a = 0) : cfc f b = 0 := by
  rw [hab] at H
  exact H

lemma spectrum_cfc {f : ℂ → ℂ} {a : A} [ha : IsStarNormal a]
    (hf : ContinuousOn f (spectrum ℂ a)) :
    spectrum ℂ (cfc f a) = f '' spectrum ℂ a :=
  sorry

lemma cfc_comp {f g : ℂ → ℂ} {a : A} [ha : IsStarNormal a]
    (hg : ContinuousOn g (f '' spectrum ℂ a)) (hf : ContinuousOn f (spectrum ℂ a)) :
    cfc (g ∘ f) a = cfc g (cfc f a) := by
  sorry

lemma cfc_comp_neg {f : ℂ → ℂ} {a : A} [ha : IsStarNormal a]
    (hf : ContinuousOn f (- spectrum ℂ a)) :
    cfc f (-a) = cfc (fun x ↦ f (-x)) a := by
  rw [← Set.image_neg_eq_neg] at hf
  change ContinuousOn f ((-id) '' spectrum ℂ a) at hf
  rw [← cfc_id a, ← cfc_neg continuousOn_id, ← cfc_comp hf (by exact continuousOn_neg),
      cfc_id]
  rfl

example {a : A} {f g h : ℂ → ℂ}
    (f_cont : ContinuousOn f ((fun x ↦ g x + h x) '' spectrum ℂ a))
    (g_cont : ContinuousOn g (spectrum ℂ a))
    (h_cont : ContinuousOn h (spectrum ℂ a))
    (H : ∀ x : ℂ, f (g x + h x) = x) [IsStarNormal a] :
    cfc f (cfc g a + cfc h a) = a := by
  rw [← cfc_add g_cont h_cont, ← cfc_comp (by exact f_cont) (by exact g_cont.add h_cont)]
  convert cfc_id a
  ext x
  exact H x

lemma range_cfc_eq' {a : A} [ha : IsStarNormal a] :
    Set.range (fun f ↦ cfc f a) = StarAlgebra.elemental ℂ a := by
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    by_cases h : ContinuousOn f (spectrum ℂ a)
    · simp [cfc_def h]
    · rw [continuousOn_iff_continuous_restrict] at h
      simpa [cfc, dif_neg (not_and_of_not_right (IsStarNormal a) h)] using zero_mem _
  · intro hx
    lift x to StarAlgebra.elemental ℂ a using hx
    let f' := (continuousFunctionalCalculus a).symm x
    let f := Function.extend Subtype.val f' 0
    have : (spectrum ℂ a).restrict f = f' := by ext; simp [f', f]
    use f
    simp only
    rw [cfc_def]
    · simpa only [SetLike.coe_eq_coe, this] using (continuousFunctionalCalculus a).apply_symm_apply x
    · rw [continuousOn_iff_continuous_restrict, this]
      exact map_continuous f'

open BoundedContinuousFunction in
lemma norm_cfc_eq' {f : ℂ → ℂ} {a : A} [ha : IsStarNormal a] (hf : ContinuousOn f (spectrum ℂ a)) :
    ‖cfc f a‖ = sInf {C : ℝ | 0 ≤ C ∧ ∀ x ∈ spectrum ℂ a, ‖f x‖ ≤ C} := by
  rw [cfc_def hf, isometry_subtype_coe.norm_map_of_map_zero rfl, StarAlgEquiv.norm_map,
    ← norm_mkOfCompact, norm_eq]
  simp

example {a b : A} [IsStarNormal a] [IsStarNormal b] (hab : a = b) {f : ℂ → ℂ}
    (H : cfc f a = 0) : cfc f b = 0 := by
  rw [hab] at H
  exact H

lemma spectrum_cfc' {f : ℂ → ℂ} {a : A} [ha : IsStarNormal a]
    (hf : ContinuousOn f (spectrum ℂ a)) :
    spectrum ℂ (cfc f a) = f '' spectrum ℂ a := by
  rw [cfc_def hf, ← StarSubalgebra.spectrum_eq (hS := StarAlgebra.elemental.isClosed ℂ a),
    AlgEquiv.spectrum_eq, ContinuousMap.spectrum_eq_range]
  simp

-- not actually used
lemma IsStarNormal.cfc_map {f : ℂ → ℂ} {a : A} : IsStarNormal (cfc f a) := by
  by_cases f_cont : ContinuousOn f (spectrum ℂ a)
  · by_cases a_normal : IsStarNormal a
    · rw [cfc_def f_cont, isStarNormal_iff, commute_iff_eq, ← StarMemClass.coe_star,
          ← MulMemClass.coe_mul, ← MulMemClass.coe_mul, mul_comm]
    · rw [cfc_not_normal a_normal]
      infer_instance
  · rw [cfc_not_continuous f_cont]
    infer_instance

lemma cfc_comp' [CompleteSpace A] {f g : ℂ → ℂ} {a : A} [ha : IsStarNormal a]
    (hg : ContinuousOn g (f '' spectrum ℂ a)) (hf : ContinuousOn f (spectrum ℂ a)) :
    cfc (g ∘ f) a = cfc g (cfc f a) := by
  have hgf : ContinuousOn (g ∘ f) (spectrum ℂ a) := hg.comp hf (mapsTo_image _ _)
  have f_mapsto : MapsTo f (spectrum ℂ a) (f '' spectrum ℂ a) := mapsTo_image _ _

  set φ_a : C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] A :=
    (StarAlgebra.elemental ℂ a).subtype.comp
    (continuousFunctionalCalculus a)
  set f_tilde : C(spectrum ℂ a, ℂ) := ⟨_, hf.restrict⟩
  set gf_tilde : C(spectrum ℂ a, ℂ) := ⟨_, (hg.comp hf f_mapsto).restrict⟩
  -- Do not rewrite `cfc g` for now to avoid incorrect motives
  rw [← spectrum_cfc hf, cfc_def hgf, cfc_def hf] at *
  set b := φ_a f_tilde
  change φ_a gf_tilde = cfc g b
  change ContinuousOn g (spectrum ℂ b) at hg
  change MapsTo f (spectrum ℂ a) (spectrum ℂ b) at f_mapsto

  set φ_b : C(spectrum ℂ b, ℂ) →⋆ₐ[ℂ] A :=
    (StarAlgebra.elemental ℂ b).subtype.comp
    (continuousFunctionalCalculus b)
  have φ_b_id : φ_b (.restrict _ (.id _)) = b := by
    simp [φ_b, continuousFunctionalCalculus_map_id]
  set g_tilde : C(spectrum ℂ b, ℂ) := ⟨_, hg.restrict⟩
  rw [cfc_def hg]
  change φ_a gf_tilde = φ_b g_tilde

  set f_hat : C(spectrum ℂ a, spectrum ℂ b) :=
    ⟨f_mapsto.restrict, hf.restrict_mapsTo f_mapsto⟩
  set ψ : C(spectrum ℂ b, ℂ) →⋆ₐ[ℂ] A :=
    φ_a.comp (ContinuousMap.compStarAlgHom' ℂ ℂ f_hat)
  have ψ_id : ψ (.restrict _ (.id _)) = b := rfl
  change ψ g_tilde = φ_b g_tilde

  suffices ψ = φ_b by rw [this]
  have := NonUnitalStarAlgHom.instContinuousLinearMapClassComplex
    (F := C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] A)
  have := NonUnitalStarAlgHom.instContinuousLinearMapClassComplex
    (F := C(spectrum ℂ b, ℂ) →⋆ₐ[ℂ] A)
  refine ContinuousMap.starAlgHom_ext_map_X (map_continuous _) (map_continuous _) ?_
  simp [Polynomial.toContinuousMapOn_X_eq_restrict_id, φ_b_id, ψ_id]
