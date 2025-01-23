import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

namespace LeanCFC.Uniqueness

variable {R A : Type*} (p : outParam (A → Prop))
    [CommSemiring R] [StarRing R] [MetricSpace R] [TopologicalSemiring R]
    [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] [ContinuousFunctionalCalculus R p]
    [ContinuousMap.UniqueHom R A]

lemma cfc_comp (g : R → R) (f : R → R) (a : A) (ha : p a)
    (hg : ContinuousOn g (f '' spectrum R a))
    (hf : ContinuousOn f (spectrum R a)) :
    cfc (g ∘ f) a = cfc g (cfc f a) := by
  have := hg.comp hf <| (spectrum R a).mapsTo_image f
  have sp_eq : spectrum R (cfcHom (show p a from ha) (ContinuousMap.mk _ hf.restrict)) =
      f '' (spectrum R a) := by
    rw [cfcHom_map_spectrum (by exact ha) _]
    ext
    simp
  rw [cfc_apply .., cfc_apply f a,
    cfc_apply _ _ (cfcHom_predicate (show p a from ha) _) (by convert hg), ← cfcHom_comp _ _]
  swap
  · exact ContinuousMap.mk _ <| hf.restrict.codRestrict fun x ↦ by rw [sp_eq]; use x.1; simp
  · congr
  · exact fun _ ↦ rfl

class ContinuousMap.UniqueHom (R A : Type*) [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] : Prop where
  eq_of_continuous_of_map_id (s : Set R) [CompactSpace s]
    (φ ψ : C(s, R) →⋆ₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (.restrict s <| .id R) = ψ (.restrict s <| .id R)) :
    φ = ψ

end LeanCFC.Uniqueness
