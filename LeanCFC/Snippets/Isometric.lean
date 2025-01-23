import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

namespace LeanCFC

theorem norm_apply_le_norm_cfc {𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NormedRing A]
    [StarRing A] [NormedAlgebra 𝕜 A] [IsometricContinuousFunctionalCalculus 𝕜 A p]
    (f : 𝕜 → 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x ∈ spectrum 𝕜 a)
    (hf : ContinuousOn f (spectrum 𝕜 a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    ‖f x‖ ≤ ‖cfc f a‖ :=
  _root_.norm_apply_le_norm_cfc f a hx hf ha

theorem apply_le_nnnorm_cfc_nnreal {A : Type*} [NormedRing A] [StarRing A]
    [NormedAlgebra ℝ A] [PartialOrder A] [StarOrderedRing A]
    [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]
    (f : NNReal → NNReal) (a : A) ⦃x : NNReal⦄ (hx : x ∈ spectrum NNReal a)
    (hf : ContinuousOn f (spectrum NNReal a) := by cfc_cont_tac) (ha : 0 ≤ a := by cfc_tac) :
    f x ≤ ‖cfc f a‖₊ :=
  _root_.apply_le_nnnorm_cfc_nnreal f a hx hf ha

end LeanCFC
