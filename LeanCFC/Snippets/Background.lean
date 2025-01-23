import Mathlib.Algebra.Algebra.Spectrum

namespace Background

def spectrum (R : Type*) {A : Type*} [CommSemiring R]
    [Ring A] [Algebra R A] (a : A) : Set R :=
  {r : R | ¬ IsUnit (algebraMap R A r - a)}

example : spectrum = _root_.spectrum := rfl

end Background
