# The continuous functional calculus in Lean

This repository contains the code artefacts associated to the paper:
*The continuous functional calculus in Lean*. As the implementation
documented herein is already incorporated into Lean's mathematical
library, Mathlib, the code here is meant to serve solely as a 
permanent reference to the paper, not as a library that should be 
used downstream. For that purpose, users should simply use Mathlib
itself.

That being said, this is a functioning Lean 4 repository, and
interested parties can interact with all the code in the usual manner.
Simply clone this repository, and then, assuming that you already
have `elan` and `lake` installed, in the folder containing this code,
run:

```bash
$ lake exe cache get
$ lake build
```

The `build` step will build all the files in `LeanCFC`, which
should take a few minutes.
(It is possible to run the second step without the first, but it
may take anywhere from 20 minutes to a few hours to complete 
depending on your machine.)

The code contained herein is organized in the following manner.

## [Snippets](LeanCFC/Snippets)

The folder `LeanCFC/Snippets` contains all the code snippets which
appear in the paper, organized by the section in which they appear.
While only certain lines were extracted for reference in the paper,
these files build without error, but they are not meant for
consumption outside the context of where they appear in the paper.
As such, there is essentially no documentation contained in these
files.

## [Litmus Tests](LeanCFC/Litmus)

As described in the paper, there were several tasks which we 
determined would serve as effective litmus tests to determine whether
our implementation was sufficiently usable as to be practical.
We provide example implementations satisfying each of the tests in 
the folder `LeanCFC/Litmus`. We include comments to connect the dots
between the code and some of the ideas in the paper.


1. **Inv**: For an invertible element `a` and a function `f` which
    is nonzero on the spectrum, show that:
    `cfc a⁻¹ f = cfc (fun x ↦ f x⁻¹) a`.
    This test requires:
    + A continuous functional calculus over `ℂ` for normal elements.
    + Use of functions which are not everywhere continuous
      (i.e., `fun x ↦ x⁻¹`).
    + Application of the composition property (since we are working
      with continuous functional calculi for both `a` and `a⁻¹`).
3. **PosPart**: For a selfadjoint element `a` in a non-unital 
    C⋆-algebra, there are commuting positive elements `a⁺` and `a⁻`
    such that `a = a⁺ - a⁻` and `a⁺ * a⁻ = 0`.
    This test has slightly different requirements:
    + A (non-unital!) continuous functional calculus over `ℝ` for
      selfadjoint elements.
    + Use of auto-params involving the condition that `f 0 = 0`.
4. **Sqrt**: For a nonnegative element `a` in a non-unital 
    C⋆-algebra, there is a unique nonnegative element `CFC.sqrt a`
    so that `(CFC.sqrt a) ^ 2 = a`.
    This requires:
    + A (non-unital!) continuous functional calculus over `ℝ≥0`
      for nonnegative elements.
    + Application of the composition property, which requires
      uniqueness of the functional calculus. This is trickier over
      `ℝ≥0` than over `ℝ` or `ℂ` because Stone--Weierstrass doesn't
      apply.
    + Showing that we can use different functional calculi (i.e.,
      over `ℝ` too!)

## [Implementation](LeanCFC/Implementation)

Our complete implementation of the continuous functional calculus,
in all its various forms, is contained in `LeanCFC/Implementation`.
As this implementation has already been merged into Mathlib, the
declarations in these files are simply copied from the relevant files
in Mathlib. However, we have added some comments interspersed
throughout to provide better understanding for the reader. The files
in this folder contain:

1. **[Unital](LeanCFC/Implementation/Unital.lean)**: the implementation of the `ContinuousFunctionalCalculus`
    class, developing the basic properties of `cfc` and `cfcHom`
    generically.
2. **[NonUnital](LeanCFC/Implementation/NonUnital.lean)**: the same, but for `NonUnitalContinuousFunctionalCalculus`.
3. **[Unique](LeanCFC/Implementation/Unique.lean)**: instances of the uniqueness class for topological
    `𝕜`-algebras (where `𝕜 := ℝ` or `𝕜 := ℂ`).
4. **[Restrict](LeanCFC/Implementation/Restrict.lean)**: the generic lemmas that allow one to pass from a ring
    to a scalar subring, not registered as instances.
5. **[Isometric](LeanCFC/Implementation/Isometric.lean)**: the definition and basic lemmas related to the isometric
    variation of the continuous functional calculus.
6. **[Instances](LeanCFC/Implementation/Instances.lean)**: instances for the continuous functional calculus,
    and the non-unital continuous functional calculus, as well as their
    isometric variations, over `ℝ` and `ℝ≥0`, given corresponding
    instances over `ℂ` and `ℝ`, respectively.
7. **[Basic](LeanCFC/Implementation/Basic.lean)**: the ⋆-isomorphism between `C(σ ℂ a, ℂ)` and
    `StarAlgebra.elemental ℂ a` for `a : A`, where `A` is a unital
    C⋆-algebra. This also includes instances of the continuous functional
    calculus over `ℂ` for unital and non-unital C⋆-algebras.
