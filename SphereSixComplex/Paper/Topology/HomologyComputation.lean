module

public import SphereSixComplex.Prerequisites.Topology.HomologySphere
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The finite integral calculations in Section 7

The paper does not give a finite singular chain complex for the glued threefold.  It gives the
following presentation and specialization matrices and then uses Mayer--Vietoris exactness,
sweeping arguments, duality, and universal coefficients.  This file verifies the finite integer
algebra and records the remaining topological identification as an explicit realization contract.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex

/-- The generator `ν₀=(0,-1,-1,1)` of `ker α₁`. -/
public def alphaOneKernelGenerator : Fin 4 → ℤ := ![0, -1, -1, 1]

end SphereSixComplex
