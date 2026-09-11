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



/-- The six displayed columns of `α₂` in Remark 7.20. -/
public def alphaTwoMatrix : Matrix (Fin 4) (Fin 6) ℤ :=
  !![ 2,  1,  3,  0, 0, 0;
     -4, -2,  0,  1, 0, 0;
     -2, -2, -4,  0, 0, 0;
      3,  3,  0, -1, 0, 0]





/-- The primitive functional `Φ=(4,2,3,2)` annihilating the image of `α₂`. -/
public def alphaTwoFunctional (x : Fin 4 → ℤ) : ℤ :=
  4 * x 0 + 2 * x 1 + 3 * x 2 + 2 * x 3

public theorem alphaTwoFunctional_relation (y : Fin 6 → ℤ) :
    alphaTwoFunctional (alphaTwoMatrix.mulVec y) = 0 := by
  simp [alphaTwoFunctional, alphaTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The image of `α₂` is exactly `ker Φ`; equivalently its cokernel is classified by `Φ`. -/
public theorem alphaTwo_image_iff (x : Fin 4 → ℤ) :
    (∃ y : Fin 6 → ℤ, alphaTwoMatrix.mulVec y = x) ↔ alphaTwoFunctional x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact alphaTwoFunctional_relation y
  · intro h
    unfold alphaTwoFunctional at h
    have hcmod : x 2 % 2 = 0 := by
      omega
    obtain ⟨s, hs⟩ : ∃ s : ℤ, x 2 = 2 * s := ⟨x 2 / 2, by omega⟩
    refine ⟨![x 0, -x 0 - 3 * s, s, -9 * s - x 3, 0, 0], ?_⟩
    funext i
    fin_cases i <;>
      simp [alphaTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h hs ⊢ <;>
      ring_nf at h hs ⊢ <;>
      omega


/-- `Φ` is onto, so the cokernel of `α₂` is infinite cyclic. -/
public theorem alphaTwoFunctional_surjective : Function.Surjective alphaTwoFunctional := by
  intro z
  refine ⟨![0, -z, z, 0], ?_⟩
  simp [alphaTwoFunctional]
  ring

















end SphereSixComplex
