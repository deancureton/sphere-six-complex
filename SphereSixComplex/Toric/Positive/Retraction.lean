module

public import SphereSixComplex.Prerequisites.Topology.Homotopy.StrongDeformationRetraction
public import SphereSixComplex.Cusp.LocalPhaseAction

/-!
# Lifting the positive quotient retraction

The polar data carry a strong deformation retraction of the quotient onto its central core.
The covering map lifts it to an equivariant retraction of the positive part.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction

/-- The compact three-torus acting in the polar decomposition. -/
public abbrev CompactTorus := Fin 3 → Circle

/-- The compact torus embedded in the dense algebraic torus. -/
public def compactTorusEmbedding : CompactTorus →* DenseTorus where
  toFun phi i := Circle.toUnits (phi i)
  map_one' := by ext i; rfl
  map_mul' phi psi := by ext i; simp

namespace PolarHoneycombData

public abbrev OrbitQuotient (Y : Type*) [TopologicalSpace Y]
    [MulAction (Multiplicative ParameterLattice) Y] :=
  Quotient (MulAction.orbitRel (Multiplicative ParameterLattice) Y)

public def orbitProjection (Y : Type*) [TopologicalSpace Y]
    [MulAction (Multiplicative ParameterLattice) Y] : C(Y, OrbitQuotient Y) where
  toFun := Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice) Y)
  continuous_toFun := continuous_quot_mk

public def orbitCore {Y : Type*} [TopologicalSpace Y]
    [MulAction (Multiplicative ParameterLattice) Y] (A : Set Y) : Set (OrbitQuotient Y) :=
  orbitProjection Y '' A

end PolarHoneycombData

/-- The precise standard positive-part and honeycomb package used before phase spreading. -/
public structure PolarHoneycombData (M : Model) (r : ℝ) where
  positivePart : Set (localCarrier M r)
  modulus : C(localCarrier M r, positivePart)
  modulus_fixed : ∀ q : positivePart, modulus q = q
  positive_t : ∀ q : positivePart, (M.t q).im = 0 ∧ 0 ≤ (M.t q).re
  modulus_t : ∀ p, M.t (modulus p) = (‖M.t p‖ : ℝ)
  polar_surjective : ∀ p : localCarrier M r, ∃ phi : CompactTorus,
    M.torusAction (compactTorusEmbedding phi) (modulus p) = p
  central : Set positivePart
  central_eq : central = {q : positivePart | M.t (q : localCarrier M r) = 0}
  honeycomb : (Fin 2 → ℝ) ≃ₜ central
  positiveTwist : ParameterLattice → DenseTorus
  positiveTwist_zero : positiveTwist 0 = 1
  positiveTwist_add : ∀ lambda mu,
    positiveTwist (lambda + mu) = positiveTwist lambda * positiveTwist mu
  positiveTwist_last : ∀ lambda, positiveTwist lambda 2 = 1
  positiveTwist_real : ∀ lambda i,
    0 < ((positiveTwist lambda i : ℂˣ) : ℂ).re ∧
      ((positiveTwist lambda i : ℂˣ) : ℂ).im = 0
  positiveDeckAction : MulAction (Multiplicative ParameterLattice) positivePart
  positiveDeck_coe : ∀ lambda q,
    ((((Multiplicative.ofAdd lambda) • q : positivePart) : localCarrier M r) : M.Carrier) =
      M.torusAction (positiveTwist lambda)
        (Additive.toMul (M.fanShear lambda) (q : M.Carrier))
  positiveDeckContinuous :
    letI := positiveDeckAction
    ContinuousConstSMul (Multiplicative ParameterLattice) positivePart
  quotientCovering :
    letI := positiveDeckAction
    IsQuotientCoveringMap
      (PolarHoneycombData.orbitProjection positivePart)
      (Multiplicative ParameterLattice)
  central_preimage :
    letI := positiveDeckAction
    PolarHoneycombData.orbitProjection positivePart ⁻¹'
        PolarHoneycombData.orbitCore central = central
  quotientRetraction :
    letI := positiveDeckAction
    SphereSixComplex.StrongDeformationRetraction
      (PolarHoneycombData.OrbitQuotient positivePart)
      (PolarHoneycombData.orbitCore central)

namespace PolarHoneycombData

variable {M : Model} {r : ℝ} (P : PolarHoneycombData M r)



/-- The positive-part strong deformation retraction, lifted equivariantly through the regular
lattice covering. -/
public noncomputable def positiveEquivariantStrongDeformationRetraction :
    letI := P.positiveDeckAction
    SphereSixComplex.EquivariantStrongDeformationRetraction
      (Multiplicative ParameterLattice) P.positivePart P.central := by
  letI := P.positiveDeckAction
  exact Classical.choice
    (EquivariantStrongDeformationRetraction.nonempty_lift
        (orbitProjection P.positivePart) P.central (orbitCore P.central) P.quotientCovering
          P.central_preimage P.quotientRetraction)

end PolarHoneycombData

end SphereSixComplex.Geometry.InfiniteA2Toric
