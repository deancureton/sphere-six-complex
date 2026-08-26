module

public import SphereSixComplex.Topology.EstablishedStrongDeformationRetracts
public import SphereSixComplex.Topology.RelativeCWHomotopyExtensionProof
public import SphereSixComplex.Geometry.CuspLocalPhaseAction
public import Mathlib.Analysis.Complex.Circle

/-!
# Positive-part retraction for the standard infinite `A₂` toric model

The standard input below records the nonnegative part, its modulus/polar description, the
honeycomb central fibre, and the two quotient-level properties proved by the compact
three-manifold, Whitehead, and collar argument. It deliberately contains no deformation
retraction. The equivariant retraction is derived from the established general-topology results.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

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
  positivePart : Set (LocalCarrier M r)
  modulus : C(LocalCarrier M r, positivePart)
  modulus_fixed : ∀ q : positivePart, modulus q = q
  positive_t : ∀ q : positivePart, (M.t q).im = 0 ∧ 0 ≤ (M.t q).re
  modulus_t : ∀ p, M.t (modulus p) = (‖M.t p‖ : ℝ)
  polar_surjective : ∀ p : LocalCarrier M r, ∃ phi : CompactTorus,
    M.torusAction (compactTorusEmbedding phi) (modulus p) = p
  central : Set positivePart
  central_eq : central = {q : positivePart | M.t (q : LocalCarrier M r) = 0}
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
    ((((Multiplicative.ofAdd lambda) • q : positivePart) : LocalCarrier M r) : M.Carrier) =
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
  positive_contractible : ContractibleSpace positivePart
  central_contractible : ContractibleSpace central
  quotient_relativeCW :
    letI := positiveDeckAction
    Topology.RelCWComplex
      (Set.univ : Set (PolarHoneycombData.OrbitQuotient positivePart))
      (PolarHoneycombData.orbitCore central)
  quotient_t2 :
    letI := positiveDeckAction
    T2Space (PolarHoneycombData.OrbitQuotient positivePart)

namespace PolarHoneycombData

variable {M : Model} {r : ℝ} (P : PolarHoneycombData M r)

public theorem positiveDeck_preserves_t (lambda : ParameterLattice) (q : P.positivePart) :
    letI := P.positiveDeckAction
    M.t (((Multiplicative.ofAdd lambda) • q : P.positivePart) : LocalCarrier M r) =
      M.t (q : LocalCarrier M r) := by
  let _ := P.positiveDeckAction
  rw [P.positiveDeck_coe, M.t_torusAction, P.positiveTwist_last,
    M.fanShear_preserves_t]
  simp

public theorem positiveDeck_mem_central_iff (lambda : ParameterLattice)
    (q : P.positivePart) :
    letI := P.positiveDeckAction
    (Multiplicative.ofAdd lambda) • q ∈ P.central ↔ q ∈ P.central := by
  let _ := P.positiveDeckAction
  have hmem (x : P.positivePart) :
      x ∈ P.central ↔ M.t (x : LocalCarrier M r) = 0 := by
    exact Set.ext_iff.mp P.central_eq x
  rw [hmem, hmem, P.positiveDeck_preserves_t]

/-- The quotient-level strong deformation retraction obtained from Whitehead plus the collar
homotopy-extension property. -/
public noncomputable def quotientStrongDeformationRetraction :
    letI := P.positiveDeckAction
    SphereSixComplex.StrongDeformationRetraction
      (OrbitQuotient P.positivePart)
      (orbitCore P.central) := by
  letI := P.positiveDeckAction
  letI := P.quotient_t2
  let hHEP :=
    SphereSixComplex.EstablishedGeneralTopology.hasHomotopyExtensionProperty_of_relativeCWComplex_proved
      (orbitCore P.central) P.quotient_relativeCW
  let hEquiv :=
    SphereSixComplex.EstablishedGeneralTopology.isHomotopyEquivalenceInclusion_of_contractible_regularCover
        (orbitProjection P.positivePart) P.central (orbitCore P.central) P.quotientCovering
          P.central_preimage P.positive_contractible P.central_contractible P.quotient_relativeCW
  exact Classical.choice
    (SphereSixComplex.EstablishedGeneralTopology.strongDeformationRetraction_of_cofibration_homotopyEquivalence
        (orbitCore P.central) hHEP hEquiv)

/-- The positive-part strong deformation retraction, lifted equivariantly through the regular
lattice covering. -/
public noncomputable def positiveEquivariantStrongDeformationRetraction :
    letI := P.positiveDeckAction
    SphereSixComplex.EquivariantStrongDeformationRetraction
      (Multiplicative ParameterLattice) P.positivePart P.central := by
  letI := P.positiveDeckAction
  exact Classical.choice
    (SphereSixComplex.EstablishedGeneralTopology.equivariantStrongDeformationRetraction_lift
        (orbitProjection P.positivePart) P.central (orbitCore P.central) P.quotientCovering
          P.central_preimage P.quotientStrongDeformationRetraction)

end PolarHoneycombData

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

