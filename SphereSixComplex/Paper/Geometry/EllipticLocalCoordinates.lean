module

public import SphereSixComplex.Paper.Geometry.EllipticComplexFilling
public import SphereSixComplex.Prerequisites.Geometry.ComplexUnitDisc
import all SphereSixComplex.Prerequisites.Geometry.ComplexUnitDisc
public import SphereSixComplex.Prerequisites.Geometry.FuchsianEllipticCoordinates
import all SphereSixComplex.Prerequisites.Geometry.FuchsianEllipticCoordinates

/-!
# Explicit local coordinates at the elliptic points

The Cayley coordinate centered at `a ∈ ℍ` is `(z - a) / (z - conj a)`.  It identifies the
upper half-plane with the open unit disc and conjugates the two explicit elliptic generators to
scalar rotations.  These are purely local statements and use no global uniformization.
-/

open scoped ComplexConjugate

namespace SphereSixComplex.Geometry.EllipticLocalCoordinates

open Complex SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry

noncomputable section

open SphereSixComplex.LatticeData

/-- The fibre-side input left by the local Cayley calculation.  It is exactly the torus-affine
part of `EllipticActionData`; all base rotation fields are discharged explicitly below. -/
public structure EllipticFiberData (m : ℕ) [NeZero m]
    (Torus : Type*) [AddCommGroup Torus] where
  automorphism : Torus ≃+ Torus
  translation : Torus
  translationVector : Lattice
  translation_fixed : automorphism translation = translation
  automorphism_pow : automorphism.toEquiv ^ m = 1
  translation_torsion : m • translation = 0
  fiber_fixed_iff : ∀ k, 0 < k → k < m →
    ((∃ x : Torus, (affineEquiv automorphism translation ^ k) x = x) ↔
      (m : ℤ) ∣ (k : ℤ) * gamma translationVector)

namespace EllipticFiberData

variable {Torus : Type*} [AddCommGroup Torus]

/-- Complete order-three filling data obtained by adjoining the explicit Cayley-disc base. -/
@[expose] public noncomputable def orderThreeActionData
    (D : EllipticFiberData 3 Torus) :
    EllipticActionData 3 ComplexUnitDisc Torus where
  rotation := orderThreeDiscRotation
  center := ComplexUnitDisc.center
  offCenter := discOffCenter
  offCenter_ne := discOffCenter_ne
  rotation_pow := orderThreeDiscRotation_pow
  rotation_fixed_iff := orderThreeDiscRotation_fixed_iff
  automorphism := D.automorphism
  translation := D.translation
  translationVector := D.translationVector
  translation_fixed := D.translation_fixed
  automorphism_pow := D.automorphism_pow
  translation_torsion := D.translation_torsion
  fiber_fixed_iff := D.fiber_fixed_iff

/-- Complete order-four filling data obtained by adjoining the explicit Cayley-disc base. -/
@[expose] public noncomputable def orderFourActionData
    (D : EllipticFiberData 4 Torus) :
    EllipticActionData 4 ComplexUnitDisc Torus where
  rotation := orderFourDiscRotation
  center := ComplexUnitDisc.center
  offCenter := discOffCenter
  offCenter_ne := discOffCenter_ne
  rotation_pow := orderFourDiscRotation_pow
  rotation_fixed_iff := orderFourDiscRotation_fixed_iff
  automorphism := D.automorphism
  translation := D.translation
  translationVector := D.translationVector
  translation_fixed := D.translation_fixed
  automorphism_pow := D.automorphism_pow
  translation_torsion := D.translation_torsion
  fiber_fixed_iff := D.fiber_fixed_iff

/-- The existing order-three filling freeness theorem applies directly to the explicit local
Cayley base. -/
public theorem orderThreeActionData_free (D : EllipticFiberData 3 Torus)
    (hv : D.translationVector = epsilon) :
    letI := D.orderThreeActionData.diagonalAction
    IsCancelSMul (FiniteCyclic 3) (ComplexUnitDisc × Torus) :=
  epsilon_action_free D.orderThreeActionData hv

/-- The existing order-four filling freeness theorem applies directly to the explicit local
Cayley base. -/
public theorem orderFourActionData_free (D : EllipticFiberData 4 Torus)
    (hv : D.translationVector = -epsilon') :
    letI := D.orderFourActionData.diagonalAction
    IsCancelSMul (FiniteCyclic 4) (ComplexUnitDisc × Torus) :=
  neg_epsilonPrime_action_free D.orderFourActionData hv

/-- The complex-filling theorem specializes to the explicit order-three Cayley base once the
remaining affine torus action is holomorphic. -/
public theorem orderThreeActionData_quotient_isManifold
    {E H : Type*} [TopologicalSpace (ComplexUnitDisc × Torus)] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : ModelWithCorners ℂ E H)
    [T2Space (ComplexUnitDisc × Torus)] [LocallyCompactSpace (ComplexUnitDisc × Torus)]
    [ChartedSpace H (ComplexUnitDisc × Torus)]
    [IsManifold I ω (ComplexUnitDisc × Torus)]
    (D : EllipticFiberData 3 Torus) (hv : D.translationVector = epsilon)
    (hholomorphic : ∀ g : FiniteCyclic 3,
      ContMDiff I I ω (fun p : ComplexUnitDisc × Torus ↦
        D.orderThreeActionData.representation g p)) :
    let A := D.orderThreeActionData
    letI := A.diagonalAction
    let hf := quotient_isQuotientCoveringMap A (epsilon_action_free A hv)
      (fun g ↦ (hholomorphic g).continuous)
    letI : ChartedSpace H
      (MulAction.orbitRel.Quotient (FiniteCyclic 3) (ComplexUnitDisc × Torus)) :=
      hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
    IsManifold I ω
      (MulAction.orbitRel.Quotient (FiniteCyclic 3) (ComplexUnitDisc × Torus)) := by
  exact epsilonQuotient_isManifold I D.orderThreeActionData hv hholomorphic

/-- The complex-filling theorem specializes to the explicit order-four Cayley base once the
remaining affine torus action is holomorphic. -/
public theorem orderFourActionData_quotient_isManifold
    {E H : Type*} [TopologicalSpace (ComplexUnitDisc × Torus)] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : ModelWithCorners ℂ E H)
    [T2Space (ComplexUnitDisc × Torus)] [LocallyCompactSpace (ComplexUnitDisc × Torus)]
    [ChartedSpace H (ComplexUnitDisc × Torus)]
    [IsManifold I ω (ComplexUnitDisc × Torus)]
    (D : EllipticFiberData 4 Torus) (hv : D.translationVector = -epsilon')
    (hholomorphic : ∀ g : FiniteCyclic 4,
      ContMDiff I I ω (fun p : ComplexUnitDisc × Torus ↦
        D.orderFourActionData.representation g p)) :
    let A := D.orderFourActionData
    letI := A.diagonalAction
    let hf := quotient_isQuotientCoveringMap A (neg_epsilonPrime_action_free A hv)
      (fun g ↦ (hholomorphic g).continuous)
    letI : ChartedSpace H
      (MulAction.orbitRel.Quotient (FiniteCyclic 4) (ComplexUnitDisc × Torus)) :=
      hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
    IsManifold I ω
      (MulAction.orbitRel.Quotient (FiniteCyclic 4) (ComplexUnitDisc × Torus)) := by
  exact negEpsilonPrimeQuotient_isManifold I D.orderFourActionData hv hholomorphic

end EllipticFiberData

end

end SphereSixComplex.Geometry.EllipticLocalCoordinates
