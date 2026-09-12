module

public import SphereSixComplex.Paper.Topology.PaperEllipticInteriorNormalizedSplitting
public import SphereSixComplex.Paper.Topology.PaperCuspCollarRadialMappingTorus
public import SphereSixComplex.Paper.Topology.PaperEllipticTwoDiscHomologyCoordinatesRealization
public import SphereSixComplex.Paper.Topology.PaperCuspCentralFiberHomology
public import SphereSixComplex.Paper.Topology.PaperCuspPhaseSpreading
public import SphereSixComplex.Paper.Topology.PaperSectionSevenFinalDegreeZero
public import SphereSixComplex.Paper.Topology.PaperSectionSevenEllipticTwoDiscCoverRealization

/-!
# Coordinate homomorphisms for the cusp boundary

Coordinate evaluation after an additive lattice equivalence gives additive homomorphisms.
The cusp boundary coordinate is the actual Wang boundary followed by its marked invariant
coordinate. Lattice-basis extensionality and the evaluation formulas are proved here.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set

namespace SphereSixComplex

/-- Additive maps out of a finite free abelian group agree when they agree on its standard
basis. -/
public theorem addMonoidHom_ext_of_equiv_pi_single_one
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] {n : ℕ}
    (e : G ≃+ (Fin n → ℤ)) (f g : G →+ H)
    (h : ∀ i, f (e.symm (Pi.single i 1)) = g (e.symm (Pi.single i 1))) :
    f = g := by
  apply AddMonoidHom.ext
  intro x
  let y := e x
  have hx : x = e.symm y := by simp [y]
  rw [hx]
  apply Pi.single_induction (M := fun _ : Fin n => ℤ)
    (p := fun z => f (e.symm z) = g (e.symm z)) y
  · simp
  · intro a b ha hb
    simpa using congrArg₂ (· + ·) ha hb
  · intro i z
    have hz : (Pi.single i z : Fin n → ℤ) =
        z • (Pi.single i 1 : Fin n → ℤ) := by
      ext j
      classical
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    calc
      f (e.symm (Pi.single i z)) =
          f (e.symm (z • (Pi.single i 1 : Fin n → ℤ))) := by rw [hz]
      _ = z • f (e.symm (Pi.single i 1)) := by rw [map_zsmul, map_zsmul]
      _ = z • g (e.symm (Pi.single i 1)) := congrArg (z • ·) (h i)
      _ = g (e.symm (z • (Pi.single i 1 : Fin n → ℤ))) := by rw [map_zsmul, map_zsmul]
      _ = g (e.symm (Pi.single i z)) := by rw [hz]

namespace Geometry.AnalyticData

open EllipticTwoDiscHomologyCoordinates

variable {A : AnalyticData}


namespace EllipticInteriorMarkedCycleData

variable {D : A.EllipticTwoDiscCoverData}


/-- Evaluate one coordinate after an additive equivalence to a finite integer lattice. -/
public def coordinateAfterAddEquiv {G : Type*} [AddCommGroup G] {n : ℕ}
    (e : G ≃+ (Fin n → ℤ)) (i : Fin n) : G →+ ℤ where
  toFun x := e x i
  map_zero' := by simp
  map_add' x y := by simp


/-- The invariant boundary coordinate of an included cusp degree-two class. -/
public noncomputable def cuspDegreeTwoBoundaryCoordinateHom
    (N : A.EllipticBandHomologyAlignment D) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+ ℤ where
  toFun x := N.actualHomologyCoordinates.degreeTwoInvariantEquiv
    ((presentationTwo (D := D)).totalToInvariants (cuspToEllipticUnionHomology D 2 x))
  map_zero' := by
    change N.actualHomologyCoordinates.degreeTwoInvariantEquiv
      ((presentationTwo (D := D)).totalToInvariants
        (cuspToEllipticUnionHomology D 2 0)) = 0
    rw [show cuspToEllipticUnionHomology D 2 0 = 0 by
      simp [cuspToEllipticUnionHomology], map_zero, map_zero]
  map_add' x y := by
    change N.actualHomologyCoordinates.degreeTwoInvariantEquiv
        ((presentationTwo (D := D)).totalToInvariants
          (cuspToEllipticUnionHomology D 2 (x + y))) = _
    rw [show cuspToEllipticUnionHomology D 2 (x + y) =
        cuspToEllipticUnionHomology D 2 x + cuspToEllipticUnionHomology D 2 y by
      simp [cuspToEllipticUnionHomology], map_add, map_add]

public theorem cuspDegreeTwoBoundaryCoordinateHom_apply
    (N : A.EllipticBandHomologyAlignment D) (x) :
    cuspDegreeTwoBoundaryCoordinateHom N x =
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
      ((presentationTwo (D := D)).totalToInvariants
        (cuspToEllipticUnionHomology D 2 x)) := rfl


public theorem coordinateAfterAddEquiv_apply
    {G : Type*} [AddCommGroup G] {n : ℕ}
    (e : G ≃+ (Fin n → ℤ)) (i : Fin n) (x : G) :
    coordinateAfterAddEquiv e i x = e x i := rfl


end EllipticInteriorMarkedCycleData


end Geometry.AnalyticData

end SphereSixComplex
