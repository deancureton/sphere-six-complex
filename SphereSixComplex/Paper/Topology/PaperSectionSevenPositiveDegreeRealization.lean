module

public import SphereSixComplex.Paper.Topology.PaperEllipticInteriorCycleDecomposition
public import SphereSixComplex.Paper.Topology.PaperSectionSevenEllipticTwoDiscCoverRealization

/-!
# Production input for the Section 7 positive-degree calculation

The finite-cover homology calculation is now fixed.  The remaining input is geometric: a radial
two-disc realization, its marked band transport, a swept-cycle splitting, and the cycle comparison
at the cusp boundary.  This module packages exactly those dependent choices and derives the
positive-degree homology assembly without adding a trust boundary.
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

namespace Geometry.PaperAnalyticData

open EllipticTwoDiscHomologyCoordinates

variable {A : PaperAnalyticData}


namespace EllipticInteriorMarkedCycleData

variable {D : A.EllipticTwoDiscCoverData}



/-- Evaluate one coordinate after an additive equivalence to a finite integer lattice. -/
public def coordinateAfterAddEquiv {G : Type*} [AddCommGroup G] {n : ℕ}
    (e : G ≃+ (Fin n → ℤ)) (i : Fin n) : G →+ ℤ where
  toFun x := e x i
  map_zero' := by simp
  map_add' x y := by simp

/-- Evaluate the corrected elliptic degree-one functional after an additive equivalence. -/
public def actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
    {G : Type*} [AddCommGroup G] (e : G ≃+ (Fin 3 → ℤ)) : G →+ ℤ where
  toFun x := cuspEllipticDegreeOneRawCoordinate (e x)
  map_zero' := by simp [cuspEllipticDegreeOneRawCoordinate]
  map_add' x y := by simp [cuspEllipticDegreeOneRawCoordinate]; ring


/-- The first normalized elliptic-interior coordinate of an included cusp degree-one class. -/
public noncomputable def cuspDegreeOneCoordinateHom
    (N : A.EllipticBandHomologyAlignment D) :
    IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0) →+ ℤ where
  toFun x := N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
    (cuspToEllipticUnionHomology D 1 x) 0
  map_zero' := by simp [cuspToEllipticUnionHomology]
  map_add' x y := by simp [cuspToEllipticUnionHomology]


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


end Geometry.PaperAnalyticData

end SphereSixComplex
