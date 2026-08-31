module

public import SphereSixComplex.Topology.PaperEllipticInteriorCycleDecomposition
public import SphereSixComplex.Topology.PaperSectionSevenEllipticTwoDiscCoverRealization

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

open SectionSevenEllipticTwoDiscHomologyCoordinates

variable {A : PaperAnalyticData}

/-- The marked band and cusp-cycle data remaining after the actual finite-cover calculation. -/
public structure SectionSevenEllipticInteriorMarkedCycleData
    (D : A.SectionSevenEllipticTwoDiscCoverData) where
  alignment : A.EllipticBandHomologyAlignment D
  splitting :
    WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D))
  cycleDecomposition :
    A.SectionSevenEllipticInteriorCycleDecomposition
      alignment.actualHomologyCoordinates splitting

namespace SectionSevenEllipticInteriorMarkedCycleData

variable {D : A.SectionSevenEllipticTwoDiscCoverData}
  (M : A.SectionSevenEllipticInteriorMarkedCycleData D)

/-- Build the marked-cycle package from the three scalar comparisons supplied by a concrete
cycle model. -/
public def ofRawScalarCoordinates
    (N : A.EllipticBandHomologyAlignment D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (hOne : ∀ x : IntegralSingularHomology 1
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
          (cuspToEllipticUnionHomology D 1 x) 0 =
        actualCuspEllipticDegreeOneRawCoordinate (A.actualCuspRawHomologyOneEquiv x))
    (hTwoFiber : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv S
          (cuspToEllipticUnionHomology D 2 x) 0 =
        actualCuspEllipticDegreeTwoFiberRawCoordinate (A.actualCuspRawHomologyTwoEquiv x))
    (hTwoOne : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv S
          (cuspToEllipticUnionHomology D 2 x) 1 =
        A.actualCuspRawHomologyTwoEquiv x 5) :
    A.SectionSevenEllipticInteriorMarkedCycleData D where
  alignment := N
  splitting := S
  cycleDecomposition :=
    SectionSevenEllipticInteriorCycleDecomposition.ofRawScalarCoordinates
      hOne hTwoFiber hTwoOne

/-- Build the marked-cycle package from a cusp boundary formula and the remaining fibre
coordinate formula.  The included positive cusp `e₅` class determines the swept-cycle section,
so no arbitrary splitting is supplied. -/
public noncomputable def ofCuspBoundaryCoordinates
    (N : A.EllipticBandHomologyAlignment D)
    (hOne : ∀ x : IntegralSingularHomology 1
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
          (cuspToEllipticUnionHomology D 1 x) 0 =
        actualCuspEllipticDegreeOneRawCoordinate (A.actualCuspRawHomologyOneEquiv x))
    (hBoundary : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
          ((presentationTwo (D := D)).totalToInvariants
            (cuspToEllipticUnionHomology D 2 x)) =
        A.actualCuspRawHomologyTwoEquiv x 5)
    (hTwoFiber : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
          (N.actualHomologyCoordinates.degreeTwoCuspE5SplittingOfCoordinates hBoundary)
          (cuspToEllipticUnionHomology D 2 x) 0 =
        actualCuspEllipticDegreeTwoFiberRawCoordinate (A.actualCuspRawHomologyTwoEquiv x)) :
    A.SectionSevenEllipticInteriorMarkedCycleData D := by
  let B := N.actualHomologyCoordinates
  let S := B.degreeTwoCuspE5SplittingOfCoordinates hBoundary
  apply ofRawScalarCoordinates N S hOne hTwoFiber
  intro x
  rw [B.normalizedUnionHomologyTwoEquiv_one]
  exact hBoundary x

/-- Evaluate one coordinate after an additive equivalence to a finite integer lattice. -/
public def coordinateAfterAddEquiv {G : Type*} [AddCommGroup G] {n : ℕ}
    (e : G ≃+ (Fin n → ℤ)) (i : Fin n) : G →+ ℤ where
  toFun x := e x i
  map_zero' := by simp
  map_add' x y := by simp

/-- Evaluate the corrected elliptic degree-one functional after an additive equivalence. -/
public def actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
    {G : Type*} [AddCommGroup G] (e : G ≃+ (Fin 3 → ℤ)) : G →+ ℤ where
  toFun x := actualCuspEllipticDegreeOneRawCoordinate (e x)
  map_zero' := by simp [actualCuspEllipticDegreeOneRawCoordinate]
  map_add' x y := by simp [actualCuspEllipticDegreeOneRawCoordinate]; ring

/-- Evaluate the corrected elliptic degree-two fibre functional after an additive equivalence. -/
public def actualCuspEllipticDegreeTwoFiberCoordinateAfterAddEquiv
    {G : Type*} [AddCommGroup G] (e : G ≃+ (Fin 6 → ℤ)) : G →+ ℤ where
  toFun x := actualCuspEllipticDegreeTwoFiberRawCoordinate (e x)
  map_zero' := by simp [actualCuspEllipticDegreeTwoFiberRawCoordinate]
  map_add' x y := by simp [actualCuspEllipticDegreeTwoFiberRawCoordinate]; ring

/-- The first normalized elliptic-interior coordinate of an included cusp degree-one class. -/
public noncomputable def cuspDegreeOneCoordinateHom
    (N : A.EllipticBandHomologyAlignment D) :
    IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0) →+ ℤ where
  toFun x := N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
    (cuspToEllipticUnionHomology D 1 x) 0
  map_zero' := by simp [cuspToEllipticUnionHomology]
  map_add' x y := by simp [cuspToEllipticUnionHomology]

public theorem cuspDegreeOneCoordinateHom_apply (N : A.EllipticBandHomologyAlignment D) (x) :
    cuspDegreeOneCoordinateHom N x =
      N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
      (cuspToEllipticUnionHomology D 1 x) 0 := rfl

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

/-- The normalized fibre coordinate of an included cusp degree-two class. -/
public noncomputable def cuspDegreeTwoFiberCoordinateHom
    (N : A.EllipticBandHomologyAlignment D)
    (hBoundary : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
          ((presentationTwo (D := D)).totalToInvariants
            (cuspToEllipticUnionHomology D 2 x)) =
        A.actualCuspRawHomologyTwoEquiv x 5) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+ ℤ where
  toFun x := N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
    (N.actualHomologyCoordinates.degreeTwoCuspE5SplittingOfCoordinates hBoundary)
    (cuspToEllipticUnionHomology D 2 x) 0
  map_zero' := by simp [cuspToEllipticUnionHomology]
  map_add' x y := by simp [cuspToEllipticUnionHomology]

public theorem cuspDegreeTwoFiberCoordinateHom_apply
    (N : A.EllipticBandHomologyAlignment D)
    (hBoundary : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
          ((presentationTwo (D := D)).totalToInvariants
            (cuspToEllipticUnionHomology D 2 x)) =
        A.actualCuspRawHomologyTwoEquiv x 5) (x) :
    cuspDegreeTwoFiberCoordinateHom N hBoundary x =
      N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
        (N.actualHomologyCoordinates.degreeTwoCuspE5SplittingOfCoordinates hBoundary)
        (cuspToEllipticUnionHomology D 2 x) 0 := rfl

public theorem coordinateAfterAddEquiv_apply
    {G : Type*} [AddCommGroup G] {n : ℕ}
    (e : G ≃+ (Fin n → ℤ)) (i : Fin n) (x : G) :
    coordinateAfterAddEquiv e i x = e x i := rfl

/-- Checking the degree-two cusp boundary coordinate on the six raw basis vectors proves the
coordinate formula for every cusp class. -/
public theorem degreeTwoCuspBoundaryCoordinates_of_basis
    (N : A.EllipticBandHomologyAlignment D)
    (hBoundaryBasis : ∀ i : Fin 6,
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
          ((presentationTwo (D := D)).totalToInvariants
            (cuspToEllipticUnionHomology D 2
              (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)))) =
        (Pi.single i 1 : Fin 6 → ℤ) 5) :
    ∀ x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
          ((presentationTwo (D := D)).totalToInvariants
            (cuspToEllipticUnionHomology D 2 x)) =
        A.actualCuspRawHomologyTwoEquiv x 5 := by
  have h := addMonoidHom_ext_of_equiv_pi_single_one
    A.actualCuspRawHomologyTwoEquiv (cuspDegreeTwoBoundaryCoordinateHom N)
      (coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 5)
    (fun i => by
      rw [cuspDegreeTwoBoundaryCoordinateHom_apply, coordinateAfterAddEquiv_apply,
        AddEquiv.apply_symm_apply]
      exact hBoundaryBasis i)
  exact DFunLike.congr_fun h

/-- Build the marked-cycle package by checking the remaining cusp coordinate identities only on
the three raw degree-one basis vectors and the six raw degree-two basis vectors. -/
public noncomputable def ofCuspBoundaryBasisCoordinates
    (N : A.EllipticBandHomologyAlignment D)
    (hOneBasis : ∀ i : Fin 3,
      N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
          (cuspToEllipticUnionHomology D 1
            (A.actualCuspRawHomologyOneEquiv.symm (Pi.single i 1))) 0 =
        actualCuspEllipticDegreeOneRawCoordinate (Pi.single i 1))
    (hBoundaryBasis : ∀ i : Fin 6,
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
          ((presentationTwo (D := D)).totalToInvariants
            (cuspToEllipticUnionHomology D 2
              (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)))) =
        (Pi.single i 1 : Fin 6 → ℤ) 5)
    (hTwoFiberBasis : ∀ i : Fin 6,
      N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
          (N.actualHomologyCoordinates.degreeTwoCuspE5SplittingOfCoordinates
            (degreeTwoCuspBoundaryCoordinates_of_basis N hBoundaryBasis))
          (cuspToEllipticUnionHomology D 2
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) 0 =
        actualCuspEllipticDegreeTwoFiberRawCoordinate (Pi.single i 1)) :
    A.SectionSevenEllipticInteriorMarkedCycleData D := by
  have hOneMap := addMonoidHom_ext_of_equiv_pi_single_one
    A.actualCuspRawHomologyOneEquiv (cuspDegreeOneCoordinateHom N)
      (actualCuspEllipticDegreeOneCoordinateAfterAddEquiv A.actualCuspRawHomologyOneEquiv)
      (fun i => by
        rw [cuspDegreeOneCoordinateHom_apply]
        change _ = actualCuspEllipticDegreeOneRawCoordinate
          (A.actualCuspRawHomologyOneEquiv
            (A.actualCuspRawHomologyOneEquiv.symm (Pi.single i 1)))
        rw [AddEquiv.apply_symm_apply]
        exact hOneBasis i)
  have hOne : ∀ x : IntegralSingularHomology 1
      (A.openEmbeddingStarData.collarSource 0),
    N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
        (cuspToEllipticUnionHomology D 1 x) 0 =
      actualCuspEllipticDegreeOneRawCoordinate
        (A.actualCuspRawHomologyOneEquiv x) := DFunLike.congr_fun hOneMap
  have hBoundary : ∀ x : IntegralSingularHomology 2
      (A.openEmbeddingStarData.collarSource 0),
    N.actualHomologyCoordinates.degreeTwoInvariantEquiv
        ((presentationTwo (D := D)).totalToInvariants
          (cuspToEllipticUnionHomology D 2 x)) =
      A.actualCuspRawHomologyTwoEquiv x 5 :=
    degreeTwoCuspBoundaryCoordinates_of_basis N hBoundaryBasis
  have hTwoFiberMap := addMonoidHom_ext_of_equiv_pi_single_one
    A.actualCuspRawHomologyTwoEquiv (cuspDegreeTwoFiberCoordinateHom N hBoundary)
      (actualCuspEllipticDegreeTwoFiberCoordinateAfterAddEquiv
        A.actualCuspRawHomologyTwoEquiv)
      (fun i => by
        rw [cuspDegreeTwoFiberCoordinateHom_apply]
        change _ = actualCuspEllipticDegreeTwoFiberRawCoordinate
          (A.actualCuspRawHomologyTwoEquiv
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)))
        rw [AddEquiv.apply_symm_apply]
        exact hTwoFiberBasis i)
  exact ofCuspBoundaryCoordinates N hOne hBoundary (DFunLike.congr_fun hTwoFiberMap)

/-- The marked-cycle data supplies the production positive-degree homology assembly. -/
public def positiveDegreeHomologyAssembly :
    A.SectionSevenPositiveDegreeHomologyAssembly :=
  sectionSevenPositiveDegreeHomologyAssemblyOfActualEllipticData
    M.alignment M.splitting M.cycleDecomposition

end SectionSevenEllipticInteriorMarkedCycleData

/-- The exact remaining geometric realization for the Section 7 positive-degree calculation. -/
public structure SectionSevenPositiveDegreeGeometricRealization (A : PaperAnalyticData) where
  allocation : A.SectionSevenEllipticCentralAllocation
  radial : allocation.RadialRealization
  markedCycles :
    A.SectionSevenEllipticInteriorMarkedCycleData
      radial.toSectionSevenEllipticTwoDiscCoverData

namespace SectionSevenPositiveDegreeGeometricRealization

variable (R : SectionSevenPositiveDegreeGeometricRealization A)

/-- A complete geometric realization discharges the positive-degree Section 7 input. -/
public def positiveDegreeHomologyAssembly :
    A.SectionSevenPositiveDegreeHomologyAssembly :=
  R.markedCycles.positiveDegreeHomologyAssembly

end SectionSevenPositiveDegreeGeometricRealization

end Geometry.PaperAnalyticData

end SphereSixComplex
