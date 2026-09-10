module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspPullbackWangComparison

/-!
# Final cusp-basis reduction for the Section 7 positive-degree assembly

The canonical pullback-cover boundary calculation supplies the degree-two boundary coordinates.
After that, only three degree-one and five degree-two fibre-coordinate checks remain.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open EllipticTwoDiscHomologyCoordinates
open EllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData} {D : A.EllipticTwoDiscCoverData}

/-- The Mayer--Vietoris bridge canonically obtained from the six pulled-back cusp-cover boundary
computations. -/
public theorem SectionSevenCuspPulledBackBoundaryBasisBridge.mayerVietorisBridge
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    A.CuspDegreeTwoMayerVietorisBasisBridge N :=
  EllipticTwoDiscCoverData.SectionSevenCuspPulledBackBoundaryBasisBridge.toMayerVietorisBasisBridge
    D N G

/-- The six pulled-back boundary calculations obtained from the single Wang-boundary map
comparison. -/
public theorem SectionSevenCuspPulledBackWangBoundaryComparison.pulledBackBoundaryBasisBridge
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackWangBoundaryComparison N) :
    D.SectionSevenCuspPulledBackBoundaryBasisBridge N :=
  EllipticTwoDiscCoverData.SectionSevenCuspPulledBackWangBoundaryComparison.toPulledBackBoundaryBasisBridge
    D N G

/-- The pulled-back boundary basis obtained from the marked Wang-boundary comparison. -/
public theorem SectionSevenCuspMarkedBoundaryComparison.pulledBackBoundaryBasisBridge
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspMarkedBoundaryComparison N) :
    D.SectionSevenCuspPulledBackBoundaryBasisBridge N :=
  EllipticTwoDiscCoverData.SectionSevenCuspPulledBackWangBoundaryComparison.toPulledBackBoundaryBasisBridge
    D N
      (EllipticTwoDiscCoverData.SectionSevenCuspMarkedBoundaryComparison.toPulledBackWangBoundaryComparison
        D N G)

/-- The exact eight scalar comparisons remaining after the six canonical cusp-cover boundary
computations. -/
public structure PositiveDegreeCuspBasisInput
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) : Prop where
  degreeOne : ∀ i : Fin 3,
    N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
        (cuspToEllipticUnionHomology D 1
          (A.cuspRawHomologyOneEquiv.symm (Pi.single i 1))) 0 =
      cuspEllipticDegreeOneRawCoordinate (Pi.single i 1)
  degreeTwoFiber : ∀ i : Fin 6, i ≠ 5 →
    N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
        (N.actualHomologyCoordinates.degreeTwoCuspE5SplittingOfCoordinates
          (EllipticInteriorMarkedCycleData.degreeTwoCuspBoundaryCoordinates_of_basis N
            (fun j ↦
              (SectionSevenCuspPulledBackBoundaryBasisBridge.mayerVietorisBridge N G).boundaryCoordinates
                N j)))
        (cuspToEllipticUnionHomology D 2
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1))) 0 =
      cuspEllipticDegreeTwoFiberRawCoordinate (Pi.single i 1)

/-- The residual cusp comparison expressed without choosing basis vectors: the included
degree-one meridian coordinate and the degree-two fibre coordinate are the corresponding raw
cusp coordinate homomorphisms. -/
public structure PositiveDegreeCuspCoordinateComparison
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) : Prop where
  degreeOneCoordinateHom :
    cuspDegreeOneCoordinateHom N =
      actualCuspEllipticDegreeOneCoordinateAfterAddEquiv A.cuspRawHomologyOneEquiv
  degreeTwoFiberCoordinateHom :
    cuspDegreeTwoFiberCoordinateHom N
        (degreeTwoCuspBoundaryCoordinates_of_basis N
          (fun i ↦
            (SectionSevenCuspPulledBackBoundaryBasisBridge.mayerVietorisBridge N G).boundaryCoordinates
              N i)) =
      actualCuspEllipticDegreeTwoFiberCoordinateAfterAddEquiv
        A.cuspRawHomologyTwoEquiv

namespace PositiveDegreeCuspCoordinateComparison

variable {N : A.EllipticBandHomologyAlignment D}
  {G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- The two coordinate-homomorphism identities imply all eight residual basis checks. -/
public theorem toCuspBasisInput
    (C : A.PositiveDegreeCuspCoordinateComparison N G) :
    A.PositiveDegreeCuspBasisInput N G where
  degreeOne i := by
    have h := DFunLike.congr_fun C.degreeOneCoordinateHom
      (A.cuspRawHomologyOneEquiv.symm (Pi.single i 1))
    change _ = cuspEllipticDegreeOneRawCoordinate (Pi.single i 1)
    simpa [cuspDegreeOneCoordinateHom_apply,
      actualCuspEllipticDegreeOneCoordinateAfterAddEquiv] using h
  degreeTwoFiber i hi := by
    have h := DFunLike.congr_fun C.degreeTwoFiberCoordinateHom
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1))
    change _ = cuspEllipticDegreeTwoFiberRawCoordinate (Pi.single i 1)
    simpa [cuspDegreeTwoFiberCoordinateHom_apply,
      actualCuspEllipticDegreeTwoFiberCoordinateAfterAddEquiv] using h

end PositiveDegreeCuspCoordinateComparison

namespace PositiveDegreeCuspBasisInput

variable {N : A.EllipticBandHomologyAlignment D}
  {G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- The eight basis checks are equivalent to the two coordinate-homomorphism identities.  The
missing `e₅` fibre evaluation is zero because `e₅` defines the swept-section splitting. -/
public theorem coordinateComparison
    (C : A.PositiveDegreeCuspBasisInput N G) :
    A.PositiveDegreeCuspCoordinateComparison N G where
  degreeOneCoordinateHom := by
    apply addMonoidHom_ext_of_equiv_pi_single_one A.cuspRawHomologyOneEquiv
    intro i
    rw [cuspDegreeOneCoordinateHom_apply]
    change _ = cuspEllipticDegreeOneRawCoordinate
      (A.cuspRawHomologyOneEquiv
        (A.cuspRawHomologyOneEquiv.symm (Pi.single i 1)))
    rw [AddEquiv.apply_symm_apply]
    exact C.degreeOne i
  degreeTwoFiberCoordinateHom := by
    apply addMonoidHom_ext_of_equiv_pi_single_one A.cuspRawHomologyTwoEquiv
    intro i
    rw [cuspDegreeTwoFiberCoordinateHom_apply]
    change _ = cuspEllipticDegreeTwoFiberRawCoordinate
      (A.cuspRawHomologyTwoEquiv
        (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1)))
    rw [AddEquiv.apply_symm_apply]
    by_cases hi : i = 5
    · subst i
      simpa [degreeTwoCuspE5Generator,
        cuspEllipticDegreeTwoFiberRawCoordinate] using
        degreeTwoCuspE5_fiberCoordinate_zero N
          (degreeTwoCuspBoundaryCoordinates_of_basis N
            (fun i ↦
              (SectionSevenCuspPulledBackBoundaryBasisBridge.mayerVietorisBridge N G).boundaryCoordinates
                N i))
    · exact C.degreeTwoFiber i hi

/-- The eight remaining scalar calculations assemble into the marked-cycle package. -/
public noncomputable def markedCycles
    (C : A.PositiveDegreeCuspBasisInput N G) :
    A.EllipticInteriorMarkedCycleData D :=
  EllipticInteriorMarkedCycleData.ofCuspMayerVietorisBasisBridge
    N (SectionSevenCuspPulledBackBoundaryBasisBridge.mayerVietorisBridge N G)
      C.degreeOne C.degreeTwoFiber

/-- The cusp-basis input supplies the production positive-degree homology assembly. -/
public noncomputable def positiveDegreeHomologyAssembly
    (C : A.PositiveDegreeCuspBasisInput N G) :
    A.PositiveDegreeHomologyAssembly :=
  C.markedCycles.positiveDegreeHomologyAssembly

end PositiveDegreeCuspBasisInput

/-- The original eight basis evaluations and the two coordinate-map comparisons are logically
equivalent. -/
public theorem positiveDegreeCuspBasisInput_iff_coordinateComparison
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    A.PositiveDegreeCuspBasisInput N G ↔
      A.PositiveDegreeCuspCoordinateComparison N G :=
  ⟨PositiveDegreeCuspBasisInput.coordinateComparison,
    PositiveDegreeCuspCoordinateComparison.toCuspBasisInput⟩

/-- The remaining positive-degree input expressed as one Wang-boundary comparison and the eight
residual scalar coordinates. -/
public structure PositiveDegreeWangInput
    (N : A.EllipticBandHomologyAlignment D) : Prop where
  boundary : D.SectionSevenCuspPulledBackWangBoundaryComparison N
  scalar : A.PositiveDegreeCuspBasisInput N
    (SectionSevenCuspPulledBackWangBoundaryComparison.pulledBackBoundaryBasisBridge N boundary)

namespace PositiveDegreeWangInput

variable {N : A.EllipticBandHomologyAlignment D}

/-- The Wang comparison and eight residual scalar coordinates supply the production assembly. -/
public noncomputable def positiveDegreeHomologyAssembly
    (C : A.PositiveDegreeWangInput N) :
    A.PositiveDegreeHomologyAssembly :=
  C.scalar.positiveDegreeHomologyAssembly

end PositiveDegreeWangInput

/-- The remaining positive-degree input stated as three exact marked-coordinate comparisons:
one boundary comparison and two inclusion-coordinate homomorphism identities. -/
public structure PositiveDegreeMarkedCoordinateInput
    (N : A.EllipticBandHomologyAlignment D) : Prop where
  boundary : D.SectionSevenCuspMarkedBoundaryComparison N
  inclusionCoordinates : A.PositiveDegreeCuspCoordinateComparison N
    (SectionSevenCuspMarkedBoundaryComparison.pulledBackBoundaryBasisBridge N boundary)

namespace PositiveDegreeMarkedCoordinateInput

variable {N : A.EllipticBandHomologyAlignment D}

/-- The three marked-coordinate comparisons supply the production positive-degree assembly. -/
public noncomputable def positiveDegreeHomologyAssembly
    (C : A.PositiveDegreeMarkedCoordinateInput N) :
    A.PositiveDegreeHomologyAssembly :=
  C.inclusionCoordinates.toCuspBasisInput.positiveDegreeHomologyAssembly

end PositiveDegreeMarkedCoordinateInput

end SphereSixComplex.Geometry.PaperAnalyticData
