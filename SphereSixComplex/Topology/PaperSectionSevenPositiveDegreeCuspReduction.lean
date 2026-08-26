module

public import SphereSixComplex.Topology.PaperSectionSevenCuspPullbackWangComparison

/-!
# Final cusp-basis reduction for the Section 7 positive-degree assembly

The canonical pullback-cover boundary calculation supplies the degree-two boundary coordinates.
After that, only three degree-one and five degree-two fibre-coordinate checks remain.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscHomologyCoordinates
open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData} {D : A.SectionSevenEllipticTwoDiscCoverData}

/-- The Mayer--Vietoris bridge canonically obtained from the six pulled-back cusp-cover boundary
computations. -/
public theorem SectionSevenCuspPulledBackBoundaryBasisBridge.mayerVietorisBridge
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    A.SectionSevenCuspDegreeTwoMayerVietorisBasisBridge N :=
  SectionSevenEllipticTwoDiscCoverData.SectionSevenCuspPulledBackBoundaryBasisBridge.toMayerVietorisBasisBridge
    D N G

/-- The six pulled-back boundary calculations obtained from the single Wang-boundary map
comparison. -/
public theorem SectionSevenCuspPulledBackWangBoundaryComparison.pulledBackBoundaryBasisBridge
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackWangBoundaryComparison N) :
    D.SectionSevenCuspPulledBackBoundaryBasisBridge N :=
  SectionSevenEllipticTwoDiscCoverData.SectionSevenCuspPulledBackWangBoundaryComparison.toPulledBackBoundaryBasisBridge
    D N G

/-- The pulled-back boundary basis obtained from the marked Wang-boundary comparison. -/
public theorem SectionSevenCuspMarkedBoundaryComparison.pulledBackBoundaryBasisBridge
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspMarkedBoundaryComparison N) :
    D.SectionSevenCuspPulledBackBoundaryBasisBridge N :=
  SectionSevenEllipticTwoDiscCoverData.SectionSevenCuspPulledBackWangBoundaryComparison.toPulledBackBoundaryBasisBridge
    D N
      (SectionSevenEllipticTwoDiscCoverData.SectionSevenCuspMarkedBoundaryComparison.toPulledBackWangBoundaryComparison
        D N G)

/-- The exact eight scalar comparisons remaining after the six canonical cusp-cover boundary
computations. -/
public structure SectionSevenPositiveDegreeCuspBasisInput
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) : Prop where
  degreeOne : ∀ i : Fin 3,
    N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
        (cuspToEllipticUnionHomology D 1
          (A.actualCuspRawHomologyOneEquiv.symm (Pi.single i 1))) 0 =
      (Pi.single i 1 : Fin 3 → ℤ) 2
  degreeTwoFiber : ∀ i : Fin 6, i ≠ 5 →
    N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
        (N.actualHomologyCoordinates.degreeTwoCuspE5SplittingOfCoordinates
          (SectionSevenEllipticInteriorMarkedCycleData.degreeTwoCuspBoundaryCoordinates_of_basis N
            (fun j ↦
              (SectionSevenCuspPulledBackBoundaryBasisBridge.mayerVietorisBridge N G).boundaryCoordinates
                N j)))
        (cuspToEllipticUnionHomology D 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) 0 =
      (Pi.single i 1 : Fin 6 → ℤ) 4

/-- The residual cusp comparison expressed without choosing basis vectors: the included
degree-one meridian coordinate and the degree-two fibre coordinate are the corresponding raw
cusp coordinate homomorphisms. -/
public structure SectionSevenPositiveDegreeCuspCoordinateComparison
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) : Prop where
  degreeOneCoordinateHom :
    cuspDegreeOneCoordinateHom N =
      coordinateAfterAddEquiv A.actualCuspRawHomologyOneEquiv 2
  degreeTwoFiberCoordinateHom :
    cuspDegreeTwoFiberCoordinateHom N
        (degreeTwoCuspBoundaryCoordinates_of_basis N
          (fun i ↦
            (SectionSevenCuspPulledBackBoundaryBasisBridge.mayerVietorisBridge N G).boundaryCoordinates
              N i)) =
      coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 4

namespace SectionSevenPositiveDegreeCuspCoordinateComparison

variable {N : A.EllipticBandHomologyAlignment D}
  {G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- The two coordinate-homomorphism identities imply all eight residual basis checks. -/
public theorem toCuspBasisInput
    (C : A.SectionSevenPositiveDegreeCuspCoordinateComparison N G) :
    A.SectionSevenPositiveDegreeCuspBasisInput N G where
  degreeOne i := by
    have h := DFunLike.congr_fun C.degreeOneCoordinateHom
      (A.actualCuspRawHomologyOneEquiv.symm (Pi.single i 1))
    simpa [cuspDegreeOneCoordinateHom_apply, coordinateAfterAddEquiv_apply] using h
  degreeTwoFiber i hi := by
    have h := DFunLike.congr_fun C.degreeTwoFiberCoordinateHom
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))
    simpa [cuspDegreeTwoFiberCoordinateHom_apply, coordinateAfterAddEquiv_apply] using h

end SectionSevenPositiveDegreeCuspCoordinateComparison

namespace SectionSevenPositiveDegreeCuspBasisInput

variable {N : A.EllipticBandHomologyAlignment D}
  {G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- The eight basis checks are equivalent to the two coordinate-homomorphism identities.  The
missing `e₅` fibre evaluation is zero because `e₅` defines the swept-section splitting. -/
public theorem coordinateComparison
    (C : A.SectionSevenPositiveDegreeCuspBasisInput N G) :
    A.SectionSevenPositiveDegreeCuspCoordinateComparison N G where
  degreeOneCoordinateHom := by
    apply addMonoidHom_ext_of_equiv_pi_single_one A.actualCuspRawHomologyOneEquiv
    intro i
    rw [cuspDegreeOneCoordinateHom_apply, coordinateAfterAddEquiv_apply,
      AddEquiv.apply_symm_apply]
    exact C.degreeOne i
  degreeTwoFiberCoordinateHom := by
    apply addMonoidHom_ext_of_equiv_pi_single_one A.actualCuspRawHomologyTwoEquiv
    intro i
    rw [cuspDegreeTwoFiberCoordinateHom_apply, coordinateAfterAddEquiv_apply,
      AddEquiv.apply_symm_apply]
    by_cases hi : i = 5
    · subst i
      simpa [degreeTwoCuspE5Generator] using
        degreeTwoCuspE5_fiberCoordinate_zero N
          (degreeTwoCuspBoundaryCoordinates_of_basis N
            (fun i ↦
              (SectionSevenCuspPulledBackBoundaryBasisBridge.mayerVietorisBridge N G).boundaryCoordinates
                N i))
    · exact C.degreeTwoFiber i hi

/-- The eight remaining scalar calculations assemble into the marked-cycle package. -/
public noncomputable def markedCycles
    (C : A.SectionSevenPositiveDegreeCuspBasisInput N G) :
    A.SectionSevenEllipticInteriorMarkedCycleData D :=
  SectionSevenEllipticInteriorMarkedCycleData.ofCuspMayerVietorisBasisBridge
    N (SectionSevenCuspPulledBackBoundaryBasisBridge.mayerVietorisBridge N G)
      C.degreeOne C.degreeTwoFiber

/-- The cusp-basis input supplies the production positive-degree homology assembly. -/
public noncomputable def positiveDegreeHomologyAssembly
    (C : A.SectionSevenPositiveDegreeCuspBasisInput N G) :
    A.SectionSevenPositiveDegreeHomologyAssembly :=
  C.markedCycles.positiveDegreeHomologyAssembly

end SectionSevenPositiveDegreeCuspBasisInput

/-- The original eight basis evaluations and the two coordinate-map comparisons are logically
equivalent. -/
public theorem sectionSevenPositiveDegreeCuspBasisInput_iff_coordinateComparison
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    A.SectionSevenPositiveDegreeCuspBasisInput N G ↔
      A.SectionSevenPositiveDegreeCuspCoordinateComparison N G :=
  ⟨SectionSevenPositiveDegreeCuspBasisInput.coordinateComparison,
    SectionSevenPositiveDegreeCuspCoordinateComparison.toCuspBasisInput⟩

/-- The remaining positive-degree input expressed as one Wang-boundary comparison and the eight
residual scalar coordinates. -/
public structure SectionSevenPositiveDegreeWangInput
    (N : A.EllipticBandHomologyAlignment D) : Prop where
  boundary : D.SectionSevenCuspPulledBackWangBoundaryComparison N
  scalar : A.SectionSevenPositiveDegreeCuspBasisInput N
    (SectionSevenCuspPulledBackWangBoundaryComparison.pulledBackBoundaryBasisBridge N boundary)

namespace SectionSevenPositiveDegreeWangInput

variable {N : A.EllipticBandHomologyAlignment D}

/-- The Wang comparison and eight residual scalar coordinates supply the production assembly. -/
public noncomputable def positiveDegreeHomologyAssembly
    (C : A.SectionSevenPositiveDegreeWangInput N) :
    A.SectionSevenPositiveDegreeHomologyAssembly :=
  C.scalar.positiveDegreeHomologyAssembly

end SectionSevenPositiveDegreeWangInput

/-- The remaining positive-degree input stated as three exact marked-coordinate comparisons:
one boundary comparison and two inclusion-coordinate homomorphism identities. -/
public structure SectionSevenPositiveDegreeMarkedCoordinateInput
    (N : A.EllipticBandHomologyAlignment D) : Prop where
  boundary : D.SectionSevenCuspMarkedBoundaryComparison N
  inclusionCoordinates : A.SectionSevenPositiveDegreeCuspCoordinateComparison N
    (SectionSevenCuspMarkedBoundaryComparison.pulledBackBoundaryBasisBridge N boundary)

namespace SectionSevenPositiveDegreeMarkedCoordinateInput

variable {N : A.EllipticBandHomologyAlignment D}

/-- The three marked-coordinate comparisons supply the production positive-degree assembly. -/
public noncomputable def positiveDegreeHomologyAssembly
    (C : A.SectionSevenPositiveDegreeMarkedCoordinateInput N) :
    A.SectionSevenPositiveDegreeHomologyAssembly :=
  C.inclusionCoordinates.toCuspBasisInput.positiveDegreeHomologyAssembly

end SectionSevenPositiveDegreeMarkedCoordinateInput

end SphereSixComplex.Geometry.PaperAnalyticData
