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

namespace SectionSevenPositiveDegreeCuspBasisInput

variable {N : A.EllipticBandHomologyAlignment D}
  {G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

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

end SphereSixComplex.Geometry.PaperAnalyticData
