module

public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianProjectionNaturality

/-!
# Chain-level realization of the first cusp invariant suspension

The remaining degree-two comparison is represented by a prism cycle on the radial mapping
torus.  This file records degree-two singular cycles, proves functoriality of their homology
classes, and reduces the marked coordinate identity to an explicit chain image of a six-cycle
basis.  In particular, the fourth basis cycle is the first invariant-suspension prism.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory
open scoped ContinuousMap

namespace SphereSixComplex

/-- An integral singular two-cycle represented as a map from the rank-one free abelian group. -/
public structure DegreeTwoSingularCycle (X : Type) [TopologicalSpace X] where
  chain : AddCommGrpCat.of ℤ ⟶ (IntegralSingularChainComplex X).X 2
  boundary_zero : chain ≫ (IntegralSingularChainComplex X).d 2 1 = 0

namespace DegreeTwoSingularCycle

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Postcompose a singular two-cycle with the chain map induced by a continuous map. -/
public noncomputable def map (c : DegreeTwoSingularCycle X) (f : C(X, Y)) :
    DegreeTwoSingularCycle Y where
  chain := c.chain ≫ (integralSingularChainMap f).f 2
  boundary_zero := by
    rw [Category.assoc, (integralSingularChainMap f).comm 2 1, ← Category.assoc,
      c.boundary_zero]
    simp

/-- The homology-class morphism represented by a singular two-cycle. -/
public noncomputable def homologyClassMorphism (c : DegreeTwoSingularCycle X) :
    AddCommGrpCat.of ℤ ⟶ (IntegralSingularChainComplex X).homology 2 :=
  (IntegralSingularChainComplex X).liftCycles c.chain 1 (by simp) c.boundary_zero ≫
    (IntegralSingularChainComplex X).homologyπ 2

/-- The homology class represented by a singular two-cycle. -/
public noncomputable def homologyClass (c : DegreeTwoSingularCycle X) :
    IntegralSingularHomology 2 X :=
  ConcreteCategory.hom c.homologyClassMorphism 1

/-- Chain maps commute with passage from an explicit cycle to its homology-class morphism. -/
public theorem homologyClassMorphism_naturality
    (c : DegreeTwoSingularCycle X) (f : C(X, Y)) :
    c.homologyClassMorphism ≫
        HomologicalComplex.homologyMap (integralSingularChainMap f) 2 =
      (c.map f).homologyClassMorphism := by
  unfold homologyClassMorphism map
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  rw [HomologicalComplex.liftCycles_comp_cyclesMap]

/-- The induced singular-homology map sends the class of a cycle to the class of its chain
image. -/
public theorem homologyClass_map (c : DegreeTwoSingularCycle X) (f : C(X, Y)) :
    integralSingularHomologyMap 2 f c.homologyClass = (c.map f).homologyClass := by
  have h := congrArg ConcreteCategory.hom (c.homologyClassMorphism_naturality f)
  exact DFunLike.congr_fun h 1

/-- Two cycles with the same underlying chain represent the same homology class. -/
public theorem homologyClass_eq_of_chain_eq (c d : DegreeTwoSingularCycle X)
    (h : c.chain = d.chain) : c.homologyClass = d.homologyClass := by
  cases c with
  | mk c hc =>
    cases d with
    | mk d hd =>
      dsimp at h ⊢
      subst d
      rfl

end DegreeTwoSingularCycle

namespace Geometry.PaperAnalyticData

open CircleMappingTorusHomologyBases
open SectionSevenEllipticTwoDiscHomologyCoordinates
open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

namespace SectionSevenEllipticTwoDiscCoverData

/-- The second normalized elliptic coordinate of a cusp class is its raw Wang boundary
coordinate. -/
public theorem normalizedEllipticInteriorHomologyTwoEquiv_cuspToEllipticInteriorMap_one
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
      (D.cuspNormalizedDegreeTwoSplitting N G))
        (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x) 1 =
      A.actualCuspRawHomologyTwoEquiv x 5 := by
  rw [D.cuspToEllipticInteriorMap_homology]
  let e := integralSingularHomologyEquiv 2
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  change (N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
      (D.cuspNormalizedDegreeTwoSplitting N G))
        (e.symm (e (cuspToEllipticUnionHomology D 2 x))) 1 = _
  rw [e.symm_apply_apply,
    N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv_one]
  exact D.cuspBoundaryCoordinateFormula N G x

/-- Explicit chain representatives for the degree-two mapping-torus basis and their images under
a reference map.  The chain equality at index four is the invariant-suspension prism square;
the coordinate formula records that precisely this prism has first elliptic fibre coordinate
one. -/
public structure CuspEllipticInvariantSuspensionPrismComparison
    (N : A.EllipticBandHomologyAlignment D)
    (G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N)
    (referenceMap :
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      C(CircleMappingTorus G.clutching, A.SectionSevenEllipticInterior)) where
  sourceBasisCycle :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    Fin 6 → DegreeTwoSingularCycle (CircleMappingTorus G.clutching)
  targetImageCycle : Fin 6 → DegreeTwoSingularCycle A.SectionSevenEllipticInterior
  sourceBasisClass :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ∀ i : Fin 6, (sourceBasisCycle i).homologyClass =
      G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1)
  chainImage :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ∀ i : Fin 6, ((sourceBasisCycle i).map referenceMap).chain =
      (targetImageCycle i).chain
  targetCoordinate : ∀ i : Fin 6,
    D.ellipticInteriorDegreeTwoFiberCoordinateHom N G₀
        (targetImageCycle i).homologyClass =
      (Pi.single i 1 : Fin 6 → ℤ) 4

namespace CuspEllipticInvariantSuspensionPrismComparison

variable {D : A.SectionSevenEllipticTwoDiscCoverData}
  {N : A.EllipticBandHomologyAlignment D}
  {G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}
  {referenceMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(CircleMappingTorus G.clutching, A.SectionSevenEllipticInterior)}

/-- The reference map sends every explicit source-basis cycle to the homology class represented
by its target chain image. -/
public theorem referenceMap_on_basis
    (P : D.CuspEllipticInvariantSuspensionPrismComparison N G₀ referenceMap)
    (i : Fin 6) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap 2 referenceMap
        (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1)) =
      (P.targetImageCycle i).homologyClass := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change integralSingularHomologyMap 2 referenceMap
      (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1)) = _
  rw [← P.sourceBasisClass i, DegreeTwoSingularCycle.homologyClass_map]
  exact DegreeTwoSingularCycle.homologyClass_eq_of_chain_eq _ _ (P.chainImage i)

/-- The fourth source cycle is the first invariant-suspension prism, and its image has normalized
elliptic fibre coordinate one. -/
public theorem firstInvariantSuspensionPrism_coordinate
    (P : D.CuspEllipticInvariantSuspensionPrismComparison N G₀ referenceMap) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    D.ellipticInteriorDegreeTwoFiberCoordinateHom N G₀
        (integralSingularHomologyMap 2 referenceMap
          (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
            (Pi.single (4 : Fin 6) 1))) = 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change D.ellipticInteriorDegreeTwoFiberCoordinateHom N G₀
      (integralSingularHomologyMap 2 referenceMap
        (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
          (Pi.single (4 : Fin 6) 1))) = 1
  rw [P.referenceMap_on_basis 4, P.targetCoordinate 4]
  simp

/-- The explicit prism-chain comparison computes the remaining degree-two coordinate map. -/
public theorem degreeTwoFiber
    (P : D.CuspEllipticInvariantSuspensionPrismComparison N G₀ referenceMap) :
    (D.ellipticInteriorDegreeTwoFiberCoordinateHom N G₀).comp
        (integralSingularHomologyMap 2 referenceMap) =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      coordinateAfterAddEquiv G.geometricWangSections.circleMappingTorusHTwoAddEquiv 4 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply addMonoidHom_ext_of_equiv_pi_single_one
    G.geometricWangSections.circleMappingTorusHTwoAddEquiv
  intro i
  rw [AddMonoidHom.comp_apply, coordinateAfterAddEquiv_apply,
    AddEquiv.apply_symm_apply, P.referenceMap_on_basis i]
  exact P.targetCoordinate i

end CuspEllipticInvariantSuspensionPrismComparison

/-- Structural data for the cusp comparison before the normalized index-four calculation.  The
five complementary target cycles are identified with multiples of the swept basis class, so
their first normalized coordinate vanishes without any scalar coordinate assumption. -/
public structure CuspEllipticMappingTorusPrismGeometricData
    (N : A.EllipticBandHomologyAlignment D)
    (G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) where
  meridianProjection : D.CuspEllipticMappingTorusMeridianProjectionComparison N
  referenceMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(CircleMappingTorus G.clutching, A.SectionSevenEllipticInterior)
  modelHomotopy :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    D.cuspMappingTorusToEllipticInteriorMap.Homotopic referenceMap
  sourceBasisCycle :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    Fin 6 → DegreeTwoSingularCycle (CircleMappingTorus G.clutching)
  targetImageCycle : Fin 6 → DegreeTwoSingularCycle A.SectionSevenEllipticInterior
  sourceBasisClass :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ∀ i : Fin 6, (sourceBasisCycle i).homologyClass =
      G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1)
  chainImage :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ∀ i : Fin 6, ((sourceBasisCycle i).map referenceMap).chain =
      (targetImageCycle i).chain
  targetComplementCoefficient : Fin 6 → ℤ
  targetComplementSweptClass : ∀ i : Fin 6, i ≠ 4 →
    (targetImageCycle i).homologyClass =
      targetComplementCoefficient i •
        (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
          (D.cuspNormalizedDegreeTwoSplitting N G₀)).symm (Pi.single (1 : Fin 2) 1)

/-- The sole normalized prism calculation: the image of the fourth mapping-torus basis cycle is
the first normalized elliptic-interior basis class. -/
public structure NormalizedIndexFourPrismCalculation
    {N : A.EllipticBandHomologyAlignment D}
    {G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}
    (C : D.CuspEllipticMappingTorusPrismGeometricData N G₀) : Prop where
  indexFourClass :
    (C.targetImageCycle 4).homologyClass =
      (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
        (D.cuspNormalizedDegreeTwoSplitting N G₀)).symm (Pi.single (0 : Fin 2) 1)

/-- The sole paper-specific scalar left by the prism comparison: with the geometric orientation,
the fourth prism has coefficient one on the normalized elliptic fibre class. -/
public structure NormalizedIndexFourPrismCoefficientCalculation
    {N : A.EllipticBandHomologyAlignment D}
    {G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}
    (C : D.CuspEllipticMappingTorusPrismGeometricData N G₀) : Prop where
  coefficient :
    (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
      (D.cuspNormalizedDegreeTwoSplitting N G₀))
        (C.targetImageCycle 4).homologyClass 0 = 1

namespace CuspEllipticMappingTorusPrismGeometricData

variable {D : A.SectionSevenEllipticTwoDiscCoverData}
  {N : A.EllipticBandHomologyAlignment D}
  {G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- The reference map sends each explicit source basis cycle to its specified target chain
image. -/
public theorem referenceMap_on_basis
    (C : D.CuspEllipticMappingTorusPrismGeometricData N G₀) (i : Fin 6) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap 2 C.referenceMap
        (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1)) =
      (C.targetImageCycle i).homologyClass := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change integralSingularHomologyMap 2 C.referenceMap
      (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1)) = _
  rw [← C.sourceBasisClass i, DegreeTwoSingularCycle.homologyClass_map]
  exact DegreeTwoSingularCycle.homologyClass_eq_of_chain_eq _ _ (C.chainImage i)

/-- The swept coordinate of the fourth target cycle vanishes.  This is forced by the cusp
boundary formula, since the fourth raw Wang basis vector has fifth coordinate zero. -/
public theorem targetIndexFour_sweptCoordinate_zero
    (C : D.CuspEllipticMappingTorusPrismGeometricData N G₀) :
    let E := N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
      (D.cuspNormalizedDegreeTwoSplitting N G₀)
    E (C.targetImageCycle 4).homologyClass 1 = 0 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let E := N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
    (D.cuspNormalizedDegreeTwoSplitting N G₀)
  let x := A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)
  have hx :
      integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun x =
        G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
          (Pi.single (4 : Fin 6) 1) := by
    apply G.geometricWangSections.circleMappingTorusHTwoAddEquiv.injective
    rw [← actualCuspRawHomologyTwoEquiv_apply_mappingTorus A x]
    simp [x]
  have hactual :
      E (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x) 1 = 0 := by
    rw [D.normalizedEllipticInteriorHomologyTwoEquiv_cuspToEllipticInteriorMap_one]
    simp [x]
  have hhom := DFunLike.congr_fun
    (coordinate_comp_integralSingularHomologyMap_eq_of_homotopic
      C.modelHomotopy 2 (coordinateAfterAddEquiv E 1))
    (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
      (Pi.single (4 : Fin 6) 1))
  simp only [AddMonoidHom.comp_apply, coordinateAfterAddEquiv_apply] at hhom
  calc
    E (C.targetImageCycle 4).homologyClass 1 =
        E (integralSingularHomologyMap 2 C.referenceMap
          (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
            (Pi.single (4 : Fin 6) 1))) 1 := by
      rw [C.referenceMap_on_basis 4]
    _ = E (integralSingularHomologyMap 2 D.cuspMappingTorusToEllipticInteriorMap
          (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
            (Pi.single (4 : Fin 6) 1))) 1 := hhom.symm
    _ = E (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x) 1 := by
      rw [D.cuspToEllipticInteriorMap_homology_mappingTorusModel 2 x, hx]
    _ = 0 := hactual

/-- The scalar coefficient calculation and the forced vanishing of the swept coordinate recover
the full normalized class identity. -/
public theorem normalizedIndexFourPrismCalculation
    (C : D.CuspEllipticMappingTorusPrismGeometricData N G₀)
    (I : D.NormalizedIndexFourPrismCoefficientCalculation C) :
    D.NormalizedIndexFourPrismCalculation C := by
  let E := N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
    (D.cuspNormalizedDegreeTwoSplitting N G₀)
  constructor
  apply E.injective
  rw [E.apply_symm_apply]
  funext i
  fin_cases i
  · simpa [E] using I.coefficient
  · simpa [E] using C.targetIndexFour_sweptCoordinate_zero

/-- The structural comparison and the single normalized prism calculation recover the explicit
cycle package used by homology naturality. -/
public noncomputable def suspensionPrismComparison
    (C : D.CuspEllipticMappingTorusPrismGeometricData N G₀)
    (I : D.NormalizedIndexFourPrismCalculation C) :
    D.CuspEllipticInvariantSuspensionPrismComparison N G₀ C.referenceMap where
  sourceBasisCycle := C.sourceBasisCycle
  targetImageCycle := C.targetImageCycle
  sourceBasisClass := C.sourceBasisClass
  chainImage := C.chainImage
  targetCoordinate i := by
    let E := N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
      (D.cuspNormalizedDegreeTwoSplitting N G₀)
    change E (C.targetImageCycle i).homologyClass 0 =
      (Pi.single i 1 : Fin 6 → ℤ) 4
    by_cases hi : i = 4
    · subst i
      rw [I.indexFourClass, E.apply_symm_apply]
      simp
    · rw [C.targetComplementSweptClass i hi, map_zsmul, E.apply_symm_apply]
      rw [Pi.single_eq_of_ne (Ne.symm hi)]
      simp

/-- The structural data reduces the complete coordinate comparison to the normalized index-four
prism calculation. -/
public theorem coordinateComparison
    (C : D.CuspEllipticMappingTorusPrismGeometricData N G₀)
    (I : D.NormalizedIndexFourPrismCoefficientCalculation C) :
    D.CuspEllipticMappingTorusCoordinateComparison N G₀ :=
  { degreeOne := C.meridianProjection.degreeOne
    degreeTwoFiber := by
      rw [coordinate_comp_integralSingularHomologyMap_eq_of_homotopic C.modelHomotopy]
      exact (C.suspensionPrismComparison (C.normalizedIndexFourPrismCalculation I)).degreeTwoFiber }

end CuspEllipticMappingTorusPrismGeometricData

/-- The final structural cusp package: meridian naturality is a projection square, while the
degree-two comparison is an explicit basis of singular cycles whose fourth member is the first
invariant-suspension prism. -/
public structure CuspEllipticMappingTorusPrismGeometricComparison
    (N : A.EllipticBandHomologyAlignment D)
    (G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) where
  meridianProjection : D.CuspEllipticMappingTorusMeridianProjectionComparison N
  referenceMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(CircleMappingTorus G.clutching, A.SectionSevenEllipticInterior)
  modelHomotopy :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    D.cuspMappingTorusToEllipticInteriorMap.Homotopic referenceMap
  suspensionPrism :
    D.CuspEllipticInvariantSuspensionPrismComparison N G₀ referenceMap

namespace CuspEllipticMappingTorusPrismGeometricComparison

variable {D : A.SectionSevenEllipticTwoDiscCoverData}
  {N : A.EllipticBandHomologyAlignment D}
  {G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- Projection naturality and prism-chain naturality give the complete mapping-torus coordinate
comparison. -/
public theorem coordinateComparison
    (C : D.CuspEllipticMappingTorusPrismGeometricComparison N G₀) :
    D.CuspEllipticMappingTorusCoordinateComparison N G₀ where
  degreeOne := C.meridianProjection.degreeOne
  degreeTwoFiber := by
    rw [coordinate_comp_integralSingularHomologyMap_eq_of_homotopic C.modelHomotopy]
    exact C.suspensionPrism.degreeTwoFiber

end CuspEllipticMappingTorusPrismGeometricComparison

end SectionSevenEllipticTwoDiscCoverData

end Geometry.PaperAnalyticData

end SphereSixComplex

end
