module

public import SphereSixComplex.Topology.PaperSectionSevenCuspInvariantSuspensionPrismNaturality

/-!
# Explicit cycles for the structural Section 7 cusp prism package

Every integral singular degree-two homology class is represented by an explicit singular cycle.
Applying this to the geometric Wang basis of the radial cusp mapping torus supplies the explicit
cycle basis, its chain images and their homology classes required by the structural Section 7
cusp package, with the mapping-torus model map itself as reference map.  The swept normalized
degree-two basis class of the elliptic interior is identified with the image of the second cusp
suspension class, which settles the swept description at index five.

What remains of the package are exactly two geometric coordinate identities: the degree-one
meridian identity on the mapping-torus model, and the vanishing of the normalized elliptic fibre
coordinate on the four cusp fibre coinvariant classes.  The meridian projection square is shown
to be equivalent to the former.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory
open scoped ContinuousMap

namespace SphereSixComplex

/-- Every integral singular degree-two homology class is represented by an explicit cycle. -/
public theorem exists_degreeTwoSingularCycle {X : Type} [TopologicalSpace X]
    (x : IntegralSingularHomology 2 X) :
    ∃ c : DegreeTwoSingularCycle X, c.homologyClass = x := by
  classical
  let K := IntegralSingularChainComplex X
  obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ 2)).1 inferInstance x
  let p : K.X 2 := K.iCycles 2 y
  have hp : K.d 2 1 p = 0 := by
    have h := CategoryTheory.congr_fun (K.iCycles_d 2 1) y
    simp only [CategoryTheory.comp_apply] at h
    simpa using h
  have hchain : (AddCommGrpCat.asHom p) ≫ K.d 2 1 = 0 := by
    apply AddCommGrpCat.int_hom_ext
    change K.d 2 1 ((AddCommGrpCat.asHom p) 1) = _
    rw [AddCommGrpCat.asHom_hom_apply, one_zsmul]
    simpa using hp
  refine ⟨⟨AddCommGrpCat.asHom p, hchain⟩, ?_⟩
  have hnext : (ComplexShape.down ℕ).next 2 = 1 := by simp
  have hl : K.liftCycles (AddCommGrpCat.asHom p) 1 hnext hchain ≫ K.iCycles 2 =
      AddCommGrpCat.asHom p := K.liftCycles_i _ _ _ _
  have hly : ConcreteCategory.hom
      (K.liftCycles (AddCommGrpCat.asHom p) 1 hnext hchain) 1 = y := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles 2)).1 inferInstance
    have h := CategoryTheory.congr_fun hl 1
    simp only [CategoryTheory.comp_apply] at h
    rw [h, AddCommGrpCat.asHom_hom_apply, one_zsmul]
  show ConcreteCategory.hom
    (K.liftCycles (AddCommGrpCat.asHom p) 1 hnext hchain ≫ K.homologyπ 2) 1 = x
  rw [CategoryTheory.comp_apply, hly, hy]

/-- The identity map induces the identity on integral singular homology. -/
public theorem integralSingularHomologyMap_id {X : Type} [TopologicalSpace X] (k : ℕ)
    (x : IntegralSingularHomology k X) :
    integralSingularHomologyMap k (ContinuousMap.id X) x = x := by
  change ConcreteCategory.hom
    (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
      (TopCat.ofHom (ContinuousMap.id X))) x = x
  rw [show TopCat.ofHom (ContinuousMap.id X) = CategoryTheory.CategoryStruct.id (TopCat.of X) from
    rfl, CategoryTheory.Functor.map_id]
  rfl

namespace Geometry.PaperAnalyticData

open CircleMappingTorusHomologyBases
open SectionSevenEllipticTwoDiscHomologyCoordinates
open SectionSevenEllipticInteriorMarkedCycleData
open SectionSevenEllipticTwoDiscCoverData

variable {A : PaperAnalyticData} {D : A.SectionSevenEllipticTwoDiscCoverData}
  {N : A.EllipticBandHomologyAlignment D}
  {G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- The normalized fibre coordinate of an included cusp class is computed inside the literal
union of the two elliptic sides. -/
public theorem normalizedEllipticInteriorHomologyTwoEquiv_cuspToEllipticInteriorMap_zero
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
      (D.cuspNormalizedDegreeTwoSplitting N G₀))
        (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x) 0 =
      N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
        (D.cuspNormalizedDegreeTwoSplitting N G₀)
        (cuspToEllipticUnionHomology D 2 x) 0 :=
  D.ellipticInteriorDegreeTwoFiberCoordinateHom_cuspToEllipticInteriorMap N G₀ x

/-- The swept normalized degree-two basis class of the elliptic interior is the image of the
second cusp suspension class. -/
public theorem normalizedEllipticInteriorHomologyTwoEquiv_symm_single_one :
    (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
      (D.cuspNormalizedDegreeTwoSplitting N G₀)).symm (Pi.single (1 : Fin 2) 1) =
      integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) := by
  have h0 : (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
      (D.cuspNormalizedDegreeTwoSplitting N G₀))
        (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))) 0 = 0 := by
    rw [normalizedEllipticInteriorHomologyTwoEquiv_cuspToEllipticInteriorMap_zero]
    exact degreeTwoCuspE5_fiberCoordinate_zero N (D.cuspBoundaryCoordinateFormula N G₀)
  have h1 : (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
      (D.cuspNormalizedDegreeTwoSplitting N G₀))
        (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))) 1 = 1 := by
    rw [D.normalizedEllipticInteriorHomologyTwoEquiv_cuspToEllipticInteriorMap_one N G₀,
      AddEquiv.apply_symm_apply]
    simp
  rw [AddEquiv.symm_apply_eq]
  funext i
  fin_cases i
  · simpa using h0.symm
  · simpa using h1.symm

/-- The mapping-torus model map sends the geometric Wang degree-two basis to the image of the
corresponding raw cusp basis class. -/
public theorem cuspMappingTorusToEllipticInteriorMap_basis (i : Fin 6) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap 2 D.cuspMappingTorusToEllipticInteriorMap
        (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1)) =
      integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let x := A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)
  have hx :
      integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun x =
        G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1) := by
    apply G.geometricWangSections.circleMappingTorusHTwoAddEquiv.injective
    rw [← actualCuspRawHomologyTwoEquiv_apply_mappingTorus A x]
    simp [x]
  change integralSingularHomologyMap 2 D.cuspMappingTorusToEllipticInteriorMap
      (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1)) =
    integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x
  rw [D.cuspToEllipticInteriorMap_homology_mappingTorusModel 2 x, hx]

/-- An explicit degree-two singular cycle on the radial cusp mapping torus representing the
`i`-th geometric Wang basis class. -/
public noncomputable def cuspMappingTorusBasisCycle (A : PaperAnalyticData) (i : Fin 6) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    DegreeTwoSingularCycle (CircleMappingTorus G.clutching) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact (exists_degreeTwoSingularCycle
    (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1))).choose

/-- The explicit cusp mapping-torus cycles do represent the geometric Wang basis. -/
public theorem cuspMappingTorusBasisCycle_homologyClass (A : PaperAnalyticData) (i : Fin 6) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (A.cuspMappingTorusBasisCycle i).homologyClass =
      G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact (exists_degreeTwoSingularCycle
    (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1))).choose_spec

/-- The chain image of the `i`-th explicit basis cycle represents the image of the `i`-th raw
cusp basis class. -/
public theorem cuspMappingTorusBasisCycle_map_homologyClass (i : Fin 6) :
    ((A.cuspMappingTorusBasisCycle i).map D.cuspMappingTorusToEllipticInteriorMap).homologyClass =
      integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)) := by
  rw [← DegreeTwoSingularCycle.homologyClass_map (A.cuspMappingTorusBasisCycle i)
    D.cuspMappingTorusToEllipticInteriorMap, cuspMappingTorusBasisCycle_homologyClass A i]
  exact cuspMappingTorusToEllipticInteriorMap_basis i

/-- The chain image of the fifth explicit basis cycle is exactly the swept normalized degree-two
basis class of the elliptic interior. -/
public theorem cuspMappingTorusBasisCycle_map_homologyClass_five :
    ((A.cuspMappingTorusBasisCycle 5).map D.cuspMappingTorusToEllipticInteriorMap).homologyClass =
      (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
        (D.cuspNormalizedDegreeTwoSplitting N G₀)).symm (Pi.single (1 : Fin 2) 1) := by
  rw [cuspMappingTorusBasisCycle_map_homologyClass,
    normalizedEllipticInteriorHomologyTwoEquiv_symm_single_one]

/-- The meridian projection square is nothing more than the degree-one mapping-torus coordinate
identity: the elliptic interior itself, with the identity projection, realizes both coordinates
over a common base. -/
public noncomputable def cuspEllipticMappingTorusMeridianProjectionComparison_of_degreeOne
    (h : (D.ellipticInteriorDegreeOneCoordinateHom N).comp
        (integralSingularHomologyMap 1 D.cuspMappingTorusToEllipticInteriorMap) =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      coordinateAfterAddEquiv G.geometricWangSections.circleMappingTorusHOneAddEquiv 2) :
    D.CuspEllipticMappingTorusMeridianProjectionComparison N where
  Base := A.SectionSevenEllipticInterior
  baseTopology := inferInstance
  baseCoordinate := D.ellipticInteriorDegreeOneCoordinateHom N
  sourceProjection :=
    { projection := D.cuspMappingTorusToEllipticInteriorMap
      coordinate_eq := h.symm }
  targetProjection :=
    { projection := ContinuousMap.id _
      coordinate_eq := by
        ext x
        exact (congrArg (D.ellipticInteriorDegreeOneCoordinateHom N)
          (integralSingularHomologyMap_id 1 x)).symm }
  projectionHomotopy := ContinuousMap.Homotopic.refl _

/-- The structural Section 7 cusp prism package, assembled from the meridian projection square
and the vanishing of the normalized elliptic fibre coordinate on the four cusp fibre coinvariant
classes.  All the remaining fields are supplied unconditionally: the reference map is the
mapping-torus model itself, the source basis is an explicit family of singular cycles, the target
cycles are their chain images, and the second suspension class is exactly the swept normalized
basis class. -/
public noncomputable def cuspEllipticMappingTorusPrismGeometricData_of_fiberCoinvariantVanishing
    (M : D.CuspEllipticMappingTorusMeridianProjectionComparison N)
    (hvanish : ∀ i : Fin 6, i ≠ 4 → i ≠ 5 →
      (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
        (D.cuspNormalizedDegreeTwoSplitting N G₀))
          (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) 0 = 0) :
    D.CuspEllipticMappingTorusPrismGeometricData N G₀ := by
  classical
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  let f := D.cuspMappingTorusToEllipticInteriorMap
  refine
    { meridianProjection := M
      referenceMap := f
      modelHomotopy := ContinuousMap.Homotopic.refl _
      sourceBasisCycle := A.cuspMappingTorusBasisCycle
      targetImageCycle := fun i ↦ (A.cuspMappingTorusBasisCycle i).map f
      sourceBasisClass := cuspMappingTorusBasisCycle_homologyClass A
      chainImage := fun _ ↦ rfl
      targetComplementCoefficient := fun i ↦ (Pi.single i 1 : Fin 6 → ℤ) 5
      targetComplementSweptClass := ?_ }
  intro i hi
  by_cases h5 : i = 5
  · subst h5
    rw [cuspMappingTorusBasisCycle_map_homologyClass_five (N := N) (G₀ := G₀)]
    simp
  rw [cuspMappingTorusBasisCycle_map_homologyClass]
  rw [Pi.single_eq_of_ne (Ne.symm h5), zero_smul]
  apply (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
    (D.cuspNormalizedDegreeTwoSplitting N G₀)).injective
  rw [map_zero]
  funext j
  fin_cases j
  · simpa using hvanish i hi h5
  · have h1 := D.normalizedEllipticInteriorHomologyTwoEquiv_cuspToEllipticInteriorMap_one N G₀
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))
    have hz : (Pi.single i 1 : Fin 6 → ℤ) 5 = 0 := Pi.single_eq_of_ne (Ne.symm h5) 1
    rw [AddEquiv.apply_symm_apply, hz] at h1
    simpa using h1

/-- The structural Section 7 cusp prism package assembled from the two residual geometric
coordinate identities: the degree-one meridian identity on the mapping-torus model, and the
vanishing of the normalized elliptic fibre coordinate on the four cusp fibre coinvariant
classes. -/
public noncomputable def cuspEllipticMappingTorusPrismGeometricData_of_coordinateIdentities
    (hOne : (D.ellipticInteriorDegreeOneCoordinateHom N).comp
        (integralSingularHomologyMap 1 D.cuspMappingTorusToEllipticInteriorMap) =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      coordinateAfterAddEquiv G.geometricWangSections.circleMappingTorusHOneAddEquiv 2)
    (hTwo : ∀ i : Fin 6, i ≠ 4 → i ≠ 5 →
      (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
        (D.cuspNormalizedDegreeTwoSplitting N G₀))
          (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) 0 = 0) :
    D.CuspEllipticMappingTorusPrismGeometricData N G₀ :=
  cuspEllipticMappingTorusPrismGeometricData_of_fiberCoinvariantVanishing
    (cuspEllipticMappingTorusMeridianProjectionComparison_of_degreeOne hOne) hTwo

/-- The Section 7 cusp package in the exact shape used by the affine radial completion, given the
two residual geometric coordinate identities. -/
public noncomputable def cuspEllipticMappingTorusPrismGeometricData_proved_of_coordinateIdentities
    (R : A.SectionSevenAffineRadialCompletionInput)
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment)
    (hOne : (R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
        (integralSingularHomologyMap 1
          R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap) =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      coordinateAfterAddEquiv G.geometricWangSections.circleMappingTorusHOneAddEquiv 2)
    (hTwo : ∀ i : Fin 6, i ≠ 4 → i ≠ 5 →
      (R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
        (R.twoDiscCover.cuspNormalizedDegreeTwoSplitting R.homologyAlignment
          W.pulledBackBoundaryBasisBridge))
          (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) 0 = 0) :
    R.twoDiscCover.CuspEllipticMappingTorusPrismGeometricData R.homologyAlignment
      W.pulledBackBoundaryBasisBridge :=
  cuspEllipticMappingTorusPrismGeometricData_of_coordinateIdentities hOne hTwo

end Geometry.PaperAnalyticData

end SphereSixComplex

end
