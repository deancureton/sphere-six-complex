module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspMeridianWangSectionProof
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspMeridianSectionGeneratorCompletion
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspMappingTorusPhaseBridge

/-!
# The orientation of the actual cusp meridian

The radial mapping-torus equivalence sends the additive logarithmic coordinate `s` to the
mapping-torus base coordinate `s.re` modulo integers.  The paper's literal angular meridian is
the path `s - t`, so its base-circle winding is `-1`.  The Wang-boundary comparison then fixes
the previously ambiguous sign of the specialization-normalized degree-one section.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspRadialClutchingConstruction
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.CuspPeriodExpansion
open CuspPuncturedCollarBridge.CuspFiberSpecializationNormalization
open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup

variable (A : PaperAnalyticData)

private def subtractCircle (c : UnitAddCircle) : C(UnitAddCircle, UnitAddCircle) where
  toFun x := x - c
  continuous_toFun := continuous_id.sub continuous_const

private def subtractCircleHomotopy (c : UnitAddCircle) :
    ContinuousMap.Homotopy (subtractCircle c) (ContinuousMap.id UnitAddCircle) where
  toFun u := u.2 + PathConnectedSpace.somePath (-c) 0 u.1
  continuous_toFun := continuous_snd.add
    ((PathConnectedSpace.somePath (-c) 0).continuous.comp continuous_fst)
  map_zero_left x := by simp [subtractCircle, sub_eq_add_neg]
  map_one_left x := by simp

private theorem winding_neg_one_of_loop
    {X : Type} [TopologicalSpace X] {x : X}
    (p : Path x x) (f : C(X, UnitAddCircle))
    (hpoint : ∀ t : unitInterval,
      f (p t) - f (p 0) = (((-(t : ℝ)) : ℝ) : UnitAddCircle)) :
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 f
          (StandardCircleHomologyLiftDegree.loopHomologyClass p)) = -1 := by
  let q := p.map f.continuous
  let c := f x
  let shift := subtractCircle c
  have hsource : (0 : UnitAddCircle) = shift (f x) := by
    change (0 : UnitAddCircle) = f x - f x
    simp
  let q0 : Path (0 : UnitAddCircle) 0 := (q.map shift.continuous).cast hsource hsource
  have hq0 : q0 = StandardCircleHomologyLiftDegree.unitCircleIntegerLoop (-1) := by
    apply Path.ext
    funext t
    change f (p t) - f x = (((t : ℝ) * ((-1 : ℤ) : ℝ) : ℝ) : UnitAddCircle)
    calc
      f (p t) - f x = f (p t) - f (p 0) := by rw [p.source]
      _ = (((-(t : ℝ)) : ℝ) : UnitAddCircle) := hpoint t
      _ = (((t : ℝ) * ((-1 : ℤ) : ℝ) : ℝ) : UnitAddCircle) := by
        congr 1
        ring
  rw [StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass]
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (StandardCircleHomologyLiftDegree.loopHomologyClass q) = -1
  have hshift := integralSingularHomologyMap_eq_of_homotopy 1
    (subtractCircleHomotopy c)
  have hclass :
      integralSingularHomologyMap 1 shift
          (StandardCircleHomologyLiftDegree.loopHomologyClass q) =
        StandardCircleHomologyLiftDegree.loopHomologyClass q := by
    rw [hshift, integralSingularHomologyMap_id_wang]
  rw [← hclass]
  rw [StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass]
  rw [← StandardCircleHomologyLiftDegree.loopHomologyClass_cast
    (q.map shift.continuous) hsource]
  rw [show (q.map shift.continuous).cast hsource hsource = q0 by rfl, hq0]
  exact StandardCircleHomologyLiftDegree.unitCircleHomologyWinding_integerLoop (-1)


/-- The interval-clutching homeomorphism preserves the real height modulo integers. -/
public theorem circleMappingTorusBaseCircleProjection_realMappingTorus_mk
    {T : Type} [TopologicalSpace T] (phi : T ≃ₜ T) (s : ℝ) (y : T) :
    circleMappingTorusBaseCircleProjection phi
        (CyclicAngularFundamentalDomain.realMappingTorusHomeomorph phi
          (Quotient.mk (CyclicAngularFundamentalDomain.realMappingTorusSetoid phi)
            (s, y))) =
      ((s : ℝ) : UnitAddCircle) := by
  obtain ⟨p, hp⟩ := CyclicAngularFundamentalDomain.realMappingTorusIntervalProjection_surjective
    phi (Quotient.mk (CyclicAngularFundamentalDomain.realMappingTorusSetoid phi) (s, y))
  rw [← hp,
    CuspPuncturedCollarBridge.realMappingTorusHomeomorph_intervalProjection,
    circleMappingTorusBaseCircleProjection_cylinderProjection]
  obtain ⟨k, hk⟩ :=
    (CyclicAngularFundamentalDomain.realMappingTorusMk_eq_iff phi (s, y)
      ((p.1 : ℝ), p.2)).mp hp.symm
  have hfirst := congrArg Prod.fst hk
  rw [CyclicAngularFundamentalDomain.mappingTorusShift_apply] at hfirst
  change ((p.1 : ℝ) : UnitAddCircle) = (s : UnitAddCircle)
  apply (StandardTorusHomology.unitAddCircle_eq_iff _ _).2
  refine ⟨-k, ?_⟩
  dsimp at hfirst ⊢
  rw [hfirst]
  push_cast
  ring



private theorem actualRadialBaseCircleProjection_additivePoint_explicit
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
    let _ := G.fiberTopology
    circleMappingTorusBaseCircleProjection G.clutching
        (G.totalHomotopyEquiv.toFun
          (additiveCuspBoundaryProjection A.starCuspWitness p)) =
      ((p.1.2.re : ℝ) : UnitAddCircle) := by
  dsimp only
  rw [show additiveCuspBoundaryProjection A.starCuspWitness p =
      collarPeriodPointMap A.starCuspWitness p by rfl]
  change circleMappingTorusBaseCircleProjection
      (cuspFiberClutching
        (cuspBasePoint A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness)))
      ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
        (markedCuspParameter A.starCuspWitness)
        (collarPeriodPointMap A.starCuspWitness p)).2) = _
  rw [puncturedLocalCuspQuotientHomeomorph_apply]
  change circleMappingTorusBaseCircleProjection
      (cuspFiberClutching
        (cuspBasePoint A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness)))
      (CyclicAngularFundamentalDomain.realMappingTorusHomeomorph
        (cuspFiberClutching
          (cuspBasePoint A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness)))
        (Quotient.mk _
          (p.1.2.re,
            additiveTorusProjection
              (cuspBasePoint A.cuspCoordinate
                (markedCuspParameter A.starCuspWitness)).1
              (collarFiberEquiv A.cuspCoordinate
                (markedCuspParameter A.starCuspWitness) p.1.2 p.1.1)))) = _
  exact circleMappingTorusBaseCircleProjection_realMappingTorus_mk _ _ _

/-- The actual radial equivalence sends an additive cusp point to its logarithmic real part on
the mapping-torus base circle. -/
public theorem cuspRadialBaseCircleProjection_additivePoint
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    circleMappingTorusBaseCircleProjection G.clutching
        (G.totalHomotopyEquiv.toFun
          (additiveCuspBoundaryProjection A.starCuspWitness p)) =
      ((p.1.2.re : ℝ) : UnitAddCircle) := by
  dsimp only
  exact actualRadialBaseCircleProjection_additivePoint_explicit A p

private noncomputable def actualTransportedBaseCircleMap :
    C(PuncturedLocalCuspQuotient A.starCuspWitness, UnitAddCircle) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact (circleMappingTorusBaseCircleProjection G.clutching).comp
    G.totalHomotopyEquiv.toFun

private theorem actualTransportedBaseCircleMap_additivePoint
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    actualTransportedBaseCircleMap A
        (additiveCuspBoundaryProjection A.starCuspWitness p) =
      ((p.1.2.re : ℝ) : UnitAddCircle) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change circleMappingTorusBaseCircleProjection G.clutching
      (G.totalHomotopyEquiv.toFun
        (additiveCuspBoundaryProjection A.starCuspWitness p)) = _
  exact cuspRadialBaseCircleProjection_additivePoint A p

private theorem actualCuspAngularPuncturedLoop_apply (t : unitInterval) :
    A.cuspAngularPuncturedLoop t =
      additiveCuspBoundaryProjection A.starCuspWitness
        (A.cuspAngularLiftPoint t) := by
  rfl

private theorem actualCuspAngularPuncturedLoop_base_winding_neg_one :
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (actualTransportedBaseCircleMap A)
          (StandardCircleHomologyLiftDegree.loopHomologyClass
            A.cuspAngularPuncturedLoop)) = -1 := by
  apply winding_neg_one_of_loop A.cuspAngularPuncturedLoop
    (actualTransportedBaseCircleMap A)
  intro t
  rw [actualCuspAngularPuncturedLoop_apply A t,
    actualTransportedBaseCircleMap_additivePoint A,
    actualCuspAngularPuncturedLoop_apply A 0,
    actualTransportedBaseCircleMap_additivePoint A]
  change
    ((((A.cuspBoundaryCoverBase.1.2 - (t : ℝ)).re : ℝ) : UnitAddCircle) -
      (((A.cuspBoundaryCoverBase.1.2 - (0 : ℝ)).re : ℝ) : UnitAddCircle)) =
        (((-(t : ℝ)) : ℝ) : UnitAddCircle)
  rw [← AddCircle.coe_sub]
  congr 1
  simp

/-- The literal actual cusp meridian winds negatively once around the mapping-torus base. -/
public theorem cuspMappingTorusMeridian_base_winding_neg_one :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (circleMappingTorusBaseCircleProjection G.clutching)
          (cuspMappingTorusMeridianHomologyClass G
            A.cuspLocalBoundaryBase)) = -1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1
        (circleMappingTorusBaseCircleProjection G.clutching)
        (cuspMappingTorusMeridianHomologyClass G
          A.cuspLocalBoundaryBase)) = -1
  rw [A.cuspMappingTorusMeridianHomologyClass_eq_cuspAngularPuncturedLoop_image]
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1
        (circleMappingTorusBaseCircleProjection G.clutching)
        (integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun
          (StandardCircleHomologyLiftDegree.loopHomologyClass
            A.cuspAngularPuncturedLoop))) = -1
  rw [integralSingularHomologyMap_comp_wang]
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1 (actualTransportedBaseCircleMap A)
        (StandardCircleHomologyLiftDegree.loopHomologyClass
          A.cuspAngularPuncturedLoop)) = -1
  exact actualCuspAngularPuncturedLoop_base_winding_neg_one A

/-- Equivalently, the literal meridian has Wang invariant coordinate `-1`. -/
public theorem cuspMappingTorusMeridian_wangInvariant_neg_one :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    degreeOneWangInvariantEquivInteger G
        ((circleMappingTorusHOnePresentation G.clutching).totalToInvariants
          (cuspMappingTorusMeridianHomologyClass G
            A.cuspLocalBoundaryBase)) = -1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let _ : PathConnectedSpace (AdditiveTorus G.fiberParameter) :=
    additiveTorus_pathConnected G.fiberParameter
  let _ : PathConnectedSpace G.Fiber :=
    G.fiberHomeomorph.symm.surjective.pathConnectedSpace
      G.fiberHomeomorph.symm.continuous
  change pathConnectedIntegralHomologyZeroEquivInteger G.Fiber
      ((circleMappingTorusWangPresentationOfCover G.clutching 0).boundary
        (cuspMappingTorusMeridianHomologyClass G
          A.cuspLocalBoundaryBase)) = -1
  rw [← SphereSixComplex.Topology.IdentityPointMappingTorusWindingBoundary.circleMappingTorusBaseCircle_winding_eq_wangBoundary]
  exact cuspMappingTorusMeridian_base_winding_neg_one A

/-- The specialization-normalized positive Wang section is the negative of the literal angular
meridian. -/
public theorem cuspSelectedPositiveMeridianClass_eq_neg_explicit :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    cuspSelectedPositiveMeridianClass A =
      -(cuspMappingTorusMeridianHomologyClass G
        A.cuspLocalBoundaryBase) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply cuspSelectedPositiveMeridianClass_eq_neg_explicit_of_normalizations
    A A.cuspLocalBoundaryBase
  · exact rawDegreeOneTotalSpecialization_selectedPositiveMeridianClass A
  · change degreeOneWangInvariantEquivInteger G
        ((circleMappingTorusHOnePresentation G.clutching).totalToInvariants
          (-(cuspMappingTorusMeridianHomologyClass G
            A.cuspLocalBoundaryBase))) = 1
    rw [map_neg, map_neg,
      cuspMappingTorusMeridian_wangInvariant_neg_one]
    norm_num









end SphereSixComplex.Geometry.PaperAnalyticData

end
