module

public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianWangSectionProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianSectionGeneratorCompletion
public import SphereSixComplex.Topology.PaperSectionSevenCuspMappingTorusPhaseBridge

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

private theorem winding_of_real_lift
    {X : Type} [TopologicalSpace X] {x : X}
    (p : Path x x) (f : C(X, UnitAddCircle)) (L : C(unitInterval, ℝ)) (n : ℤ)
    (hpoint : ∀ t : unitInterval,
      f (p t) - f (p 0) = ((L t - L 0 : ℝ) : UnitAddCircle))
    (hend : L 1 - L 0 = n) :
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 f
          (StandardCircleHomologyLiftDegree.loopHomologyClass p)) = n := by
  let q := p.map f.continuous
  let c := f x
  let shift := subtractCircle c
  have hsource : (0 : UnitAddCircle) = shift (f x) := by
    change (0 : UnitAddCircle) = f x - f x
    simp
  let q0 : Path (0 : UnitAddCircle) 0 := (q.map shift.continuous).cast hsource hsource
  let r : Path (0 : UnitAddCircle) 0 :=
    { toFun := fun t ↦ ((L t - L 0 : ℝ) : UnitAddCircle)
      continuous_toFun := continuous_quotient_mk'.comp (L.continuous.sub continuous_const)
      source' := by simp
      target' := by rw [hend]; simp }
  have hq0 : q0 = r := by
    apply Path.ext
    funext t
    change f (p t) - f x = ((L t - L 0 : ℝ) : UnitAddCircle)
    calc
      f (p t) - f x = f (p t) - f (p 0) := by rw [p.source]
      _ = _ := hpoint t
  let H : Path.Homotopy r
      (StandardCircleHomologyLiftDegree.unitCircleIntegerLoop n) :=
    { toFun := fun u ↦
        ((((1 - (u.1 : ℝ)) * (L u.2 - L 0) +
          (u.1 : ℝ) * ((u.2 : ℝ) * (n : ℝ)) : ℝ)) : UnitAddCircle)
      continuous_toFun := by fun_prop
      map_zero_left := by
        intro t
        change
          ((((1 - (0 : ℝ)) * (L t - L 0) +
            (0 : ℝ) * ((t : ℝ) * (n : ℝ)) : ℝ)) : UnitAddCircle) =
            ((L t - L 0 : ℝ) : UnitAddCircle)
        congr 1
        ring
      map_one_left := by
        intro t
        change
          ((((1 - (1 : ℝ)) * (L t - L 0) +
            (1 : ℝ) * ((t : ℝ) * (n : ℝ)) : ℝ)) : UnitAddCircle) =
            (((t : ℝ) * (n : ℝ) : ℝ) : UnitAddCircle)
        congr 1
        ring
      prop' := by
        intro u t ht
        rcases ht with rfl | ht
        · change
            ((((1 - (u : ℝ)) * (L 0 - L 0) +
              (u : ℝ) * ((0 : ℝ) * (n : ℝ)) : ℝ)) : UnitAddCircle) =
              ((L 0 - L 0 : ℝ) : UnitAddCircle)
          congr 1
          ring
        · rw [Set.mem_singleton_iff] at ht
          subst t
          change
            ((((1 - (u : ℝ)) * (L 1 - L 0) +
              (u : ℝ) * ((1 : ℝ) * (n : ℝ)) : ℝ)) : UnitAddCircle) =
              ((L 1 - L 0 : ℝ) : UnitAddCircle)
          rw [hend]
          congr 1
          ring }
  rw [StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass]
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (StandardCircleHomologyLiftDegree.loopHomologyClass q) = n
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
  rw [SphereSixComplex.Topology.FirstHurewiczProof.loopHomologyClass_homotopic H]
  exact StandardCircleHomologyLiftDegree.unitCircleHomologyWinding_integerLoop n

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

/-- The fibre contribution to the cusp source character is invariant under every clutching
iterate. -/
public theorem cuspFiberTwelveFirstCoordinate_zpow
    (x : Periods.PeriodDomain) (k : ℤ) (y : AdditiveTorus x.1) :
    cuspFiberTwelveFirstCoordinate x ((cuspFiberClutching x ^ k) y) =
      cuspFiberTwelveFirstCoordinate x y := by
  induction k using Int.induction_on generalizing y with
  | zero => simp
  | succ k ih =>
      rw [zpow_add_one, Homeomorph.mul_apply, ih,
        cuspFiberTwelveFirstCoordinate_clutching]
  | pred k ih =>
      rw [zpow_sub_one, Homeomorph.mul_apply, ih]
      have h := cuspFiberTwelveFirstCoordinate_clutching x
        ((cuspFiberClutching x).symm y)
      rw [(cuspFiberClutching x).apply_symm_apply] at h
      exact h.symm

/-- On a real mapping-torus representative, the cusp source character is the base height plus
the twelvefold first fibre coordinate. -/
public theorem cuspMeridianSourceCircleMap_realMappingTorus_mk
    (x : Periods.PeriodDomain) (s : ℝ) (y : AdditiveTorus x.1) :
    cuspMeridianSourceCircleMap x
        (CyclicAngularFundamentalDomain.realMappingTorusHomeomorph
          (cuspFiberClutching x)
          (Quotient.mk
            (CyclicAngularFundamentalDomain.realMappingTorusSetoid
              (cuspFiberClutching x)) (s, y))) =
      ((s : ℝ) : UnitAddCircle) + cuspFiberTwelveFirstCoordinate x y := by
  let phi := cuspFiberClutching x
  obtain ⟨p, hp⟩ := CyclicAngularFundamentalDomain.realMappingTorusIntervalProjection_surjective
    phi (Quotient.mk (CyclicAngularFundamentalDomain.realMappingTorusSetoid phi) (s, y))
  rw [← hp,
    CuspPuncturedCollarBridge.realMappingTorusHomeomorph_intervalProjection,
    cuspMeridianSourceCircleMap_cylinderProjection]
  obtain ⟨k, hk⟩ :=
    (CyclicAngularFundamentalDomain.realMappingTorusMk_eq_iff phi (s, y)
      ((p.1 : ℝ), p.2)).mp hp.symm
  have hfirst := congrArg Prod.fst hk
  have hsecond := congrArg Prod.snd hk
  rw [CyclicAngularFundamentalDomain.mappingTorusShift_apply] at hfirst hsecond
  have hfirst' : (p.1 : ℝ) = s - (k : ℝ) := by simpa using hfirst
  have hsecond' : p.2 = (phi ^ k) y := by simpa using hsecond
  rw [hsecond', cuspFiberTwelveFirstCoordinate_zpow, hfirst']
  congr 1
  apply (StandardTorusHomology.unitAddCircle_eq_iff _ _).2
  refine ⟨-k, ?_⟩
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
public theorem actualCuspRadialBaseCircleProjection_additivePoint
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
    C(puncturedLocalCuspQuotient A.starCuspWitness, UnitAddCircle) := by
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
  exact actualCuspRadialBaseCircleProjection_additivePoint A p

private theorem actualCuspAngularPuncturedLoop_apply (t : unitInterval) :
    A.actualCuspAngularPuncturedLoop t =
      additiveCuspBoundaryProjection A.starCuspWitness
        (A.actualCuspAngularLiftPoint t) := by
  rfl

private theorem actualCuspAngularPuncturedLoop_base_winding_neg_one :
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (actualTransportedBaseCircleMap A)
          (StandardCircleHomologyLiftDegree.loopHomologyClass
            A.actualCuspAngularPuncturedLoop)) = -1 := by
  apply winding_neg_one_of_loop A.actualCuspAngularPuncturedLoop
    (actualTransportedBaseCircleMap A)
  intro t
  rw [actualCuspAngularPuncturedLoop_apply A t,
    actualTransportedBaseCircleMap_additivePoint A,
    actualCuspAngularPuncturedLoop_apply A 0,
    actualTransportedBaseCircleMap_additivePoint A]
  change
    ((((A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ)).re : ℝ) : UnitAddCircle) -
      (((A.actualCuspBoundaryCoverBase.1.2 - (0 : ℝ)).re : ℝ) : UnitAddCircle)) =
        (((-(t : ℝ)) : ℝ) : UnitAddCircle)
  rw [← AddCircle.coe_sub]
  congr 1
  simp

/-- The literal actual cusp meridian winds negatively once around the mapping-torus base. -/
public theorem actualCuspMappingTorusMeridian_base_winding_neg_one :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (circleMappingTorusBaseCircleProjection G.clutching)
          (cuspMappingTorusMeridianHomologyClass G
            A.actualCuspLocalBoundaryBase)) = -1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1
        (circleMappingTorusBaseCircleProjection G.clutching)
        (cuspMappingTorusMeridianHomologyClass G
          A.actualCuspLocalBoundaryBase)) = -1
  rw [A.cuspMappingTorusMeridianHomologyClass_eq_actualCuspAngularPuncturedLoop_image]
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1
        (circleMappingTorusBaseCircleProjection G.clutching)
        (integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun
          (StandardCircleHomologyLiftDegree.loopHomologyClass
            A.actualCuspAngularPuncturedLoop))) = -1
  rw [integralSingularHomologyMap_comp_wang]
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1 (actualTransportedBaseCircleMap A)
        (StandardCircleHomologyLiftDegree.loopHomologyClass
          A.actualCuspAngularPuncturedLoop)) = -1
  exact actualCuspAngularPuncturedLoop_base_winding_neg_one A

/-- Equivalently, the literal meridian has Wang invariant coordinate `-1`. -/
public theorem actualCuspMappingTorusMeridian_wangInvariant_neg_one :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    degreeOneWangInvariantEquivInteger G
        ((circleMappingTorusHOnePresentation G.clutching).totalToInvariants
          (cuspMappingTorusMeridianHomologyClass G
            A.actualCuspLocalBoundaryBase)) = -1 := by
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
          A.actualCuspLocalBoundaryBase)) = -1
  rw [← SphereSixComplex.Topology.IdentityPointMappingTorusWindingBoundary.circleMappingTorusBaseCircle_winding_eq_wangBoundary]
  exact actualCuspMappingTorusMeridian_base_winding_neg_one A

/-- The specialization-normalized positive Wang section is the negative of the literal angular
meridian. -/
public theorem actualCuspSelectedPositiveMeridianClass_eq_neg_explicit :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspSelectedPositiveMeridianClass A =
      -(cuspMappingTorusMeridianHomologyClass G
        A.actualCuspLocalBoundaryBase) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply actualCuspSelectedPositiveMeridianClass_eq_neg_explicit_of_normalizations
    A A.actualCuspLocalBoundaryBase
  · exact rawDegreeOneTotalSpecialization_selectedPositiveMeridianClass A
  · change degreeOneWangInvariantEquivInteger G
        ((circleMappingTorusHOnePresentation G.clutching).totalToInvariants
          (-(cuspMappingTorusMeridianHomologyClass G
            A.actualCuspLocalBoundaryBase))) = 1
    rw [map_neg, map_neg,
      actualCuspMappingTorusMeridian_wangInvariant_neg_one]
    norm_num

private noncomputable def actualTransportedSourceCircleMap :
    C(puncturedLocalCuspQuotient A.starCuspWitness, UnitAddCircle) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact A.actualCuspMeridianSourceCircleMap.comp G.totalHomotopyEquiv.toFun

private theorem actualTransportedSourceCircleMap_additivePoint
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    actualTransportedSourceCircleMap A
        (additiveCuspBoundaryProjection A.starCuspWitness p) =
      ((p.1.2.re : ℝ) : UnitAddCircle) +
        cuspFiberTwelveFirstCoordinate
          (cuspBasePoint A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness))
          (additiveTorusProjection
            (cuspBasePoint A.cuspCoordinate
              (markedCuspParameter A.starCuspWitness)).1
            (collarFiberEquiv A.cuspCoordinate
              (markedCuspParameter A.starCuspWitness) p.1.2 p.1.1)) := by
  change cuspMeridianSourceCircleMap
      (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness))
      ((CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness).totalHomotopyEquiv.toFun
        (additiveCuspBoundaryProjection A.starCuspWitness p)) = _
  rw [show additiveCuspBoundaryProjection A.starCuspWitness p =
      collarPeriodPointMap A.starCuspWitness p by rfl]
  change cuspMeridianSourceCircleMap
      (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness))
      ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
        (markedCuspParameter A.starCuspWitness)
        (collarPeriodPointMap A.starCuspWitness p)).2) = _
  rw [puncturedLocalCuspQuotientHomeomorph_apply]
  change cuspMeridianSourceCircleMap
      (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness))
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
  exact cuspMeridianSourceCircleMap_realMappingTorus_mk _ _ _

public noncomputable def actualCuspSourceRealLift : C(unitInterval, ℝ) where
  toFun t :=
    (A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ)).re +
      12 * periodCoordinates
        (cuspBasePoint A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness))
        (collarFiberEquiv A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness)
          (A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ))
          A.actualCuspBoundaryCoverBase.1.1) 0
  continuous_toFun := by
    let x := cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness)
    have hs : A.actualCuspBoundaryCoverBase.1.2 ∈
        cuspHalfPlane A.cuspCoordinate.height :=
      additiveCuspRadiusCover_halfPlane A.starCuspWitness.localWitness.radius_le
        A.actualCuspBoundaryCoverBase
    have hparameter : Continuous (fun t : unitInterval ↦
        A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ)) := by
      fun_prop
    have hparameter_mem : ∀ t : unitInterval,
        A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ) ∈
          cuspHalfPlane A.cuspCoordinate.height := by
      intro t
      simpa [cuspHalfPlane] using hs
    have hlift : Continuous (fun t : unitInterval ↦
        A.cuspCoordinate.lift
          (A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ))) :=
      A.cuspCoordinate.lift_holomorphic.continuousOn.comp_continuous
        hparameter hparameter_mem
    have hmoving : Continuous (fun t : unitInterval ↦
        (movingToFixedCover
          (assembledFuchsianPeriodFunctions A.modular A.localPeriods)
          (A.cuspCoordinate.lift (markedCuspParameter A.starCuspWitness))
          (A.cuspCoordinate.lift
            (A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ)),
              A.actualCuspBoundaryCoverBase.1.1)).2) :=
      continuous_snd.comp
        ((movingToFixedCover_continuous
          (assembledFuchsianPeriodFunctions A.modular A.localPeriods)
          (A.cuspCoordinate.lift (markedCuspParameter A.starCuspWitness))).comp
            (hlift.prodMk continuous_const))
    have hz : Continuous (fun t : unitInterval ↦
        collarFiberEquiv A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness)
          (A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ))
          A.actualCuspBoundaryCoverBase.1.1) := by
      convert hmoving using 1
      funext t
      exact collarFiberEquiv_eq_movingToFixed
        (N := A.cuspCoordinate) _ _ _
    have hc : Continuous (fun t : unitInterval ↦
        periodCoordinates x
          (collarFiberEquiv A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness)
            (A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ))
            A.actualCuspBoundaryCoverBase.1.1) 0) :=
      (continuous_apply 0).comp
        ((fullRankDomain x).realEquiv.symm.continuous.comp hz)
    exact (by fun_prop : Continuous (fun t : unitInterval ↦
      (A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ)).re)).add
        (continuous_const.mul hc)

/-- The twelvefold fibre summand has zero endpoint increment along the literal meridian, so the
source-character lift changes by exactly `-1`. -/
public theorem actualCuspSourceRealLift_endpoint :
    actualCuspSourceRealLift A 1 - actualCuspSourceRealLift A 0 = -1 := by
  let s := A.actualCuspBoundaryCoverBase.1.2
  let zeta := A.actualCuspBoundaryCoverBase.1.1
  let s0 := markedCuspParameter A.starCuspWitness
  let x := cuspBasePoint A.cuspCoordinate s0
  have hs : s ∈ cuspHalfPlane A.cuspCoordinate.height :=
    additiveCuspRadiusCover_halfPlane A.starCuspWitness.localWitness.radius_le
      A.actualCuspBoundaryCoverBase
  have hsub : s - (1 : ℝ) = s + ((-1 : ℤ) : ℂ) := by
    apply Complex.ext
    · simp
      ring
    · simp
  have hshift := collarFiberEquiv_shift (N := A.cuspCoordinate)
    s0 s hs (-1) zeta
  have hcoord : periodCoordinates x
      (collarFiberEquiv A.cuspCoordinate s0 (s - (1 : ℝ)) zeta) 0 =
    periodCoordinates x (collarFiberEquiv A.cuspCoordinate s0 s zeta) 0 := by
    rw [hsub, hshift, neg_neg, zpow_one, cuspFiberLift_apply]
    rw [periodCoordinates, ContinuousLinearEquiv.symm_apply_apply]
    change (rhoLambdaReal g₀
      (periodCoordinates x (collarFiberEquiv A.cuspCoordinate s0 s zeta))) 0 = _
    exact rhoLambdaReal_gZero_firstCoordinate _
  change ((s - (1 : ℝ)).re + 12 *
      periodCoordinates x (collarFiberEquiv A.cuspCoordinate s0 (s - (1 : ℝ)) zeta) 0) -
    ((s - (0 : ℝ)).re + 12 *
      periodCoordinates x (collarFiberEquiv A.cuspCoordinate s0 (s - (0 : ℝ)) zeta) 0) = -1
  rw [hcoord]
  simp

private theorem actualCuspAngularPuncturedLoop_source_winding_neg_one :
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (actualTransportedSourceCircleMap A)
          (StandardCircleHomologyLiftDegree.loopHomologyClass
            A.actualCuspAngularPuncturedLoop)) = -1 := by
  apply winding_of_real_lift A.actualCuspAngularPuncturedLoop
    (actualTransportedSourceCircleMap A) (actualCuspSourceRealLift A) (-1)
  · intro t
    have hvalue (u : unitInterval) :
        actualTransportedSourceCircleMap A (A.actualCuspAngularPuncturedLoop u) =
          ((actualCuspSourceRealLift A u : ℝ) : UnitAddCircle) := by
      rw [actualCuspAngularPuncturedLoop_apply A u,
        actualTransportedSourceCircleMap_additivePoint A,
        cuspFiberTwelveFirstCoordinate_projection]
      change
        (((A.actualCuspBoundaryCoverBase.1.2 - (u : ℝ)).re : ℝ) : UnitAddCircle) +
            (12 : ℤ) •
              ((periodCoordinates
                (cuspBasePoint A.cuspCoordinate
                  (markedCuspParameter A.starCuspWitness))
                (collarFiberEquiv A.cuspCoordinate
                  (markedCuspParameter A.starCuspWitness)
                  (A.actualCuspBoundaryCoverBase.1.2 - (u : ℝ))
                  A.actualCuspBoundaryCoverBase.1.1) 0 : ℝ) : UnitAddCircle) =
          (((A.actualCuspBoundaryCoverBase.1.2 - (u : ℝ)).re +
            12 * periodCoordinates
              (cuspBasePoint A.cuspCoordinate
                (markedCuspParameter A.starCuspWitness))
              (collarFiberEquiv A.cuspCoordinate
                (markedCuspParameter A.starCuspWitness)
                (A.actualCuspBoundaryCoverBase.1.2 - (u : ℝ))
                A.actualCuspBoundaryCoverBase.1.1) 0 : ℝ) : UnitAddCircle)
      rw [← AddCircle.coe_zsmul]
      norm_num [zsmul_eq_mul]
    rw [hvalue t, hvalue 0, ← AddCircle.coe_sub]
  · exact_mod_cast actualCuspSourceRealLift_endpoint A

/-- The literal angular meridian evaluates to `-1` under the full cusp source character. -/
public theorem actualCuspMappingTorusMeridian_source_winding_neg_one :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 A.actualCuspMeridianSourceCircleMap
          (cuspMappingTorusMeridianHomologyClass G
            A.actualCuspLocalBoundaryBase)) = -1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1 A.actualCuspMeridianSourceCircleMap
        (cuspMappingTorusMeridianHomologyClass G
          A.actualCuspLocalBoundaryBase)) = -1
  rw [A.cuspMappingTorusMeridianHomologyClass_eq_actualCuspAngularPuncturedLoop_image]
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1 A.actualCuspMeridianSourceCircleMap
        (integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun
          (StandardCircleHomologyLiftDegree.loopHomologyClass
            A.actualCuspAngularPuncturedLoop))) = -1
  rw [integralSingularHomologyMap_comp_wang]
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1 (actualTransportedSourceCircleMap A)
        (StandardCircleHomologyLiftDegree.loopHomologyClass
          A.actualCuspAngularPuncturedLoop)) = -1
  exact actualCuspAngularPuncturedLoop_source_winding_neg_one A

/-- The specialization-selected positive section evaluates to the positive unit under the full
cusp source character. -/
public theorem actualCuspSelectedPositiveMeridianClass_source_winding_one :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 A.actualCuspMeridianSourceCircleMap
          (actualCuspSelectedPositiveMeridianClass A)) = 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [actualCuspSelectedPositiveMeridianClass_eq_neg_explicit]
  rw [map_neg, map_neg, actualCuspMappingTorusMeridian_source_winding_neg_one]
  norm_num

/-- The actual source circle map realizes the complete corrected degree-one coordinate
`[12, 0, 1]` on the geometric Wang basis. -/
public theorem actualCuspMeridianSourceCircleMap_homologyCoordinate :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    SectionSevenEllipticInteriorMarkedCycleData.actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
        G.geometricWangSections.circleMappingTorusHOneAddEquiv =
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding.comp
        (integralSingularHomologyMap 1 A.actualCuspMeridianSourceCircleMap) := by
  exact actualCuspMeridianSourceCircleMap_homologyCoordinate_of_selectedPositive_winding_one A
    (actualCuspSelectedPositiveMeridianClass_source_winding_one A)

end SphereSixComplex.Geometry.PaperAnalyticData

end
