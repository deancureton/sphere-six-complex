module

public import
  SphereSixComplex.Paper.Topology.PaperSectionSevenCuspInvariantBasisFromRadialCompatibilityCompletion

/-!
# The orientation-free index-five cusp coefficient

The adaptive two-leg cover identifies the index-five boundary with a primitive fibre class before
it enters the cusp collar.  This file isolates the strictly weaker map-level fact needed to retain
that primitivity after transport to the elliptic band. The inverse radial equivalence has a
constant radius, so the height is independent of the fibre. Two scalar crossing times therefore
give continuous full-fibre slices into the adaptive overlap without a continuous-selection
argument. Their signed Mayer--Vietoris comparison remains to be proved.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory TopologicalSpace

namespace SphereSixComplex

/-- A split carrier of a class with an integral coordinate equal to one can only have a unit
coefficient along a rank-one target. -/
public theorem integerCoefficient_sq_eq_one_of_split
    {S B : Type*} [AddCommGroup S] [AddCommGroup B]
    (source : S) (target : B) (sourceCoordinate : S →+ ℤ) (read : B →+ S)
    (b : ℤ) (generator : B)
    (hsource : sourceCoordinate source = 1)
    (hsplit : read target = source) (hfactor : target = b • generator) :
    b * b = 1 := by
  have hvalue := congrArg sourceCoordinate (hsplit.symm.trans
    (congrArg read hfactor |>.trans (map_zsmul read b generator)))
  rw [hsource] at hvalue
  simp only [map_zsmul] at hvalue
  change 1 = b * _ at hvalue
  have hb : IsUnit b := by
    rw [isUnit_iff_dvd_one]
    exact ⟨_, hvalue⟩
  rcases (Int.isUnit_iff.mp hb) with hb | hb
  · rw [hb]
    norm_num
  · rw [hb]
    norm_num

end SphereSixComplex

namespace SphereSixComplex.Geometry.PaperAnalyticData

open EllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData}

namespace EllipticTwoDiscCoverData

open CuspPuncturedCollarBridge CuspRadialClutchingConstruction CuspPeriodExpansion

public theorem actualCuspAdditiveLift_norm_eq_fixedRadius
    (z : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      CircleMappingTorus G.clutching) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ‖cuspQ (actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)).1.2‖ =
      ((openRadialIntervalHomotopyEquivUnit
        A.starCuspWitness.localWitness.radius_pos).invFun () : ℝ) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let a := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
  have ha := additiveCuspBoundaryProjection_actualCuspAdditiveLift
    (G.totalHomotopyEquiv.invFun z)
  have hcoord := congrArg Prod.fst
    (puncturedLocalCuspQuotientHomeomorph_apply A.starCuspWitness
      (markedCuspParameter A.starCuspWitness) a)
  have hnorm : ‖cuspQ a.1.2‖ =
      ((G.totalHomeomorph (G.totalHomotopyEquiv.invFun z)).1 : ℝ) := by
    rw [← ha]
    exact (congrArg Subtype.val hcoord).symm
  change ‖cuspQ a.1.2‖ = _
  rw [hnorm]
  change ((G.totalHomeomorph (G.totalHomeomorph.symm _)).1 : ℝ) = _
  rw [G.totalHomeomorph.apply_symm_apply]
  rfl

public theorem actualCuspCylinderHeightLoop_independent_fiber
    (R : A.AffineRadialCompletionInput)
    (y y' : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) (t : unitInterval) :
    actualCuspCylinderHeightLoop R y t = actualCuspCylinderHeightLoop R y' t := by
  rw [actualCuspCylinderHeightLoop_apply, actualCuspCylinderHeightLoop_apply,
    R.twoDiscCover.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus,
    R.twoDiscCover.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus]
  dsimp only
  rw [actualCuspAdditiveLift_cuspQ_eq_mappingTorusCylinderPolar (t, y),
    actualCuspAdditiveLift_cuspQ_eq_mappingTorusCylinderPolar (t, y'),
    actualCuspAdditiveLift_norm_eq_fixedRadius,
    actualCuspAdditiveLift_norm_eq_fixedRadius]

public theorem actualCuspCylinderHeightLoop_uniform_middle_crossings
    (R : A.AffineRadialCompletionInput)
    (y₀ : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    let m : unitInterval := ⟨5 / 16, by constructor <;> norm_num⟩
    ∃ t₀ ∈ Set.Icc (0 : unitInterval) m, ∃ t₁ ∈ Set.Icc m (1 : unitInterval),
      ∀ y, actualCuspCylinderHeightLoop R y t₀ = 1 / 2 ∧
        actualCuspCylinderHeightLoop R y t₁ = 1 / 2 := by
  obtain ⟨t₀, ht₀, hv₀, t₁, ht₁, hv₁⟩ :=
    actualCuspCylinderHeightLoop_crosses_level_on_both_sides R y₀ (1 / 2)
      (by norm_num) (by norm_num)
  refine ⟨t₀, ht₀, t₁, ht₁, fun y ↦ ?_⟩
  exact ⟨(actualCuspCylinderHeightLoop_independent_fiber R y y₀ t₀).trans hv₀,
    (actualCuspCylinderHeightLoop_independent_fiber R y y₀ t₁).trans hv₁⟩

public noncomputable def actualCuspCylinderMiddleIntersectionSlice
    (R : A.AffineRadialCompletionInput)
    (t : unitInterval)
    (ht : ∀ y, actualCuspCylinderHeightLoop R y t = 1 / 2) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ContinuousMap G.Fiber
      ((Opens.toTopCat (TopCat.of (CircleMappingTorus G.clutching))).obj
        (actualCuspMappingTorusOrderThreeOpen R ⊓
          actualCuspMappingTorusOrderFourOpen R)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  refine ⟨fun y ↦ ⟨circleMappingTorusCylinderProjection G.clutching (t, y), ?_⟩, ?_⟩
  · constructor
    · apply (cuspToEllipticInteriorMap_mem_orderThreeSide_iff_height R _).2
      change actualCuspCylinderHeightLoop R y t < 2 / 3
      rw [ht]
      norm_num
    · apply (cuspToEllipticInteriorMap_mem_orderFourSide_iff_height R _).2
      change 1 / 3 < actualCuspCylinderHeightLoop R y t
      rw [ht]
      norm_num
  · exact ((circleMappingTorusCylinderProjection G.clutching).continuous.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _

/-- The index-five boundary in the natural-order adaptive mapping-torus overlap. -/
public noncomputable def actualCuspAdaptiveIndexFiveBoundary
    (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1
      ((Opens.toTopCat (TopCat.of (CircleMappingTorus G.clutching))).obj
        (actualCuspMappingTorusOrderThreeOpen R ⊓
          actualCuspMappingTorusOrderFourOpen R)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  exact (actualCuspMappingTorusPulledBackHomologyComparison R).boundaryHom 1
    (e (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)))

/-- The same adaptive boundary after radial pullback and inclusion in the elliptic band. -/
public noncomputable def actualCuspAdaptiveIndexFiveBandCarrier
    (R : A.AffineRadialCompletionInput) :
    IntegralSingularHomology 1
      (R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
        Set A.ellipticInterior) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let pullback :=
    SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyHom
      (actualCuspMappingTorusToCollarTopCatMap A)
      R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen 1
  exact R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne
    (pullback (actualCuspAdaptiveIndexFiveBoundary R))

/-- The coefficient actually used by the marked degree-two Mayer--Vietoris matrix. -/
public noncomputable def actualCuspIndexFiveBoundaryCoefficient
    (R : A.AffineRadialCompletionInput) : ℤ :=
  R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment
    (R.twoDiscCover.cuspPulledBackBoundaryHom
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)))

/-- The adaptive source read evaluates the index-five boundary as the positive primitive fibre
coordinate. -/
public theorem actualCuspAdaptiveIndexFiveBoundary_read_eq_one
    (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspFiberFourthCoordinateHom A
      (actualCuspAdaptiveNaturalSourceRead R
        (actualCuspAdaptiveIndexFiveBoundary R)) = 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  let x := A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)
  have hread := DFunLike.congr_fun
    (congrArg (fun q ↦ q.comp e.toAddMonoidHom)
      (actualCuspAdaptiveNaturalSourceRead_boundary_eq_wang R)) x
  change actualCuspAdaptiveNaturalSourceRead R
      ((actualCuspMappingTorusPulledBackHomologyComparison R).boundaryHom 1 (e x)) =
    actualCuspWangBoundaryHom A x at hread
  change actualCuspFiberFourthCoordinateHom A
      (actualCuspAdaptiveNaturalSourceRead R
        ((actualCuspMappingTorusPulledBackHomologyComparison R).boundaryHom 1 (e x))) = 1
  rw [hread]
  have hcoordinate := DFunLike.congr_fun
    (actualCuspMarkedWangComposite_eq_rawCoordinateFive A) x
  simp only [AddMonoidHom.comp_apply] at hcoordinate
  rw [hcoordinate, coordinateAfterAddEquiv_apply, AddEquiv.apply_symm_apply]
  simp

/-- Pullback naturality identifies the adaptive carrier with the literal index-five boundary
used in the elliptic two-disc presentation. -/
public theorem actualCuspAdaptiveIndexFiveBandCarrier_eq_pulledBackBoundary
    (R : A.AffineRadialCompletionInput) :
    actualCuspAdaptiveIndexFiveBandCarrier R =
      R.twoDiscCover.cuspPulledBackBoundaryHom
        (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  let x := A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)
  let boundary := (actualCuspMappingTorusPulledBackHomologyComparison R).boundaryHom 1
  let pullback :=
    SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyHom
      (actualCuspMappingTorusToCollarTopCatMap A)
      R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen 1
  have hnat := actualCuspHeightPreimageCover_boundary_naturality R 1
  have hnatApply := DFunLike.congr_fun (congrArg ConcreteCategory.hom hnat) (e x)
  have hcancel :
      SphereSixComplex.BinaryOpenCover.integralHomologyMapHom
          (actualCuspMappingTorusToCollarTopCatMap A) 2 (e x) = x := by
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  change pullback (boundary (e x)) =
    R.twoDiscCover.cuspOpenCoverConnectingHom
      (SphereSixComplex.BinaryOpenCover.integralHomologyMapHom
        (actualCuspMappingTorusToCollarTopCatMap A) 2 (e x)) at hnatApply
  rw [hcancel] at hnatApply
  change R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne
      (pullback (boundary (e x))) = R.twoDiscCover.cuspPulledBackBoundaryHom x
  rw [hnatApply, R.twoDiscCover.cuspPulledBackBoundaryHom_eq_comp]
  rfl

/-- A left inverse on the single adaptive index-five carrier is enough to prove that its band
coefficient is a unit.  This is weaker than identifying the carrier with the canonical marked
fibre map, and it is insensitive to a simultaneous reversal of the overlap orientation. -/
public theorem actualCuspIndexFiveBoundaryCoefficient_sq_eq_one_of_split_carrier
    (R : A.AffineRadialCompletionInput)
    (read : IntegralSingularHomology 1
        (R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
          Set A.ellipticInterior) →+
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1
        ((Opens.toTopCat (TopCat.of (CircleMappingTorus G.clutching))).obj
          (actualCuspMappingTorusOrderThreeOpen R ⊓
            actualCuspMappingTorusOrderFourOpen R)))
    (hsplit : read (actualCuspAdaptiveIndexFiveBandCarrier R) =
      actualCuspAdaptiveIndexFiveBoundary R) :
    actualCuspIndexFiveBoundaryCoefficient R *
        actualCuspIndexFiveBoundaryCoefficient R = 1 := by
  let E := R.homologyAlignment.actualHomologyCoordinates.degreeTwoInvariantEquiv
  let x := A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)
  let b := actualCuspIndexFiveBoundaryCoefficient R
  let g := (E.symm 1).1
  have hcoordinate : E (R.twoDiscCover.cuspPulledBackBoundaryInvariantHom x) = b := by
    change R.twoDiscCover.cuspPulledBackBoundaryCoordinateHom R.homologyAlignment x = b
    rw [R.twoDiscCover.cuspPulledBackBoundaryCoordinateHom_apply_eq_bandCoordinate]
    rfl
  have hinvariant : R.twoDiscCover.cuspPulledBackBoundaryInvariantHom x = b • E.symm 1 := by
    apply E.injective
    rw [hcoordinate, map_zsmul, E.apply_symm_apply]
    simp
  have hband : R.twoDiscCover.cuspPulledBackBoundaryHom x = b • g := by
    exact congrArg Subtype.val hinvariant
  have hfactor : actualCuspAdaptiveIndexFiveBandCarrier R = b • g := by
    rw [actualCuspAdaptiveIndexFiveBandCarrier_eq_pulledBackBoundary, hband]
  change b * b = 1
  exact SphereSixComplex.integerCoefficient_sq_eq_one_of_split
    (actualCuspAdaptiveIndexFiveBoundary R)
    (actualCuspAdaptiveIndexFiveBandCarrier R)
    ((actualCuspFiberFourthCoordinateHom A).comp
      (actualCuspAdaptiveNaturalSourceRead R)) read b g
    (actualCuspAdaptiveIndexFiveBoundary_read_eq_one R) hsplit hfactor

/-- The former exact invariant-basis datum implies the weaker orientation-free endpoint, but
the converse deliberately does not recover either the index-four value or the positive sign. -/
public theorem actualCuspIndexFiveBoundaryCoefficient_sq_eq_one_of_invariantBasisData
    (R : A.AffineRadialCompletionInput)
    (h : ((R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
        (R.twoDiscCover.cuspPulledBackBoundaryHom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 0 ∧
      (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
        (R.twoDiscCover.cuspPulledBackBoundaryHom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))) = 1)) :
    actualCuspIndexFiveBoundaryCoefficient R *
        actualCuspIndexFiveBoundaryCoefficient R = 1 := by
  rw [actualCuspIndexFiveBoundaryCoefficient, h.2]
  norm_num

end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
