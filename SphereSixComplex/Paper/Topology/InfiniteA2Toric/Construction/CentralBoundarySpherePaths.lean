module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralAttachment
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryModel
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveBoundaryPaths
public import SphereSixComplex.Prerequisites.Topology.OnePointComplexHomology
import all SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryCharts
import all SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryModel

@[expose] public section
noncomputable section
open Set Topology Matrix
open scoped OnePoint
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex SphereSixComplex.Periods
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspPhaseEstimates
open CuspStraighteningRetraction CuspToricPhaseAction
variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

theorem actualDeck_effectivePhase_formula
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : constructedPositiveCentralFiber W.localWitness.radius)
    (lambda : ParameterLattice) (k : Fin 2 → Circle) :
    letI := actualLocalCuspQuotientAction W
    (((Multiplicative.ofAdd lambda • effectivePhaseCentralPoint W k q).1 :
      localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
      constructedModel.torusAction
        (compactTorusEmbedding (frozenCompactPhase N lambda * effectivePhaseSection k))
        (normalizedPositiveDeckCarrierMap N constructedModel lambda
          (q.1.1.1 : constructedModel.Carrier)) := by
  let _ := actualLocalCuspQuotientAction W
  let C := NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
    N W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let p := effectivePhaseCentralPoint W k q
  have hactual : C.psiMap lambda p.1 =
      frozenLocalPsiMap N constructedModel W.localWitness.radius lambda p.1 := by
    apply Subtype.ext
    rw [C.psiMap_coe, frozenLocalPsiMap_coe, p.property]
    rfl
  change (((C.toCuspActionData (M := constructedModel)).psiMap lambda p.1).1 :
    constructedModel.Carrier) = _
  rw [← C.psiMap_eq_generic, hactual]
  exact frozenDeck_effectivePhase_formula W.localWitness.radius lambda k
    (positiveCentralPoint W q).1

theorem actualPhaseOrbit_deck_axis
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : constructedPositiveCentralFiber W.localWitness.radius)
    (lambda : ParameterLattice) (k : Fin 2 → Circle)
    (a : ChartIndex) (j : Fin 3) (z : ℂ)
    (ha : normalizedPositiveDeckCarrierMap N constructedModel lambda
      (q.1.1.1 : constructedModel.Carrier) = inclusion a (singleAxis j z)) :
    ∃ p : actualLocalCuspCentralSubMulAction W, ∃ w : ℂ,
      Quotient.mk _ p = effectivePhaseCentralOrbit W k q ∧
      (p.1.1 : Carrier) = inclusion a (singleAxis j w) := by
  let _ := actualLocalCuspQuotientAction W
  let p : actualLocalCuspCentralSubMulAction W :=
    Multiplicative.ofAdd lambda • effectivePhaseCentralPoint W k q
  refine ⟨p, torusChartCoordinates a
    (compactTorusEmbedding (frozenCompactPhase N lambda * effectivePhaseSection k)) j * z, ?_, ?_⟩
  · apply Quotient.sound
    change MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) p (effectivePhaseCentralPoint W k q)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨Multiplicative.ofAdd lambda, rfl⟩
  · change ((Multiplicative.ofAdd lambda • effectivePhaseCentralPoint W k q).1.1 : Carrier) = _
    rw [actualDeck_effectivePhase_formula, ha]
    change carrierTorusActionFun _ (inclusion a (singleAxis j z)) = _
    rw [carrierTorusActionFun_inclusion]
    congr 1
    funext l
    by_cases h : l = j <;> simp [singleAxis, h]

theorem upperOrbit_mem_sphere
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (z : ℂ) :
    CentralBoundary.upperOrbit W i z ∈ Set.range (CentralBoundary.sphereMap W i) := by
  by_cases hz : z = 0
  · subst z
    exact ⟨(∞ : OnePoint ℂ), by
      rw [CentralBoundary.sphereMap_infty, CentralBoundary.upperOrbit_zero]⟩
  · exact ⟨(z⁻¹ : ℂ), (CentralBoundary.upperOrbit_eq_lower_inv W i z hz).symm⟩

theorem phaseOrbit_lower_axis_mem_sphere
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : constructedPositiveCentralFiber W.localWitness.radius)
    (lambda : ParameterLattice) (k : Fin 2 → Circle) (j : Fin 3) (z : ℂ)
    (ha : normalizedPositiveDeckCarrierMap N constructedModel lambda
      (q.1.1.1 : constructedModel.Carrier) = inclusion (false, 0) (singleAxis j z)) :
    effectivePhaseCentralOrbit W k q ∈ Set.range (CentralBoundary.sphereMap W j) := by
  obtain ⟨p,w,hp,hw⟩ := actualPhaseOrbit_deck_axis W q lambda k _ j z ha
  refine ⟨(w : ℂ), ?_⟩
  rw [← hp]
  change Quotient.mk _ (CentralBoundary.axisPoint W false j w) = Quotient.mk _ p
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply Subtype.ext
  exact hw.symm

theorem phaseOrbit_upper_axis_mem_sphere
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : constructedPositiveCentralFiber W.localWitness.radius)
    (lambda : ParameterLattice) (k : Fin 2 → Circle) (j : Fin 3) (z : ℂ)
    (ha : normalizedPositiveDeckCarrierMap N constructedModel lambda
      (q.1.1.1 : constructedModel.Carrier) =
        inclusion (CentralBoundary.upperChart j) (singleAxis (CentralBoundary.upperAxis j) z)) :
    effectivePhaseCentralOrbit W k q ∈ Set.range (CentralBoundary.sphereMap W j) := by
  obtain ⟨p,w,hp,hw⟩ := actualPhaseOrbit_deck_axis W q lambda k _ _ z ha
  have he : CentralBoundary.upperOrbit W j w = effectivePhaseCentralOrbit W k q := by
    rw [← hp]
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    apply Subtype.ext
    exact hw.symm
  rw [← he]
  exact upperOrbit_mem_sphere W j w
theorem square_zero_one_mem_sphere
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 6) (p : CellSquare) (hp : p.1 1 = 0) (k : Fin 2 → Circle) :
    effectivePhaseCentralOrbit W k (cellSquareProjection W.localWitness.radius_pos 0 ⟨i,p⟩).1 ∈
      Set.range (CentralBoundary.sphereMap W (![1,0,2,1,0,2] i)) := by
  obtain ⟨z,hz⟩ := positiveDeck_square_zero_one (N := N) i p hp
  fin_cases i
  all_goals first
    | exact phaseOrbit_lower_axis_mem_sphere W _ _ k _ z hz
    | exact phaseOrbit_upper_axis_mem_sphere W _ _ k _ z hz

theorem square_zero_zero_mem_sphere
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 6) (p : CellSquare) (hp : p.1 0 = 0) (k : Fin 2 → Circle) :
    effectivePhaseCentralOrbit W k (cellSquareProjection W.localWitness.radius_pos 0 ⟨i,p⟩).1 ∈
      Set.range (CentralBoundary.sphereMap W (![2,1,0,2,1,0] i)) := by
  obtain ⟨z,hz⟩ := positiveDeck_square_zero_zero (N := N) i p hp
  fin_cases i
  all_goals first
    | exact phaseOrbit_lower_axis_mem_sphere W _ _ k _ z hz
    | exact phaseOrbit_upper_axis_mem_sphere W _ _ k _ z hz

theorem actualHexagonSide_mem_sphere
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) (t : unitInterval) :
    actualHexagonSidePath W i t ∈
      Set.range (CentralBoundary.sphereMap W (![1,0,2,1,0,2] i)) := by
  change correctedPlaneCellOrbit W (hexagonSide i t) ∈ _
  unfold hexagonSide
  split_ifs
  · rw [correctedPlaneCellOrbit_square]
    exact square_zero_one_mem_sphere W i _ rfl _
  · rw [correctedPlaneCellOrbit_square]
    have hi : (![2,1,0,2,1,0] : Fin 6 → Fin 3) (cellNextIndex i) =
        (![1,0,2,1,0,2] : Fin 6 → Fin 3) i := by fin_cases i <;> rfl
    rw [← hi]
    exact square_zero_zero_mem_sphere W _ _ rfl _


noncomputable def sphereToBoundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    C(OnePoint ℂ, centralBoundary W) :=
  ⟨fun z ↦ ⟨CentralBoundary.sphereMap W i z,
    CentralBoundary.sphereMap_not_mem_singletonPhaseImage W i z⟩,
    (CentralBoundary.sphereMap W i).continuous.subtype_mk _⟩

theorem sphereToBoundary_embedding
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    IsEmbedding (sphereToBoundary W i) := by
  apply (Continuous.isClosedEmbedding (sphereToBoundary W i).continuous ?_).isEmbedding
  intro z w h
  have he := (CentralBoundary.sphereMap_eq_iff W (i,z) (i,w)).mp (congrArg Subtype.val h)
  rcases he with he | he | he
  · exact congrArg Prod.snd he
  · exact he.1.trans he.2.symm
  · exact he.1.trans he.2.symm

def boundaryOrigin
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (upper : Bool) :
    centralBoundary W := ⟨constructedCentralOriginOrbit W upper, by
  change constructedCentralOriginOrbit W upper ∉ singletonPhaseImage W
  cases upper
  · simpa only [CentralBoundary.sphereMap_coe, CentralBoundary.axisOrbit_zero] using
      CentralBoundary.sphereMap_not_mem_singletonPhaseImage W 0 (0 : ℂ)
  · simpa only [CentralBoundary.sphereMap_infty] using
      CentralBoundary.sphereMap_not_mem_singletonPhaseImage W 0 OnePoint.infty⟩

theorem actualSide_mem_boundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) (t : unitInterval) :
    actualHexagonSidePath W i t ∈ centralBoundary W := by
  obtain ⟨z,hz⟩ := actualHexagonSide_mem_sphere W i t
  exact hz ▸ CentralBoundary.sphereMap_not_mem_singletonPhaseImage W _ z

def boundarySide
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) :
    Path (boundaryOrigin W (cellChart 0 i).1)
      (boundaryOrigin W (cellChart 0 (cellNextIndex i)).1) where
  toFun t := ⟨actualHexagonSidePath W i t, actualSide_mem_boundary W i t⟩
  continuous_toFun := (actualHexagonSidePath W i).continuous.subtype_mk _
  source' := Subtype.ext (actualHexagonSidePath W i).source
  target' := Subtype.ext (actualHexagonSidePath W i).target

theorem boundarySide_mem_sphere
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) (t : unitInterval) :
    boundarySide W i t ∈ range (sphereToBoundary W (![1,0,2,1,0,2] i)) := by
  obtain ⟨z,hz⟩ := actualHexagonSide_mem_sphere W i t
  exact ⟨z, Subtype.ext hz⟩

open StandardCircleHomologyLiftDegree

theorem boundaryLoop_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    loopHomologyClass (((((boundarySide W 0).trans (boundarySide W 1)).trans
      (boundarySide W 2)).trans (boundarySide W 3)).trans
      (boundarySide W 4) |>.trans (boundarySide W 5)) = 0 := by
  let := onePointComplex_homologyOne_subsingleton
  apply alternatingHexagonBoundaryPath_homology_zero_of_pairLoops
  · exact pairLoop_eq_zero_of_range
      (sphereToBoundary W 1) (sphereToBoundary_embedding W 1)
      (boundarySide W 0) (boundarySide W 3)
      (boundarySide_mem_sphere W 0)
      (boundarySide_mem_sphere W 3)
  · exact pairLoop_eq_zero_of_range
      (sphereToBoundary W 0) (sphereToBoundary_embedding W 0)
      (boundarySide W 1) (boundarySide W 4)
      (boundarySide_mem_sphere W 1)
      (boundarySide_mem_sphere W 4)
  · exact pairLoop_eq_zero_of_range
      (sphereToBoundary W 2) (sphereToBoundary_embedding W 2)
      (boundarySide W 2) (boundarySide W 5)
      (boundarySide_mem_sphere W 2)
      (boundarySide_mem_sphere W 5)

def boundaryLoop
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Path (boundaryOrigin W false) (boundaryOrigin W false) :=
  (((((boundarySide W 0).trans (boundarySide W 1)).trans
    (boundarySide W 2)).trans (boundarySide W 3)).trans
    (boundarySide W 4)).trans (boundarySide W 5)

theorem boundaryCorrectedBallOrbit_boundary_mem_centralBoundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) (hx : x.1 ∈ Metric.sphere 0 1) :
    boundaryCorrectedBallOrbit W x ∈ centralBoundary W := by
  let z : correctedPlaneCell 0 :=
    ⟨correctedHexagonHomeomorph 0 x.1,
      (correctedHexagonHomeomorph_mem_closed_iff 0 x.1).mpr x.property⟩
  obtain ⟨⟨i, p⟩, hproj⟩ := surjective_correctedPlaneSquareProjection 0 z
  have htile : correctedPlaneTile 0 i p =
      correctedHexagonHomeomorph 0 x.1 := congrArg Subtype.val hproj
  have hcell : closedBallPositiveCellHomeomorph W x =
      cellSquareProjection W.localWitness.radius_pos 0 ⟨i, p⟩ := by
    change correctedFiniteQuotientCellHomeomorph W.localWitness.radius_pos 0 z = _
    rw [← hproj, correctedFiniteQuotientCellHomeomorph_apply]
  have hp : p.1 0 = 0 ∨ p.1 1 = 0 := by
    by_contra hp
    push Not at hp
    have hopen := correctedPlaneTile_mem_open_of_nonzero 0 i p (by
      intro j
      fin_cases j
      · exact hp.1
      · exact hp.2)
    rw [htile] at hopen
    have hball := (correctedHexagonHomeomorph_mem_open_iff 0 x.1).mp hopen
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hx hball
  unfold boundaryCorrectedBallOrbit
  rw [← htile, hcell]
  rcases hp with hp | hp
  · obtain ⟨z,hz⟩ := square_zero_zero_mem_sphere W i p hp
      (actualBoundaryGauge (N := N) (correctedPlaneTile 0 i p))
    exact hz ▸ CentralBoundary.sphereMap_not_mem_singletonPhaseImage W _ z
  · obtain ⟨z,hz⟩ := square_zero_one_mem_sphere W i p hp
      (actualBoundaryGauge (N := N) (correctedPlaneTile 0 i p))
    exact hz ▸ CentralBoundary.sphereMap_not_mem_singletonPhaseImage W _ z


end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
