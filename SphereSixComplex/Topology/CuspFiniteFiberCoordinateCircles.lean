module
public import SphereSixComplex.Topology.CuspFiniteFiberSpecializationGeometricReduction
public import SphereSixComplex.Topology.IntegerPeriodCircle
public import SphereSixComplex.Topology.CuspPeriodLoopDeckComparison
public import SphereSixComplex.Topology.CuspDeckHomologyOne

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open SphereSixComplex.Periods ComplexTorus TorusFamily GlobalTorusFamily
open CuspPuncturedCollarBridge CuspRadialClutchingConstruction CuspPeriodExpansion
open StandardCircleHomologyLiftDegree EllipticFamilySpecialization

public def cuspFiniteFiberCoordinateCircle (A : PaperAnalyticData) (j : Fin 2) :
    C(StdTorus 1, AdditiveTorus (cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness)).1) :=
  integerPeriodCircle _ (fullRankDomain (cuspBasePoint A.cuspCoordinate
    (markedCuspParameter A.starCuspWitness))) (Pi.single (Fin.castAdd 2 j) 1)

public theorem cuspFiniteFiberCoordinateCircle_generator (A : PaperAnalyticData) (j : Fin 2) :
    let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
    let _ := G.fiberTopology
    integralSingularHomologyMap 1 (A.cuspFiniteFiberCoordinateCircle j)
      standardCircleHomologyGenerator = G.degreeOneFiberGenerator j := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
  let _ := G.fiberTopology
  apply G.monodromyCoordinates.degreeOne.injective
  rw [ActualCuspRadialClutchingData.degreeOneFiberGenerator,
    G.monodromyCoordinates.degreeOne.apply_symm_apply]
  exact integerPeriodCircle_homology _ _ _

public def cuspFiniteFiberCircleToFilling (A : PaperAnalyticData) (j : Fin 2) :
    C(StdTorus 1, actualLocalCuspFilling A.starCuspWitness) := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
  let _ := G.fiberTopology
  exact G.markedFiberToCuspFilling.comp (A.cuspFiniteFiberCoordinateCircle j)

public theorem cuspFiniteFiberCircleToFilling_homology (A : PaperAnalyticData) (j : Fin 2) :
    let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
    let _ := G.fiberTopology
    integralSingularHomologyMap 1 (A.cuspFiniteFiberCircleToFilling j)
      standardCircleHomologyGenerator =
    integralSingularHomologyMap 1 G.markedFiberToCuspFilling (G.degreeOneFiberGenerator j) := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
  let _ := G.fiberTopology
  change integralSingularHomologyMap 1
    (G.markedFiberToCuspFilling.comp (A.cuspFiniteFiberCoordinateCircle j)) _ = _
  erw [← integralSingularHomologyMap_comp_wang]
  exact congrArg (integralSingularHomologyMap 1 G.markedFiberToCuspFilling)
    (A.cuspFiniteFiberCoordinateCircle_generator j)

public theorem cuspFiniteFiberCircleToFilling_real (A : PaperAnalyticData) (j : Fin 2)
    (t : ℝ) :
    let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
    A.cuspFiniteFiberCircleToFilling j (fun _ ↦ (t : UnitAddCircle)) =
      puncturedLocalCuspToFilling A.starCuspWitness
        (actualCuspCollarPeriodPoint A.starCuspWitness G.markingParameter_mem
          (t • periodVector (cuspBasePoint A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness)).1 (Pi.single (Fin.castAdd 2 j) 1))) := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
  let _ := G.fiberTopology
  apply G.markedFiberToCuspFilling_eq_actualCuspCollarPeriodPoint
  exact integerPeriodCircle_real _ _ _ t

public theorem cuspMarkedParameter_halfPlane (A : PaperAnalyticData) :
    markedCuspParameter A.starCuspWitness ∈ cuspHalfPlane A.cuspCoordinate.height :=
  mem_cuspHalfPlane_of_norm_cuspQ_lt A.starCuspWitness.localWitness.radius_le
    (markedCuspParameter_mem A.starCuspWitness)

public theorem cuspFiniteFiberCircleToFilling_loop (A : PaperAnalyticData) (j : Fin 2) :
    let s := markedCuspParameter A.starCuspWitness
    let hs := A.cuspMarkedParameter_halfPlane
    let hsr : cuspQ s ∈ Metric.ball (0 : ℂ) A.starCuspWitness.localWitness.radius := by
      simpa only [Metric.mem_ball, dist_zero_right] using markedCuspParameter_mem A.starCuspWitness
    integralSingularHomologyMap 1 (A.cuspFiniteFiberCircleToFilling j)
      standardCircleHomologyGenerator =
      loopHomologyClass (localCuspPeriodLoop A.starCuspWitness s hs hsr (Pi.single j 1)) := by
  dsimp only
  rw [standardCircleHomologyGenerator,
    integralSingularHomologyMap_loopHomologyClass]
  let p := standardCirclePositiveLoop.map (A.cuspFiniteFiberCircleToFilling j).continuous
  let q := localCuspPeriodLoop A.starCuspWitness _ A.cuspMarkedParameter_halfPlane
    (by simpa only [Metric.mem_ball, dist_zero_right] using markedCuspParameter_mem A.starCuspWitness)
    (Pi.single j 1)
  have h : ∀ t, p t = q t := by
    intro t
    have ht : standardCirclePositiveLoop t = fun _ ↦ ((t : ℝ) : UnitAddCircle) := by
      ext i
      change ((((t : ℝ) * (1 : ℤ) : ℝ)) : UnitAddCircle) = ((t : ℝ) : UnitAddCircle)
      simp
    change A.cuspFiniteFiberCircleToFilling j (standardCirclePositiveLoop t) = _
    rw [ht, A.cuspFiniteFiberCircleToFilling_real]
    have hn : firstPeriodCoefficients (Pi.single j 1) = Pi.single (Fin.castAdd 2 j) 1 := by
      ext i
      fin_cases j <;> fin_cases i <;> rfl
    change _ = puncturedLocalCuspToFilling A.starCuspWitness
      (actualCuspCollarPeriodPoint A.starCuspWitness _
        ((t : ℝ) • periodVector _ (firstPeriodCoefficients (Pi.single j 1))))
    rw [hn]
    rfl
  have hxy := p.source.symm.trans ((h 0).trans q.source)
  erw [← loopHomologyClass_cast q hxy]
  congr 1
  ext t
  exact h t

public theorem cuspFiniteFiberGenerator_deckCoordinates (A : PaperAnalyticData) (j : Fin 2) :
    let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
    let _ := G.fiberTopology
    actualCuspDeckHomologyOneEquiv A.starCuspWitness
      (integralSingularHomologyMap 1 G.markedFiberToCuspFilling
        (G.degreeOneFiberGenerator j)) = Pi.single j 1 := by
  dsimp only
  rw [← A.cuspFiniteFiberCircleToFilling_homology j,
    A.cuspFiniteFiberCircleToFilling_loop j]
  let W := A.starCuspWitness
  let _ := actualLocalCuspQuotientAction W
  let _ : SimplyConnectedSpace (CuspLocalPhaseAction.LocalCarrier A.toricModel W.localWitness.radius) :=
    A.toricModel.localCarrierSimplyConnected W.localWitness.radius W.localWitness.radius_pos
  let hp := actualCuspFillingProjection_isQuotientCoveringMap W
  let _ : PathConnectedSpace (actualLocalCuspFilling W) :=
    hp.surjective.pathConnectedSpace hp.continuous
  let e : CuspLocalPhaseAction.LocalCarrier A.toricModel W.localWitness.radius := Classical.arbitrary _
  have h := localCuspPeriodLoop_homology W _ A.cuspMarkedParameter_halfPlane
    (by simpa only [Metric.mem_ball, dist_zero_right] using markedCuspParameter_mem W)
    e (Pi.single j 1)
  rw [actualCuspDeckHomologyOneEquiv_eq W e]
  erw [← h]
  exact (abelianCoverHomologyEquiv hp e).symm_apply_apply _

end SphereSixComplex.Geometry.PaperAnalyticData
