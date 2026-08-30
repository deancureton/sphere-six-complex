module

public import SphereSixComplex.Topology.ToricPhaseSpreading
public import SphereSixComplex.Topology.EstablishedA2PhaseSpreading
public import SphereSixComplex.Topology.ActualCuspStraighteningRetraction
public import SphereSixComplex.Geometry.PaperOpenEmbeddingStar

/-!
# Toric phase spreading for the straightened cusp

The compatibility structure below isolates the remaining standard toric-cellular content: the
phase-orbit quotient topology, compatibility with the frozen deck action, and preservation of
torus stabilizers by the positive-part homotopy.  From exactly these inputs, phase spreading and
transport back through Lemma 7.5 are formal consequences.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.CuspStraighteningRetraction

open SphereSixComplex
open SphereSixComplex.Periods
open CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspPuncturedCollarBridge
open CuspStraighteningExtension
open CuspStraighteningHomeomorph
open StandardInfiniteA2ToricModel

namespace FrozenLocalCuspPhaseSpreadingData

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
  {P : PolarHoneycombData M r} (F : FrozenLocalCuspPhaseSpreadingData N M r P)

/-- Phase spreading supplies the frozen-action equivariant deformation retraction. -/
public noncomputable def frozenEquivariantStrongDeformationRetraction :
    letI := frozenLocalCuspAction N M r
    EquivariantStrongDeformationRetraction
      (Multiplicative ParameterLattice) (LocalCarrier M r) {p | M.t p = 0} := by
  letI := P.positiveDeckAction
  let R := F.positiveRetraction
  letI := frozenLocalCuspAction N M r
  let orbit : C(CompactTorus × P.positivePart, LocalCarrier M r) :=
    ⟨compactPhaseOrbit M r P.positivePart, continuous_compactPhaseOrbit M r P.positivePart⟩
  have htarget (k : CompactTorus) (p : P.positivePart) :
      compactPhaseOrbit M r P.positivePart (k, p) ∈
          {x : LocalCarrier M r | M.t x = 0} ↔ p ∈ P.central := by
    change M.t (compactPhaseOrbit M r P.positivePart (k, p)) = 0 ↔ p ∈ P.central
    rw [P.central_eq]
    change M.t (compactPhaseOrbit M r P.positivePart (k, p)) = 0 ↔
      M.t (p : LocalCarrier M r) = 0
    change M.t (M.torusAction (compactTorusEmbedding k) (p : M.Carrier)) = 0 ↔ _
    rw [M.t_torusAction, mul_eq_zero]
    exact or_iff_right (Units.ne_zero (compactTorusEmbedding k 2))
  let S : ToricPhaseSpreadingData (K := CompactTorus) (X := LocalCarrier M r) R
      {p : LocalCarrier M r | M.t p = 0} := {
    orbit := orbit
    orbit_prod_isQuotientMap := F.phaseOrbit_prod_isQuotientMap
    deckPhase := F.deckPhase
    deck_orbit := F.deck_orbit
    homotopy_fiberwise := F.homotopy_fiberwise
    target_iff := fun k p ↦ htarget k p
  }
  exact S.equivariantStrongDeformationRetraction R

end FrozenLocalCuspPhaseSpreadingData

/-- Transport the phase-spread frozen retraction through the point-level straightening
homeomorphism. -/
public noncomputable def actualLocalCuspCentralFiberRetractionData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (P : PolarHoneycombData M W.localWitness.radius)
    (F : FrozenLocalCuspPhaseSpreadingData N M W.localWitness.radius P) :
    ActualLocalCuspCentralFiberRetractionData W := by
  letI := P.positiveDeckAction
  letI := frozenLocalCuspAction N M W.localWitness.radius
  let Rf := F.frozenEquivariantStrongDeformationRetraction
  let rfRetract : C(LocalCarrier M W.localWitness.radius,
      LocalCarrier M W.localWitness.radius) := Rf.retract
  let rfHomotopy : ContinuousMap.Homotopy (ContinuousMap.id _) rfRetract := Rf.homotopy
  have hRf_mem (x : LocalCarrier M W.localWitness.radius) :
      M.t (rfRetract x) = 0 := Rf.retract_mem x
  have hRf_fixed (x : LocalCarrier M W.localWitness.radius) (hx : M.t x = 0) :
      rfRetract x = x := Rf.retract_fixed x hx
  have hRf_homotopy_fixed (s : unitInterval)
      (x : LocalCarrier M W.localWitness.radius) (hx : M.t x = 0) :
      rfHomotopy (s, x) = x := Rf.homotopy_fixed s x hx
  have hRf_retract (g : Multiplicative ParameterLattice)
      (x : LocalCarrier M W.localWitness.radius) :
      rfRetract (frozenLocalPsiMap N M W.localWitness.radius
        (Multiplicative.toAdd g) x) =
      frozenLocalPsiMap N M W.localWitness.radius
        (Multiplicative.toAdd g) (rfRetract x) :=
    Rf.retract_equivariant g x
  have hRf_homotopy (g : Multiplicative ParameterLattice) (s : unitInterval)
      (x : LocalCarrier M W.localWitness.radius) :
      rfHomotopy (s, frozenLocalPsiMap N M W.localWitness.radius
        (Multiplicative.toAdd g) x) =
      frozenLocalPsiMap N M W.localWitness.radius
        (Multiplicative.toAdd g) (rfHomotopy (s, x)) :=
    Rf.homotopy_equivariant g s x
  let J := StandardInfiniteA2ToricModel.Established.establishedContinuousTorusAction M
  let H := pointStraighteningHomeomorph J W
  let retract : C(LocalCarrier M W.localWitness.radius,
      LocalCarrier M W.localWitness.radius) := {
    toFun := fun x ↦ H.symm (rfRetract (H x))
    continuous_toFun := H.symm.continuous.comp
      (rfRetract.continuous.comp H.continuous)
  }
  let homotopy : ContinuousMap.Homotopy (ContinuousMap.id _ ) retract := {
    toFun z := H.symm (rfHomotopy (z.1, H z.2))
    continuous_toFun := H.symm.continuous.comp
      (rfHomotopy.continuous.comp
        (continuous_fst.prodMk (H.continuous.comp continuous_snd)))
    map_zero_left x := by
      change H.symm (rfHomotopy (0, H x)) = x
      exact (congrArg H.symm (rfHomotopy.map_zero_left (H x))).trans
        (H.symm_apply_apply x)
    map_one_left _ := rfl
  }
  letI := actualLocalCuspQuotientAction W
  refine ⟨{
    retract := retract
    homotopy := homotopy
    retract_mem := ?_
    retract_fixed := ?_
    homotopy_fixed := ?_
    retract_equivariant := ?_
    homotopy_equivariant := ?_
  }⟩
  · intro x
    change M.t (pointUnstraightening W (rfRetract (pointStraightening W x))) = 0
    have hcentral : M.t (rfRetract (pointStraightening W x)) = 0 := hRf_mem _
    rw [pointUnstraightening_of_t_eq_zero W _ hcentral]
    exact hcentral
  · intro x hx
    change pointUnstraightening W (rfRetract (pointStraightening W x)) = x
    have hstraight : pointStraightening W x = x :=
      pointStraightening_of_t_eq_zero W x hx
    rw [hstraight, hRf_fixed x hx, pointUnstraightening_of_t_eq_zero W x hx]
  · intro s x hx
    change pointUnstraightening W (rfHomotopy (s, pointStraightening W x)) = x
    have hstraight : pointStraightening W x = x :=
      pointStraightening_of_t_eq_zero W x hx
    rw [hstraight, hRf_homotopy_fixed s x hx,
      pointUnstraightening_of_t_eq_zero W x hx]
  · intro g x
    let C := CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
    change pointUnstraightening W
        (rfRetract (pointStraightening W
          ((C.toCuspActionData W.localWitness.fixedPoint).psiMap
            (Multiplicative.toAdd g) x))) =
      (C.toCuspActionData W.localWitness.fixedPoint).psiMap
        (Multiplicative.toAdd g)
          (pointUnstraightening W (rfRetract (pointStraightening W x)))
    rw [pointStraightening_genericPsiMap W, hRf_retract]
    rw [← C.psiMap_eq_generic W.localWitness.fixedPoint]
    exact (actualPsiMap_pointUnstraightening W _ _).symm
  · intro g s x
    let C := CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
    change pointUnstraightening W
        (rfHomotopy (s, pointStraightening W
          ((C.toCuspActionData W.localWitness.fixedPoint).psiMap
            (Multiplicative.toAdd g) x))) =
      (C.toCuspActionData W.localWitness.fixedPoint).psiMap
        (Multiplicative.toAdd g)
          (pointUnstraightening W (rfHomotopy (s, pointStraightening W x)))
    rw [pointStraightening_genericPsiMap W, hRf_homotopy]
    rw [← C.psiMap_eq_generic W.localWitness.fixedPoint]
    exact (actualPsiMap_pointUnstraightening W _ _).symm

/-- The established positive-part package selected at the radius of a cusp witness. -/
public noncomputable def selectedPolarHoneycombData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    PolarHoneycombData M W.localWitness.radius :=
  Classical.choice (StandardInfiniteA2ToricModel.Established.polarHoneycombData
    M W.localWitness.radius W.localWitness.radius_pos)

/-- Once the explicit orbit-stratum compatibility is supplied, the selected paper cusp has the
required central-fibre retraction datum. -/
public noncomputable def paperCuspCentralFiberRetractionData
    (A : PaperAnalyticData)
    (F : FrozenLocalCuspPhaseSpreadingData A.cuspCoordinate A.toricModel
      A.starCuspWitness.localWitness.radius
      (selectedPolarHoneycombData A.starCuspWitness)) :
    ActualLocalCuspCentralFiberRetractionData A.starCuspWitness :=
  actualLocalCuspCentralFiberRetractionData A.starCuspWitness
    (selectedPolarHoneycombData A.starCuspWitness) F

end SphereSixComplex.Geometry.CuspStraighteningRetraction
