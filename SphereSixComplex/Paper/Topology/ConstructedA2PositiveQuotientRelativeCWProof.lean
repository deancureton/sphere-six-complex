module

public import SphereSixComplex.Paper.Topology.ConstructedA2PolarHoneycombCoordinateProof
public import SphereSixComplex.Prerequisites.Topology.ManifoldWithCornersCWComplex
public import Mathlib.Topology.CWComplex.Classical.Finite
import SphereSixComplex.Prerequisites.Geometry.Quotient
import SphereSixComplex.Prerequisites.Geometry.QuotientTopology

/-!
# Relative CW attachments for the constructed positive quotient

The free and properly discontinuous positive deck action makes the orbit projection a covering
and its quotient Hausdorff, but these facts alone do not construct a relative CW structure.  This
file gives two exact routes: relative-cell attachments, and a `C¹` manifold-with-corners structure
whose boundary is the central orbit core.  The latter route invokes the classical compatible
triangulation theorem.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

/-- The orbit quotient of the constructed positive part at the quantitative cusp radius. -/
public abbrev ConstructedA2PositiveQuotient
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :=
  letI := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  PolarHoneycombData.OrbitQuotient
    (constructedLocalPositivePart W.localWitness.radius)

/-- The image of the zero-height honeycomb in the constructed positive quotient. -/
public abbrev constructedA2PositiveQuotientCore
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set (ConstructedA2PositiveQuotient W) :=
  letI := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  PolarHoneycombData.orbitCore
    {q : constructedLocalPositivePart W.localWitness.radius |
      constructedModel.t
        (q : localCarrier constructedModel W.localWitness.radius) = 0}

/-- The zero-height fibre is closed in the constructed positive part. -/
public theorem constructedPositiveCentralFiber_isClosed (r : ℝ) :
    IsClosed {q : constructedLocalPositivePart r |
      constructedModel.t (q : localCarrier constructedModel r) = 0} := by
  exact isClosed_singleton.preimage
    (constructedModel.t_holomorphic.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val))

/-- The zero-height fibre is saturated under the normalized positive deck action. -/
public theorem constructedPositiveDeck_central_preimage
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart W.localWitness.radius)
      (constructedPositiveDeck_mem N W.localWitness.radius)
    PolarHoneycombData.orbitProjection
        (constructedLocalPositivePart W.localWitness.radius) ⁻¹'
      PolarHoneycombData.orbitCore
        {q : constructedLocalPositivePart W.localWitness.radius |
          constructedModel.t
            (q : localCarrier constructedModel W.localWitness.radius) = 0} =
      {q : constructedLocalPositivePart W.localWitness.radius |
        constructedModel.t
          (q : localCarrier constructedModel W.localWitness.radius) = 0} := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  let central := {q : constructedLocalPositivePart W.localWitness.radius |
    constructedModel.t (q : localCarrier constructedModel W.localWitness.radius) = 0}
  have hmem (lambda : ParameterLattice)
      (q : constructedLocalPositivePart W.localWitness.radius) :
      (Multiplicative.ofAdd lambda) • q ∈ central ↔ q ∈ central := by
    change constructedModel.t
        (((Multiplicative.ofAdd lambda) • q :
          constructedLocalPositivePart W.localWitness.radius) :
          localCarrier constructedModel W.localWitness.radius) = 0 ↔
      constructedModel.t
        (q : localCarrier constructedModel W.localWitness.radius) = 0
    change constructedModel.t
        (normalizedPositiveDeckLocalMap N constructedModel W.localWitness.radius lambda
          (q : localCarrier constructedModel W.localWitness.radius)) = 0 ↔ _
    simp only [normalizedPositiveDeckLocalMap, normalizedPositiveDeckCarrierMap,
      constructedModel.t_torusAction, normalizedCuspPositiveTwist_last, Units.val_one, one_mul,
      constructedModel.fanShear_preserves_t]
  change PolarHoneycombData.orbitProjection
        (constructedLocalPositivePart W.localWitness.radius) ⁻¹'
      PolarHoneycombData.orbitCore central = central
  ext q
  constructor
  · rintro ⟨c, hc, hqc⟩
    change Quotient.mk _ c = Quotient.mk _ q at hqc
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hqc
    obtain ⟨g, hg⟩ := hqc
    rw [← hg] at hc
    simpa using (hmem (Multiplicative.toAdd g) q).mp hc
  · intro hq
    exact ⟨q, hq, rfl⟩

/-- The central orbit core is closed in the positive quotient. -/
public theorem constructedPositiveDeck_orbitCore_isClosed
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsClosed (constructedA2PositiveQuotientCore W) := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  rw [← (isQuotientMap_quotient_mk'
      (s := MulAction.orbitRel (Multiplicative ParameterLattice)
        (constructedLocalPositivePart W.localWitness.radius))).isClosed_preimage]
  change IsClosed (PolarHoneycombData.orbitProjection
      (constructedLocalPositivePart W.localWitness.radius) ⁻¹'
    PolarHoneycombData.orbitCore
      {q : constructedLocalPositivePart W.localWitness.radius |
        constructedModel.t
          (q : localCarrier constructedModel W.localWitness.radius) = 0})
  rw [constructedPositiveDeck_central_preimage W]
  exact constructedPositiveCentralFiber_isClosed W.localWitness.radius

/-- The exact differential-topological structure needed to invoke relative triangulation on the
positive quotient.  Its three fields are intrinsic to the explicit positive toric atlas: the
quadrant manifold structure, identification of its boundary with the zero-height fibre, and
smoothness of the normalized deck transformations. -/
public structure ConstructedA2PositiveCOneManifoldBoundaryData
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) where
  charts : ChartedSpace (EuclideanQuadrant 3)
    (constructedLocalPositivePart W.localWitness.radius)
  isManifold :
    let _ := charts
    IsManifold (modelWithCornersEuclideanQuadrant 3) 1
      (constructedLocalPositivePart W.localWitness.radius)
  boundary_eq :
    let _ := charts
    (modelWithCornersEuclideanQuadrant 3).boundary
        (constructedLocalPositivePart W.localWitness.radius) =
      {q : constructedLocalPositivePart W.localWitness.radius |
        constructedModel.t
          (q : localCarrier constructedModel W.localWitness.radius) = 0}
  deck_contMDiff :
    let _ := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart W.localWitness.radius)
      (constructedPositiveDeck_mem N W.localWitness.radius)
    let _ := charts
    ∀ g : Multiplicative ParameterLattice,
      ContMDiff (modelWithCornersEuclideanQuadrant 3)
        (modelWithCornersEuclideanQuadrant 3) 1
        (fun q : constructedLocalPositivePart W.localWitness.radius ↦ g • q)

/-- A compatible `C¹` quadrant atlas on the positive carrier descends to the orbit quotient.
Relative triangulation and preservation of manifold boundary by the quotient local
diffeomorphism then give the required relative CW structure. -/
public theorem constructedA2PositiveQuotientRelativeCW_of_cOneManifoldBoundary
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    {W : ActualPuncturedCuspCollarWitness N constructedModel}
    (A : ConstructedA2PositiveCOneManifoldBoundaryData W) :
    Nonempty (ConstructedA2PositiveQuotientRelativeCW W) := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (constructedLocalPositivePart W.localWitness.radius) :=
    constructedPositiveDeck_continuous N W.localWitness.radius
  let _ : T2Space (constructedLocalPositivePart W.localWitness.radius) :=
    constructedLocalPositivePart_t2Space W.localWitness.radius
  let _ : LocallyCompactSpace (constructedLocalPositivePart W.localWitness.radius) :=
    constructedLocalPositivePart_locallyCompactSpace W.localWitness.radius
  let _ : IsCancelSMul (Multiplicative ParameterLattice)
      (constructedLocalPositivePart W.localWitness.radius) :=
    constructedPositiveDeck_isCancelSMul W
  let _ : ProperlyDiscontinuousSMul (Multiplicative ParameterLattice)
      (constructedLocalPositivePart W.localWitness.radius) :=
    constructedPositiveDeck_properlyDiscontinuous W
  let _ : ChartedSpace (EuclideanQuadrant 3)
      (constructedLocalPositivePart W.localWitness.radius) := A.charts
  let _ : IsManifold (modelWithCornersEuclideanQuadrant 3) 1
      (constructedLocalPositivePart W.localWitness.radius) := A.isManifold
  have hquotientManifold : IsManifold (modelWithCornersEuclideanQuadrant 3) 1
      (ConstructedA2PositiveQuotient W) :=
    SphereSixComplex.Geometry.isManifold_orbitQuotient_of_contMDiff_smul
      (modelWithCornersEuclideanQuadrant 3) 1 A.deck_contMDiff
  let _ : IsManifold (modelWithCornersEuclideanQuadrant 3) 1
      (ConstructedA2PositiveQuotient W) := hquotientManifold
  let _ : T2Space (ConstructedA2PositiveQuotient W) :=
    constructedPositiveDeck_quotient_t2 W
  let _ : SecondCountableTopology (ConstructedA2PositiveQuotient W) :=
    SphereSixComplex.Geometry.orbitQuotient_secondCountableTopology
  have hboundaryPreimage :=
    (SphereSixComplex.Geometry.quotientProjection_isLocalDiffeomorph
      (modelWithCornersEuclideanQuadrant 3) 1 A.deck_contMDiff).preimage_boundary
        one_ne_zero
  have hboundary :
      (modelWithCornersEuclideanQuadrant 3).boundary
          (ConstructedA2PositiveQuotient W) =
        constructedA2PositiveQuotientCore W := by
    apply SphereSixComplex.Geometry.quotientProjection_surjective.preimage_injective
    rw [hboundaryPreimage, A.boundary_eq]
    exact (constructedPositiveDeck_central_preimage W).symm
  let hCW := ManifoldWithCorners.relativeCWComplex
    3 (ConstructedA2PositiveQuotient W)
  exact ⟨by simpa only [hboundary] using hCW⟩


end SphereSixComplex.Geometry.InfiniteA2Toric

end

end
