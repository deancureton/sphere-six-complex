module

public import SphereSixComplex.Topology.PaperCuspBoundaryQuotientCovering

/-!
# The cusp filling deck action

The filling quotient of the affine cusp boundary deck group is canonically the residual
parameter lattice.  This file transports the established parameter-lattice action across that
equivalence and proves compatibility with the explicit additive cusp cover.
-/

@[expose] public section

noncomputable section

open Matrix Set Topology

namespace SphereSixComplex

open Geometry Geometry.ComplexTorus Geometry.CuspPuncturedCollarBridge
open Geometry.StandardInfiniteA2ToricModel

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates.CuspPeriodExpansion

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
variable {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- The actual local cusp action, reindexed by the canonical filling deck group. -/
@[instance_reducible] public noncomputable def paperCuspFillingDeckAction
    (W : ActualPuncturedCuspCollarWitness N M) :
    MulAction paperCuspBoundaryDeckData.FillingDeck
      (LocalCarrier M W.localWitness.radius) := by
  let C := NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
    N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ := (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  exact MulAction.compHom _ paperCuspFillingDeckEquiv.toMonoidHom

@[simp]
public theorem paperCuspFillingDeck_smul_apply
    (W : ActualPuncturedCuspCollarWitness N M)
    (g : paperCuspBoundaryDeckData.FillingDeck)
    (p : LocalCarrier M W.localWitness.radius) :
    let C := NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
    letI := paperCuspFillingDeckAction W
    g • p = (C.toCuspActionData W.localWitness.fixedPoint).psiMap
      (paperCuspFillingDeckEquiv g).toAdd p :=
  rfl

/-- Reindexing by the filling deck equivalence preserves the quotient-covering structure. -/
public theorem actualCuspFillingProjection_isQuotientCoveringMap_fillingDeck
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := paperCuspFillingDeckAction W
    IsQuotientCoveringMap (actualCuspFillingProjection W)
      paperCuspBoundaryDeckData.FillingDeck := by
  let C := NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
    N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ := (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  have h := actualCuspFillingProjection_isQuotientCoveringMap W
  let _ := paperCuspFillingDeckAction W
  refine {
    __ := h.toIsQuotientMap
    continuous_const_smul := fun g ↦ h.continuous_const_smul (paperCuspFillingDeckEquiv g)
    apply_eq_iff_mem_orbit := ?_
    disjoint := ?_
  }
  · intro a b
    constructor
    · intro hab
      obtain ⟨g, hg⟩ := (h.apply_eq_iff_mem_orbit).mp hab
      rw [MulAction.mem_orbit_iff]
      refine ⟨paperCuspFillingDeckEquiv.symm g, ?_⟩
      rw [paperCuspFillingDeck_smul_apply, MulEquiv.apply_symm_apply]
      rw [← (C.toCuspActionData W.localWitness.fixedPoint).psi_smul]
      exact hg
    · rw [MulAction.mem_orbit_iff]
      rintro ⟨g, hg⟩
      apply h.apply_eq_iff_mem_orbit.mpr
      refine ⟨paperCuspFillingDeckEquiv g, ?_⟩
      change paperCuspFillingDeckEquiv g • b = a
      rw [show paperCuspFillingDeckEquiv g =
          Multiplicative.ofAdd (paperCuspFillingDeckEquiv g).toAdd from rfl]
      rw [(C.toCuspActionData W.localWitness.fixedPoint).psi_smul]
      simpa only [paperCuspFillingDeck_smul_apply] using hg
  · intro p
    obtain ⟨U, hU, hdisjoint⟩ := h.disjoint p
    refine ⟨U, hU, ?_⟩
    intro g hg
    apply paperCuspFillingDeckEquiv.injective
    rw [map_one]
    apply hdisjoint (paperCuspFillingDeckEquiv g)
    rcases hg with ⟨y, ⟨x, hx, hxy⟩, hy⟩
    refine ⟨y, ⟨x, hx, ?_⟩, hy⟩
    change g • x = y at hxy
    rw [paperCuspFillingDeck_smul_apply] at hxy
    change paperCuspFillingDeckEquiv g • x = y
    rw [show paperCuspFillingDeckEquiv g =
        Multiplicative.ofAdd (paperCuspFillingDeckEquiv g).toAdd from rfl]
    rw [(C.toCuspActionData W.localWitness.fixedPoint).psi_smul]
    exact hxy

/-- A rank-four period translation of the additive cover becomes the residual parameter-lattice
action on the local toric filling carrier. -/
public theorem additiveCuspFillingLift_latticeTranslate
    (W : ActualPuncturedCuspCollarWitness N M) (v : Lattice)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    let C := NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
    C.psiMap (paperCuspResidualProjection v) (additiveCuspFillingLift W p) =
      additiveCuspFillingLift W (cuspBoundaryLatticeTranslate W v p) := by
  let C := NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
    N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let x := periodValues
    (assembledFuchsianPeriodFunctions E D).tau
    (assembledFuchsianPeriodFunctions E D).mu
    (assembledFuchsianPeriodFunctions E D).beta (N.lift p.1.2)
  let lambda := firstParameterCoefficients v
  let n := identityParameterCoefficients v
  have hlambda : lambda = paperCuspResidualProjection v := by
    funext i
    fin_cases i <;> rfl
  have hperiod : periodVector x v =
      (periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) + fun i ↦ (n i : ℂ) := by
    rw [integerPeriods_decompose v, periodVector_add,
      periodVector_firstPeriodCoefficients, periodVector_identityPeriodCoefficients]
  have htranslated : periodVector x v + p.1.1 =
      ((periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) + p.1.1) +
        fun i ↦ (n i : ℂ) := by
    rw [hperiod]
    abel
  rw [← hlambda]
  change C.psiMap lambda
      ((additiveToPuncturedLocalHomeomorph M W.localWitness.radius
        (Quotient.mk _ p)).1) =
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      (Quotient.mk _ (cuspBoundaryLatticeTranslate W v p))).1
  rw [show ((additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      (Quotient.mk _ p)).1 : LocalCarrier M W.localWitness.radius) =
      localCuspExponentialPoint M W.localWitness.radius p.1.1 p.1.2
        (mem_ball_zero_iff.mpr p.2) from
    additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius p]
  rw [localCuspExponentialPoint_period_equivariant N M
    W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
    p.1.2 (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p)
    (mem_ball_zero_iff.mpr p.2) p.1.1 lambda]
  rw [show ((additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      (Quotient.mk _ (cuspBoundaryLatticeTranslate W v p))).1 :
        LocalCarrier M W.localWitness.radius) =
      localCuspExponentialPoint M W.localWitness.radius
        (periodVector x v + p.1.1) p.1.2 (mem_ball_zero_iff.mpr p.2) from
    additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius
      (cuspBoundaryLatticeTranslate W v p)]
  apply Subtype.ext
  rw [localCuspExponentialPoint_coe, localCuspExponentialPoint_coe, htranslated]
  apply congrArg M.torusEmbedding
  exact (denseCuspExponential_add_int
    ((periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) + p.1.1) p.1.2 n).symm

/-- Integral angular translation is invisible after mapping the additive cover to the local toric
carrier. -/
public theorem additiveCuspFillingLift_angularTranslate
    (W : ActualPuncturedCuspCollarWitness N M) (k : ℤ)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    additiveCuspFillingLift W (cuspBoundaryAngularTranslate W k p) =
      additiveCuspFillingLift W p := by
  change (additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      (Quotient.mk _ (cuspBoundaryAngularTranslate W k p))).1 =
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      (Quotient.mk _ p)).1
  rw [show ((additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      (Quotient.mk _ (cuspBoundaryAngularTranslate W k p))).1 :
        LocalCarrier M W.localWitness.radius) =
      localCuspExponentialPoint M W.localWitness.radius p.1.1 (p.1.2 - k)
        (mem_ball_zero_iff.mpr (cuspBoundaryAngularTranslate W k p).2) from
    additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius
      (cuspBoundaryAngularTranslate W k p),
    show ((additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      (Quotient.mk _ p)).1 : LocalCarrier M W.localWitness.radius) =
      localCuspExponentialPoint M W.localWitness.radius p.1.1 p.1.2
        (mem_ball_zero_iff.mpr p.2) from
    additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius p]
  apply Subtype.ext
  rw [localCuspExponentialPoint_coe, localCuspExponentialPoint_coe]
  apply congrArg M.torusEmbedding
  ext i
  fin_cases i
  · rfl
  · rfl
  · simpa [denseCuspExponential, sub_eq_add_neg, Int.cast_neg] using congrArg Units.val
      (exponentialUnit_add_int p.1.2 (-k))

/-- The additive cusp filling lift is equivariant for the boundary deck action and the canonical
map to the filling deck group. -/
public theorem additiveCuspFillingLift_paperCuspBoundaryDeck_smul
    (W : ActualPuncturedCuspCollarWitness N M) (g : paperCuspBoundaryDeck)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    letI := paperCuspBoundaryDeckAction W
    letI := paperCuspFillingDeckAction W
    additiveCuspFillingLift W (g • p) =
      paperCuspBoundaryDeckData.fillingDeckMap g • additiveCuspFillingLift W p := by
  let _ := paperCuspBoundaryDeckAction W
  let _ := paperCuspFillingDeckAction W
  rw [paperCuspBoundaryDeck_smul_apply, paperCuspFillingDeck_smul_apply,
    paperCuspFillingDeckEquiv_fillingDeckMap, paperCuspBoundaryDeckProjection_apply]
  change additiveCuspFillingLift W
      (cuspBoundaryLatticeTranslate W g.left.toAdd
        (cuspBoundaryAngularTranslate W g.right.toAdd p)) = _
  rw [← additiveCuspFillingLift_latticeTranslate,
    additiveCuspFillingLift_angularTranslate]
  exact (NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
    N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le).psiMap_eq_generic
      W.localWitness.fixedPoint _ _

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex

end
