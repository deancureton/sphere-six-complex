module

public import SphereSixComplex.Topology.ConstructedNormalizedPolarHoneycombReduction
public import SphereSixComplex.Topology.ConstructedA2HoneycombCorrectedHexagonalCell
public import SphereSixComplex.Topology.ConstructedA2HoneycombCorrectedActualQuotientCell

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup
open SphereSixComplex.LatticeData
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

@[simp]
public theorem frozenCompactPhase_zero :
    frozenCompactPhase N 0 = 1 := by
  ext i
  fin_cases i <;>
    simp [frozenCompactPhase, normalizedCuspPositiveTwist, positiveRadialPart]

public theorem frozenCompactPhase_add (lambda mu : ParameterLattice) :
    frozenCompactPhase N (lambda + mu) =
      frozenCompactPhase N lambda * frozenCompactPhase N mu := by
  ext i
  change ((phaseEmbedding (N.phaseCoefficient (lambda + mu) 0) i : ℂ) /
      (normalizedCuspPositiveTwist N (lambda + mu) i : ℂ)) =
    ((phaseEmbedding (N.phaseCoefficient lambda 0) i : ℂ) /
        (normalizedCuspPositiveTwist N lambda i : ℂ)) *
      ((phaseEmbedding (N.phaseCoefficient mu 0) i : ℂ) /
        (normalizedCuspPositiveTwist N mu i : ℂ))
  rw [N.phaseCoefficient_add, map_mul, Pi.mul_apply,
    normalizedCuspPositiveTwist_add, Pi.mul_apply]
  simp only [Units.val_mul]
  ring

public theorem frozenCompactPhase_neg (lambda : ParameterLattice) :
    frozenCompactPhase N (-lambda) = (frozenCompactPhase N lambda)⁻¹ := by
  have h := frozenCompactPhase_add (N := N) (-lambda) lambda
  rw [neg_add_cancel, frozenCompactPhase_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

public theorem compactPhaseLocalAction_frozen_inverse_frozenLocalPsiMap
    (M : Model) (r : ℝ) (lambda : ParameterLattice) (p : LocalCarrier M r) :
    compactPhaseLocalAction M r (frozenCompactPhase N lambda)⁻¹
        (frozenLocalPsiMap N M r lambda p) =
      normalizedPositiveDeckLocalMap N M r lambda p := by
  rw [frozenLocalPsiMap_eq_compactPhase_positiveDeck]
  apply Subtype.ext
  change M.torusAction (compactTorusEmbedding (frozenCompactPhase N lambda)⁻¹)
      (M.torusAction (compactTorusEmbedding (frozenCompactPhase N lambda))
        (normalizedPositiveDeckLocalMap N M r lambda p : M.Carrier)) =
    (normalizedPositiveDeckLocalMap N M r lambda p : M.Carrier)
  rw [← Equiv.Perm.mul_apply]
  simp

/-- The six oriented nearest-neighbor vectors of the corrected hexagonal tiling. -/
public def constructedA2BoundaryDisplacement : Fin 6 → ToricLattice :=
  ![e₁, e₂, e₂ - e₁, -e₁, -e₂, e₁ - e₂]

/-- The unique cusp parameter whose shear is a prescribed boundary displacement. -/
public def constructedA2BoundaryShearParameter (i : Fin 6) : ParameterLattice :=
  B₀Inv *ᵥ constructedA2BoundaryDisplacement i

public theorem shearVector_constructedA2BoundaryShearParameter (i : Fin 6) :
    shearVector (constructedA2BoundaryShearParameter i) =
      constructedA2BoundaryDisplacement i := by
  change B₀ *ᵥ (B₀Inv *ᵥ constructedA2BoundaryDisplacement i) = _
  rw [Matrix.mulVec_mulVec, B₀_mul_inv]
  simp

public theorem constructedA2BoundaryShearPhase_cancellation
    (M : Model) (r : ℝ) (i : Fin 6) (p : LocalCarrier M r) :
    compactPhaseLocalAction M r
        (frozenCompactPhase N (constructedA2BoundaryShearParameter i))⁻¹
        (frozenLocalPsiMap N M r (constructedA2BoundaryShearParameter i) p) =
      normalizedPositiveDeckLocalMap N M r
        (constructedA2BoundaryShearParameter i) p :=
  compactPhaseLocalAction_frozen_inverse_frozenLocalPsiMap M r _ p

/-- A real-linear lift of the two generator phases.  Unlike a pointwise choice of paths,
this lift is additive, so it satisfies the deck cocycle on every paired side. -/
public def constructedA2FrozenCompactPhaseInterpolation
    (x : Fin 2 → ℝ) : CompactTorus := fun i ↦
  Circle.exp
    (x 0 * Complex.arg (frozenCompactPhase N e₁ i) +
      x 1 * Complex.arg (frozenCompactPhase N e₂ i))

@[simp]
public theorem constructedA2FrozenCompactPhaseInterpolation_zero :
    constructedA2FrozenCompactPhaseInterpolation (N := N) 0 = 1 := by
  ext i
  simp [constructedA2FrozenCompactPhaseInterpolation]

public theorem constructedA2FrozenCompactPhaseInterpolation_add
    (x y : Fin 2 → ℝ) :
    constructedA2FrozenCompactPhaseInterpolation (N := N) (x + y) =
      constructedA2FrozenCompactPhaseInterpolation (N := N) x *
        constructedA2FrozenCompactPhaseInterpolation (N := N) y := by
  ext i
  simp only [constructedA2FrozenCompactPhaseInterpolation, Pi.add_apply, Pi.mul_apply]
  rw [show (x 0 + y 0) * Complex.arg (frozenCompactPhase N e₁ i) +
        (x 1 + y 1) * Complex.arg (frozenCompactPhase N e₂ i) =
      (x 0 * Complex.arg (frozenCompactPhase N e₁ i) +
        x 1 * Complex.arg (frozenCompactPhase N e₂ i)) +
      (y 0 * Complex.arg (frozenCompactPhase N e₁ i) +
        y 1 * Complex.arg (frozenCompactPhase N e₂ i)) by ring]
  exact congrArg Subtype.val (Circle.exp_add _ _)

public theorem constructedA2FrozenCompactPhaseInterpolation_continuous :
    Continuous (constructedA2FrozenCompactPhaseInterpolation (N := N)) := by
  apply continuous_pi
  intro i
  exact Circle.exp.continuous.comp (by fun_prop)

private theorem toricLattice_eq_coordinates (lambda : ToricLattice) :
    lambda = lambda 0 • e₁ + lambda 1 • e₂ := by
  ext i
  fin_cases i <;> simp [e₁, e₂]

private def frozenCompactPhaseAddHom :
    ParameterLattice →+ Additive CompactTorus where
  toFun lambda := Additive.ofMul (frozenCompactPhase N lambda)
  map_zero' := congrArg Additive.ofMul frozenCompactPhase_zero
  map_add' lambda mu :=
    congrArg Additive.ofMul (frozenCompactPhase_add lambda mu)

private theorem frozenCompactPhase_zsmul (z : ℤ) (lambda : ParameterLattice) :
    frozenCompactPhase N (z • lambda) = frozenCompactPhase N lambda ^ z := by
  have h := (frozenCompactPhaseAddHom (N := N)).map_zsmul z lambda
  exact congrArg Additive.toMul h

public theorem constructedA2FrozenCompactPhaseInterpolation_lattice
    (lambda : ParameterLattice) :
    constructedA2FrozenCompactPhaseInterpolation (N := N)
        (fun i ↦ (lambda i : ℝ)) =
      frozenCompactPhase N lambda := by
  calc
    constructedA2FrozenCompactPhaseInterpolation (N := N)
          (fun i ↦ (lambda i : ℝ)) =
        frozenCompactPhase N e₁ ^ lambda 0 *
          frozenCompactPhase N e₂ ^ lambda 1 := by
      ext i
      simp only [constructedA2FrozenCompactPhaseInterpolation, Pi.mul_apply,
        Pi.pow_apply]
      rw [Circle.exp_add, Circle.exp_intCast_mul, Circle.exp_intCast_mul,
        Circle.exp_arg, Circle.exp_arg]
    _ = frozenCompactPhase N
          (lambda 0 • e₁ + lambda 1 • e₂) := by
      rw [frozenCompactPhase_add, frozenCompactPhase_zsmul,
        frozenCompactPhase_zsmul]
    _ = frozenCompactPhase N lambda := by
      rw [← toricLattice_eq_coordinates lambda]

/-- Real shear coordinates dual to the corrected planar center coordinates. -/
public def constructedA2RealPlaneLatticeCoordinate (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(x 0 - 2 * x 1) / 2, (x 0 + x 1) / 2]

public def constructedA2RealShearCoordinate (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i ↦ ∑ j, (B₀Inv i j : ℝ) * constructedA2RealPlaneLatticeCoordinate x j

public theorem constructedA2RealShearCoordinate_add (x y : Fin 2 → ℝ) :
    constructedA2RealShearCoordinate (x + y) =
      constructedA2RealShearCoordinate x + constructedA2RealShearCoordinate y := by
  ext i
  simp only [constructedA2RealShearCoordinate, Pi.add_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  fin_cases j <;> simp [constructedA2RealPlaneLatticeCoordinate] <;> ring

public theorem constructedA2RealPlaneLatticeCoordinate_center
    (v : ToricLattice) :
    constructedA2RealPlaneLatticeCoordinate
        (constructedA2CorrectedPlaneCenter v) =
      fun i ↦ (v i : ℝ) := by
  ext i
  fin_cases i <;>
    simp [constructedA2RealPlaneLatticeCoordinate,
      constructedA2CorrectedPlaneCenter] <;> ring

public theorem constructedA2RealShearCoordinate_center
    (v : ToricLattice) :
    constructedA2RealShearCoordinate (constructedA2CorrectedPlaneCenter v) =
      fun i ↦ (B₀Inv.mulVec v i : ℝ) := by
  ext i
  simp only [constructedA2RealShearCoordinate,
    constructedA2RealPlaneLatticeCoordinate_center, Matrix.mulVec]
  norm_cast

/-- The canonical phase correction on the corrected honeycomb plane. -/
public def constructedA2HoneycombCompactPhaseCorrection
    (x : Fin 2 → ℝ) : CompactTorus :=
  (constructedA2FrozenCompactPhaseInterpolation (N := N)
    (constructedA2RealShearCoordinate x))⁻¹

public theorem constructedA2HoneycombCompactPhaseCorrection_continuous :
    Continuous (constructedA2HoneycombCompactPhaseCorrection (N := N)) := by
  exact (constructedA2FrozenCompactPhaseInterpolation_continuous (N := N)).inv.comp
    (by
      unfold constructedA2RealShearCoordinate constructedA2RealPlaneLatticeCoordinate
      fun_prop)

public theorem constructedA2HoneycombCompactPhaseCorrection_center_translate
    (x : Fin 2 → ℝ) (v : ToricLattice) :
    constructedA2HoneycombCompactPhaseCorrection (N := N)
        (x + constructedA2CorrectedPlaneCenter v) =
      constructedA2HoneycombCompactPhaseCorrection (N := N) x *
        (frozenCompactPhase N (B₀Inv *ᵥ v))⁻¹ := by
  rw [constructedA2HoneycombCompactPhaseCorrection,
    constructedA2HoneycombCompactPhaseCorrection,
    constructedA2RealShearCoordinate_add,
    constructedA2FrozenCompactPhaseInterpolation_add,
    constructedA2RealShearCoordinate_center,
    constructedA2FrozenCompactPhaseInterpolation_lattice]
  simp [mul_comm]

public theorem constructedA2HoneycombCompactPhaseCorrection_boundaryShear
    (x : Fin 2 → ℝ) (i : Fin 6) :
    constructedA2HoneycombCompactPhaseCorrection (N := N)
        (x + constructedA2CorrectedPlaneCenter
          (constructedA2BoundaryDisplacement i)) =
      constructedA2HoneycombCompactPhaseCorrection (N := N) x *
        (frozenCompactPhase N
          (constructedA2BoundaryShearParameter i))⁻¹ := by
  simpa [constructedA2BoundaryShearParameter] using
    constructedA2HoneycombCompactPhaseCorrection_center_translate
      (N := N) x (constructedA2BoundaryDisplacement i)

/-- After translating across any of the six paired sides, the interpolated phase cancels the
frozen phase and leaves exactly the positive deck map. -/
public theorem constructedA2BoundaryShear_interpolatedPhase_cancellation
    (M : Model) (r : ℝ) (x : Fin 2 → ℝ) (i : Fin 6)
    (p : LocalCarrier M r) :
    compactPhaseLocalAction M r
        (constructedA2HoneycombCompactPhaseCorrection (N := N)
          (x + constructedA2CorrectedPlaneCenter
            (constructedA2BoundaryDisplacement i)))
        (frozenLocalPsiMap N M r (constructedA2BoundaryShearParameter i) p) =
      compactPhaseLocalAction M r
        (constructedA2HoneycombCompactPhaseCorrection (N := N) x)
        (normalizedPositiveDeckLocalMap N M r
          (constructedA2BoundaryShearParameter i) p) := by
  rw [constructedA2HoneycombCompactPhaseCorrection_boundaryShear,
    frozenLocalPsiMap_eq_compactPhase_positiveDeck]
  apply Subtype.ext
  change M.torusAction
      (compactTorusEmbedding
        (constructedA2HoneycombCompactPhaseCorrection (N := N) x *
          (frozenCompactPhase N (constructedA2BoundaryShearParameter i))⁻¹))
      (M.torusAction
        (compactTorusEmbedding
          (frozenCompactPhase N (constructedA2BoundaryShearParameter i)))
        (normalizedPositiveDeckLocalMap N M r
          (constructedA2BoundaryShearParameter i) p : M.Carrier)) =
    M.torusAction
      (compactTorusEmbedding
        (constructedA2HoneycombCompactPhaseCorrection (N := N) x))
      (normalizedPositiveDeckLocalMap N M r
        (constructedA2BoundaryShearParameter i) p : M.Carrier)
  rw [map_mul, ← Equiv.Perm.mul_apply, ← map_mul]
  simp

/-- The positive hexagonal representative with the flat compact-phase cocycle cancelled. -/
public def constructedA2PhaseCorrectedHexagonLocal
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 2 → ℝ) : LocalCarrier constructedModel W.localWitness.radius :=
  compactPhaseLocalAction constructedModel W.localWitness.radius
    (constructedA2HoneycombCompactPhaseCorrection (N := N)
      (constructedA2CorrectedHexagonHomeomorph 0 x))
    (constructedA2PositiveCentralPoint W
      (constructedA2CorrectedPositiveHexagonMap
        W.localWitness.radius_pos 0 x) :
      LocalCarrier constructedModel W.localWitness.radius)

public theorem constructedA2PhaseCorrectedHexagonLocal_height
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 2 → ℝ) :
    constructedModel.t (constructedA2PhaseCorrectedHexagonLocal W x :
      constructedModel.Carrier) = 0 := by
  rw [constructedA2PhaseCorrectedHexagonLocal, compactPhaseLocalAction,
    constructedModel.t_torusAction]
  rw [(constructedA2PositiveCentralPoint W
    (constructedA2CorrectedPositiveHexagonMap
      W.localWitness.radius_pos 0 x)).property]
  exact mul_zero _

public def constructedA2PhaseCorrectedHexagonPoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 2 → ℝ) : actualLocalCuspCentralSubMulAction W :=
  ⟨constructedA2PhaseCorrectedHexagonLocal W x,
    constructedA2PhaseCorrectedHexagonLocal_height W x⟩

public def constructedA2PhaseCorrectedHexagonOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 2 → ℝ) : ActualLocalCuspCentralOrbitQuotient W := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact Quotient.mk _ (constructedA2PhaseCorrectedHexagonPoint W x)

public theorem constructedA2PhaseCorrectedHexagonPoint_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedA2PhaseCorrectedHexagonPoint W)
      (Metric.closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_induced_rng,
    continuous_induced_rng]
  let J := establishedContinuousTorusAction constructedModel
  apply J.variable_action
  · exact continuous_compactTorusEmbedding.comp
      ((constructedA2HoneycombCompactPhaseCorrection_continuous (N := N)).comp
        ((constructedA2CorrectedHexagonHomeomorph 0).continuous.comp
          continuous_subtype_val))
  · have hp := (continuousOn_iff_continuous_domRestrict.mp
      (constructedA2CorrectedPositiveHexagonMap_continuousOn
        W.localWitness.radius_pos 0)).subtype_val.subtype_val.subtype_val
    simpa only [constructedA2PositiveCentralPoint, Set.domRestrict_apply] using hp

public theorem constructedA2PhaseCorrectedHexagonOrbit_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedA2PhaseCorrectedHexagonOrbit W)
      (Metric.closedBall 0 1) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact continuous_quotient_mk'.continuousOn.comp
    (constructedA2PhaseCorrectedHexagonPoint_continuousOn W)
      (fun _ _ ↦ Set.mem_univ _)

/-- Any point in the closed image of one of the three established one-cells belongs to the
established positive one-skeleton. -/
public theorem constructedCentralOneCell_mem_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (x : Fin 1 → ℝ) (hx : x ∈ Metric.closedBall 0 1) :
    constructedCentralOneCell W i x ∈ constructedCentralOneSkeleton W := by
  apply Or.inr
  apply Set.mem_iUnion.mpr
  exact ⟨i, x, hx, rfl⟩

/-- Carrier equality with an established one-cell representative is sufficient for
one-skeleton membership in the actual orbit quotient. -/
public def constructedCentralOneCellRepresentativePoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (x : Fin 1 → ℝ) : actualLocalCuspCentralSubMulAction W :=
  ![constructedCentralEdgeZeroPoint W,
    centralEdgePointOf W constructedCentralEdgeOneCarrier
      constructedCentralEdgeOneCarrier_height,
    centralEdgePointOf W constructedCentralEdgeTwoCarrier
      constructedCentralEdgeTwoCarrier_height] i x

public theorem constructedCentralOneCellRepresentativePoint_orbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (x : Fin 1 → ℝ) :
    Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W))
        (constructedCentralOneCellRepresentativePoint W i x) =
      constructedCentralOneCell W i x := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  fin_cases i <;> rfl

public theorem constructedCentralCarrier_eq_oneCell_implies_mem_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : actualLocalCuspCentralSubMulAction W) (i : Fin 3)
    (x : Fin 1 → ℝ) (hx : x ∈ Metric.closedBall 0 1)
    (h : ((q : LocalCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) =
        ((constructedCentralOneCellRepresentativePoint W i x :
          LocalCarrier constructedModel W.localWitness.radius) :
            constructedModel.Carrier)) :
    Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) q ∈
        constructedCentralOneSkeleton W := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hq : Quotient.mk (MulAction.orbitRel
      (Multiplicative ParameterLattice) S) q = constructedCentralOneCell W i x := by
    rw [← constructedCentralOneCellRepresentativePoint_orbit W i x]
    apply congrArg (Quotient.mk (MulAction.orbitRel
      (Multiplicative ParameterLattice) S))
    apply Subtype.ext
    apply Subtype.ext
    exact h
  rw [hq]
  exact constructedCentralOneCell_mem_oneSkeleton W i x hx

/-- On a square-chart boundary, only the toric characters multiplying surviving coordinates
matter.  This is the reusable stabilizer criterion needed to choose side corrections. -/
public theorem constructedA2CellSquareCarrierPoint_compactPhase_eq_self
    (k : CompactTorus) (v : ToricLattice) (i : Fin 6)
    (p : ConstructedA2CellSquare)
    (h : torusChartCoordinates (constructedA2CellChart v i)
          (compactTorusEmbedding k) *
        constructedA2CellLiftCoordinates i (fun j ↦ (p.1 j : ℂ)) =
      constructedA2CellLiftCoordinates i (fun j ↦ (p.1 j : ℂ))) :
    constructedModel.torusAction (compactTorusEmbedding k)
        (constructedA2CellSquareCarrierPoint v i p) =
      constructedA2CellSquareCarrierPoint v i p := by
  change carrierTorusActionFun (compactTorusEmbedding k)
      (inclusion (constructedA2CellChart v i)
        (constructedA2CellLiftCoordinates i (fun j ↦ (p.1 j : ℂ)))) = _
  rw [carrierTorusActionFun_inclusion, h]
  rfl

public theorem constructedA2CellSquareCarrierPoint_compactPhase_eq_self_of_coordinate
    (k : CompactTorus) (v : ToricLattice) (i : Fin 6)
    (p : ConstructedA2CellSquare)
    (h : ∀ j, p.1 j ≠ 0 →
      torusChartCoordinates (constructedA2CellChart v i)
        (compactTorusEmbedding k) (constructedA2CellRemoveIndex i j) = 1) :
    constructedModel.torusAction (compactTorusEmbedding k)
        (constructedA2CellSquareCarrierPoint v i p) =
      constructedA2CellSquareCarrierPoint v i p := by
  apply constructedA2CellSquareCarrierPoint_compactPhase_eq_self
  funext a
  by_cases ha : a = constructedA2CellZeroCoordinate i
  · rw [ha, constructedA2CellLiftCoordinates_zero]
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, constructedA2CellRemoveIndex i j = a := by
      fin_cases i <;> fin_cases a <;>
        simp_all [constructedA2CellZeroCoordinate, constructedA2CellRemoveIndex]
    have hlift :
        constructedA2CellLiftCoordinates i (fun a ↦ (p.1 a : ℂ))
            (constructedA2CellRemoveIndex i j) = (p.1 j : ℂ) := by
      have happly := constructedA2CellRemoveCoordinates_apply i
        (constructedA2CellLiftCoordinates i (fun a ↦ (p.1 a : ℂ))) j
      rw [constructedA2CellRemoveCoordinates_lift] at happly
      exact happly.symm
    rw [Pi.mul_apply, hlift]
    by_cases hp : p.1 j = 0
    · simp [hp]
    · rw [h j hp]
      simp

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
