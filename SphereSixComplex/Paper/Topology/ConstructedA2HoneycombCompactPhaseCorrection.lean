module

public import SphereSixComplex.Paper.Topology.ConstructedNormalizedPolarHoneycombReduction
public import SphereSixComplex.Paper.Topology.ConstructedA2HoneycombCorrectedHexagonalCell
public import SphereSixComplex.Paper.Topology.ConstructedA2HoneycombCorrectedActualQuotientCell

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.InfiniteA2Toric

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
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
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
    (M : Model) (r : ℝ) (lambda : ParameterLattice) (p : localCarrier M r) :
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
    (M : Model) (r : ℝ) (i : Fin 6) (p : localCarrier M r) :
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
    (p : localCarrier M r) :
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
    (x : Fin 2 → ℝ) : localCarrier constructedModel W.localWitness.radius :=
  compactPhaseLocalAction constructedModel W.localWitness.radius
    (constructedA2HoneycombCompactPhaseCorrection (N := N)
      (constructedA2CorrectedHexagonHomeomorph 0 x))
    (constructedA2PositiveCentralPoint W
      (constructedA2CorrectedPositiveHexagonMap
        W.localWitness.radius_pos 0 x) :
      localCarrier constructedModel W.localWitness.radius)

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
  let J := continuousTorusAction constructedModel
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
    (h : ((q : localCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) =
        ((constructedCentralOneCellRepresentativePoint W i x :
          localCarrier constructedModel W.localWitness.radius) :
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

/-- Integral character matrices act on the compact phase torus. -/
public def constructedCompactPhaseMonomial
    (A : Matrix (Fin 3) (Fin 3) ℤ) (k : CompactTorus) : CompactTorus :=
  fun i ↦ ∏ j, k j ^ A i j

public theorem constructedCompactPhaseMonomial_coe
    (A : Matrix (Fin 3) (Fin 3) ℤ) (k : CompactTorus) :
    (fun i ↦ (constructedCompactPhaseMonomial A k i : ℂ)) =
      monomial A (fun i ↦ (k i : ℂ)) := by
  funext i
  simp [constructedCompactPhaseMonomial, monomial, Fin.prod_univ_succ]

public theorem constructedCompactPhaseMonomial_continuous
    (A : Matrix (Fin 3) (Fin 3) ℤ) : Continuous (constructedCompactPhaseMonomial A) := by
  unfold constructedCompactPhaseMonomial
  fun_prop

public theorem constructedCompactPhaseMonomial_comp
    (A B : Matrix (Fin 3) (Fin 3) ℤ) (k : CompactTorus) :
    constructedCompactPhaseMonomial A (constructedCompactPhaseMonomial B k) =
      constructedCompactPhaseMonomial (A * B) k := by
  have hk : (fun i ↦ (k i : ℂ)) ∈ coordinateTorus := fun i ↦ (k i).coe_ne_zero
  have h := monomial_comp_on_coordinateTorus A B hk
  rw [← constructedCompactPhaseMonomial_coe B k,
    ← constructedCompactPhaseMonomial_coe A,
    ← constructedCompactPhaseMonomial_coe (A * B)] at h
  exact funext fun i ↦ Subtype.ext (congrFun h i)

/-- Unimodular chart coordinates give a continuous, invertible change of compact phases. -/
public def constructedCompactPhaseChartHomeomorph (a : ChartIndex) :
    CompactTorus ≃ₜ CompactTorus where
  toFun := constructedCompactPhaseMonomial (dualMatrix a)
  invFun := constructedCompactPhaseMonomial (a2ConeMatrix a.1 a.2)
  left_inv k := by
    rw [constructedCompactPhaseMonomial_comp, coneMatrix_mul_dualMatrix]
    ext i
    simpa only [constructedCompactPhaseMonomial_coe, monomial_one] using
      congrFun (constructedCompactPhaseMonomial_coe 1 k) i
  right_inv k := by
    rw [constructedCompactPhaseMonomial_comp, dualMatrix_mul_coneMatrix]
    ext i
    simpa only [constructedCompactPhaseMonomial_coe, monomial_one] using
      congrFun (constructedCompactPhaseMonomial_coe 1 k) i
  continuous_toFun := constructedCompactPhaseMonomial_continuous _
  continuous_invFun := constructedCompactPhaseMonomial_continuous _

public theorem constructedCompactPhaseChartHomeomorph_coe
    (a : ChartIndex) (k : CompactTorus) :
    (fun i ↦ (constructedCompactPhaseChartHomeomorph a k i : ℂ)) =
      torusChartCoordinates a (compactTorusEmbedding k) :=
  constructedCompactPhaseMonomial_coe _ _

/-- Two torus translates of a chart point agree precisely when their characters agree on
its nonzero coordinates. -/
public theorem constructedTorusAction_inclusion_eq_iff
    (g h : DenseTorus) (a : ChartIndex) (z : RawCoordinates) :
    constructedModel.torusAction g (inclusion a z) =
        constructedModel.torusAction h (inclusion a z) ↔
      ∀ j, z j ≠ 0 → torusChartCoordinates a g j = torusChartCoordinates a h j := by
  change carrierTorusActionFun g (inclusion a z) =
      carrierTorusActionFun h (inclusion a z) ↔ _
  rw [carrierTorusActionFun_inclusion, carrierTorusActionFun_inclusion,
    (inclusion_isOpenEmbedding a).injective.eq_iff]
  constructor
  · intro heq j hj
    exact mul_right_cancel₀ hj (congrFun heq j)
  · intro heq
    funext j
    by_cases hj : z j = 0
    · simp [hj]
    · exact congrArg (fun c : ℂ ↦ c * z j) (heq j hj)

/-- The exact compact-phase fibres on each positive square chart are determined by the two
surviving toric characters. -/
public theorem constructedA2CellSquareCarrierPoint_compactPhase_eq_iff
    (k l : CompactTorus) (v : ToricLattice) (i : Fin 6)
    (p : ConstructedA2CellSquare) :
    constructedModel.torusAction (compactTorusEmbedding k)
        (constructedA2CellSquareCarrierPoint v i p) =
      constructedModel.torusAction (compactTorusEmbedding l)
        (constructedA2CellSquareCarrierPoint v i p) ↔
      ∀ j, p.1 j ≠ 0 →
        torusChartCoordinates (constructedA2CellChart v i)
            (compactTorusEmbedding k) (constructedA2CellRemoveIndex i j) =
          torusChartCoordinates (constructedA2CellChart v i)
            (compactTorusEmbedding l) (constructedA2CellRemoveIndex i j) := by
  change constructedModel.torusAction _ (inclusion _ _) =
    constructedModel.torusAction _ (inclusion _ _) ↔ _
  rw [constructedTorusAction_inclusion_eq_iff]
  have hlift (j : Fin 2) :
      constructedA2CellLiftCoordinates i (fun a ↦ (p.1 a : ℂ))
          (constructedA2CellRemoveIndex i j) = (p.1 j : ℂ) := by
    have h := constructedA2CellRemoveCoordinates_apply i
      (constructedA2CellLiftCoordinates i (fun a ↦ (p.1 a : ℂ))) j
    rw [constructedA2CellRemoveCoordinates_lift] at h
    exact h.symm
  constructor
  · intro h j hj
    apply h
    rw [hlift]
    exact_mod_cast hj
  · intro h a ha
    have hne : a ≠ constructedA2CellZeroCoordinate i := by
      rintro rfl
      exact ha (constructedA2CellLiftCoordinates_zero _ _)
    obtain ⟨j, rfl⟩ : ∃ j, constructedA2CellRemoveIndex i j = a := by
      fin_cases i <;> fin_cases a <;>
        simp_all [constructedA2CellZeroCoordinate, constructedA2CellRemoveIndex]
    apply h
    rw [hlift] at ha
    exact_mod_cast ha

/-- On the component of the zero ray, the effective compact phases are the first two
intrinsic torus coordinates in every one of its six charts. -/
public theorem constructedA2ZeroRay_effectivePhase_iff
    (k l : CompactTorus) (i : Fin 6) :
    (∀ j : Fin 2,
      torusChartCoordinates (constructedA2CellChart 0 i)
          (compactTorusEmbedding k) (constructedA2CellRemoveIndex i j) =
        torusChartCoordinates (constructedA2CellChart 0 i)
          (compactTorusEmbedding l) (constructedA2CellRemoveIndex i j)) ↔
      (k 0 = l 0 ∧ k 1 = l 1) := by
  have hcoe (a b : Circle) : (a : ℂ) = (b : ℂ) ↔ a = b :=
    ⟨Subtype.ext, congrArg Subtype.val⟩
  fin_cases i <;>
    simp only [← hcoe] <;>
    simp [constructedA2CellChart, constructedA2CellRemoveIndex, torusChartCoordinates,
      dualMatrix, a2DualCharacter, monomial, denseRawCoordinates, compactTorusEmbedding,
      e₁, e₂, Fin.prod_univ_succ, Fin.forall_fin_two]
  all_goals constructor <;> rintro ⟨h0, h1⟩ <;>
    simp_all [← _root_.mul_inv_rev, (l 0).coe_ne_zero, (l 1).coe_ne_zero]

/-- The same two intrinsic phases classify every interior chart over the zero ray. -/
public theorem constructedA2CellSquareCarrierPoint_zeroRay_phase_eq_iff
    (k l : CompactTorus) (i : Fin 6) (p : ConstructedA2CellSquare)
    (hp : ∀ j, p.1 j ≠ 0) :
    constructedModel.torusAction (compactTorusEmbedding k)
        (constructedA2CellSquareCarrierPoint 0 i p) =
      constructedModel.torusAction (compactTorusEmbedding l)
        (constructedA2CellSquareCarrierPoint 0 i p) ↔
      (k 0 = l 0 ∧ k 1 = l 1) := by
  rw [constructedA2CellSquareCarrierPoint_compactPhase_eq_iff]
  constructor
  · intro h
    exact (constructedA2ZeroRay_effectivePhase_iff k l i).mp (fun j ↦ h j (hp j))
  · intro h j _
    exact (constructedA2ZeroRay_effectivePhase_iff k l i).mpr h j

/-- A point supported on only the central ray has no further zero chart coordinate. -/
public theorem constructedA2CellSquare_nonzero_of_singletonSupport
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare)
    (hp : componentSupport constructedModel
      (constructedA2CellSquareCarrierPoint v i p) = {v}) :
    ∀ j, p.1 j ≠ 0 := by
  intro j hj
  let a := constructedA2CellChart v i
  let b := constructedA2CellRemoveIndex i j
  have hmem : a2Triangle a.1 a.2 b ∈ componentSupport constructedModel
      (constructedA2CellSquareCarrierPoint v i p) := by
    change constructedA2CellSquareCarrierPoint v i p ∈
      carrierCentralComponent (a2Triangle a.1 a.2 b)
    refine ⟨a, b, constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)),
      rfl, ?_, rfl⟩
    have h := constructedA2CellRemoveCoordinates_apply i
      (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) j
    rw [constructedA2CellRemoveCoordinates_lift] at h
    simpa [b, hj] using h.symm
  rw [hp, Set.mem_singleton_iff] at hmem
  change a2Triangle (constructedA2CellChart v i).1
    (constructedA2CellChart v i).2 (constructedA2CellRemoveIndex i j) = v at hmem
  fin_cases i <;> fin_cases j <;>
    simp [constructedA2CellChart, constructedA2CellRemoveIndex, a2Triangle,
      e₁, e₂, funext_iff, Fin.forall_fin_two, Matrix.vecHead, Matrix.vecTail] at hmem

/-- Effective phases agree globally on the positive singleton-support stratum, independently
of which of the six affine charts represents the point. -/
public theorem constructedPositiveCentralCell_zeroRay_phase_eq_iff
    {r : ℝ} (hr : 0 < r) (q : constructedPositiveCentralCell r 0)
    (hq : componentSupport constructedModel (q.1.1.1.1 : Carrier) = {0})
    (k l : CompactTorus) :
    constructedModel.torusAction (compactTorusEmbedding k) (q.1.1.1.1 : Carrier) =
      constructedModel.torusAction (compactTorusEmbedding l) (q.1.1.1.1 : Carrier) ↔
      (k 0 = l 0 ∧ k 1 = l 1) := by
  obtain ⟨⟨i, p⟩, rfl⟩ := constructedA2CellSquareProjection_surjective hr 0 q
  exact constructedA2CellSquareCarrierPoint_zeroRay_phase_eq_iff k l i p
    (constructedA2CellSquare_nonzero_of_singletonSupport 0 i p hq)

/-- The canonical section of effective phases on the zero-ray component. -/
public def constructedA2EffectivePhaseSection (k : Fin 2 → Circle) : CompactTorus :=
  ![k 0, k 1, 1]

public theorem constructedA2EffectivePhaseSection_continuous :
    Continuous constructedA2EffectivePhaseSection := by
  unfold constructedA2EffectivePhaseSection
  fun_prop

/-- Normalizing the third intrinsic phase preserves every interior zero-ray chart point. -/
public theorem constructedA2CellSquareCarrierPoint_phase_normalize
    (k : CompactTorus) (i : Fin 6) (p : ConstructedA2CellSquare)
    (hp : ∀ j, p.1 j ≠ 0) :
    constructedModel.torusAction
        (compactTorusEmbedding (constructedA2EffectivePhaseSection (fun j ↦ k j.castSucc)))
        (constructedA2CellSquareCarrierPoint 0 i p) =
      constructedModel.torusAction (compactTorusEmbedding k)
        (constructedA2CellSquareCarrierPoint 0 i p) := by
  apply (constructedA2CellSquareCarrierPoint_zeroRay_phase_eq_iff _ _ i p hp).mpr
  exact ⟨rfl, rfl⟩

public theorem constructedA2CellSquareCarrierPoint_effectivePhase_injective
    (i : Fin 6) (p : ConstructedA2CellSquare) (hp : ∀ j, p.1 j ≠ 0) :
    Function.Injective (fun k : Fin 2 → Circle ↦
      constructedModel.torusAction (compactTorusEmbedding (constructedA2EffectivePhaseSection k))
        (constructedA2CellSquareCarrierPoint 0 i p)) := by
  intro k l h
  have hk := (constructedA2CellSquareCarrierPoint_zeroRay_phase_eq_iff _ _ i p hp).mp h
  funext j
  fin_cases j
  · exact hk.1
  · exact hk.2

/-- Effective phase action on the actual prequotient central fibre. -/
public def constructedA2EffectivePhaseCentralPoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) (q : constructedPositiveCentralFiber W.localWitness.radius) :
    actualLocalCuspCentralSubMulAction W :=
  ⟨compactPhaseLocalAction constructedModel W.localWitness.radius
      (constructedA2EffectivePhaseSection k) (constructedA2PositiveCentralPoint W q).1, by
    change constructedModel.t
      (constructedModel.torusAction (compactTorusEmbedding (constructedA2EffectivePhaseSection k))
        q.1.1.1) = 0
    rw [constructedModel.t_torusAction, q.property, mul_zero]⟩

public theorem constructedA2EffectivePhaseCentralPoint_support
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) (q : constructedPositiveCentralFiber W.localWitness.radius) :
    componentSupport constructedModel
        ((constructedA2EffectivePhaseCentralPoint W k q).1.1 : Carrier) =
      componentSupport constructedModel (q.1.1.1 : Carrier) := by
  ext v
  exact constructedModel.torusAction_centralComponent _ _ _

/-- The canonical effective-phase parametrization in the actual central orbit quotient. -/
public def constructedA2EffectivePhaseCentralOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) (q : constructedPositiveCentralFiber W.localWitness.radius) :
    ActualLocalCuspCentralOrbitQuotient W := by
  let _ := actualLocalCuspQuotientAction W
  exact Quotient.mk _ (constructedA2EffectivePhaseCentralPoint W k q)

public theorem constructedA2EffectivePhaseCentralOrbit_injective
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : constructedPositiveCentralCell W.localWitness.radius 0)
    (hq : componentSupport constructedModel (q.1.1.1.1 : Carrier) = {0}) :
    Function.Injective (fun k : Fin 2 → Circle ↦
      constructedA2EffectivePhaseCentralOrbit W k q.1) := by
  intro k l h
  let _ := actualLocalCuspQuotientAction W
  have heq := constructedA2ActualCentralOrbitRel_coe_eq_of_singletonSupport W 0
    (constructedA2EffectivePhaseCentralPoint W k q.1)
    (constructedA2EffectivePhaseCentralPoint W l q.1)
    (by rw [constructedA2EffectivePhaseCentralPoint_support]; exact hq)
    (by rw [constructedA2EffectivePhaseCentralPoint_support]; exact hq)
    (Quotient.exact h)
  have hk := (constructedPositiveCentralCell_zeroRay_phase_eq_iff
    W.localWitness.radius_pos q hq
    (constructedA2EffectivePhaseSection k) (constructedA2EffectivePhaseSection l)).mp heq
  funext j
  fin_cases j
  · exact hk.1
  · exact hk.2

/-- Positive representatives supported on exactly the zero ray. -/
public abbrev constructedA2PositiveSingletonStratum (r : ℝ) :=
  {q : constructedPositiveCentralCell r 0 |
    componentSupport constructedModel (q.1.1.1.1 : Carrier) = {0}}

/-- Positive representative and effective phase are jointly unique in the actual orbit
quotient. -/
public theorem constructedA2EffectivePhaseCentralOrbit_jointly_injective
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Function.Injective
      (fun p : constructedA2PositiveSingletonStratum W.localWitness.radius × (Fin 2 → Circle) ↦
        constructedA2EffectivePhaseCentralOrbit W p.2 p.1.1.1) := by
  rintro ⟨q, k⟩ ⟨s, l⟩ h
  let _ := actualLocalCuspQuotientAction W
  have heq := constructedA2ActualCentralOrbitRel_coe_eq_of_singletonSupport W 0
    (constructedA2EffectivePhaseCentralPoint W k q.1.1)
    (constructedA2EffectivePhaseCentralPoint W l s.1.1)
    (by rw [constructedA2EffectivePhaseCentralPoint_support]; exact q.property)
    (by rw [constructedA2EffectivePhaseCentralPoint_support]; exact s.property)
    (Quotient.exact h)
  have hm := congrArg carrierModulus heq
  change carrierModulus (carrierTorusAction
      (compactTorusEmbedding (constructedA2EffectivePhaseSection k)) q.1.1.1.1.1) =
    carrierModulus (carrierTorusAction
      (compactTorusEmbedding (constructedA2EffectivePhaseSection l)) s.1.1.1.1.1) at hm
  have hm' := (carrierModulus_compactTorusAction
    (constructedA2EffectivePhaseSection k) (q.1.1.1.1.1 : Carrier)).symm.trans
      (hm.trans (carrierModulus_compactTorusAction
        (constructedA2EffectivePhaseSection l) (s.1.1.1.1.1 : Carrier)))
  have hfixed (x : constructedPositiveCentralFiber W.localWitness.radius) :
      carrierModulus x.1.1.1 = x.1.1.1 :=
    (mem_constructedLocalPositivePart_iff W.localWitness.radius _).mp x.1.property
  have hraw := (hfixed q.1.1).symm.trans (hm'.trans (hfixed s.1.1))
  have hqs : q = s := Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext hraw))))
  subst s
  have hkl := constructedA2EffectivePhaseCentralOrbit_injective W q.1 q.property h
  exact Prod.ext rfl hkl

end SphereSixComplex.Geometry.InfiniteA2Toric

end
