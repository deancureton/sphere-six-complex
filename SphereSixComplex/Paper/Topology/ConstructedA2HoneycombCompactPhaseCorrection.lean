module

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
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

@[simp]
public theorem frozenCompactPhase_zero :
    frozenCompactPhase N 0 = 1 := by
  ext i
  fin_cases i <;>
    simp [frozenCompactPhase, normalizedCuspPositiveTwist, positiveRadialPart]




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
