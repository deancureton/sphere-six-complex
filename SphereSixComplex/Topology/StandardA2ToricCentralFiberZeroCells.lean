module

public import SphereSixComplex.Topology.PaperCuspCentralFiberCWConstruction
public import SphereSixComplex.Geometry.StandardInfiniteA2ToricCarrierGeometryAssembly

/-!
# The zero-cells of the standard `A₂` central-fibre quotient

The two vertex orbits come from the origins of a lower and an upper maximal-cone chart.  Fan
translations preserve the lower/upper label, while phase multiplication fixes every chart origin.
-/

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

/-- The affine origin of a lower or upper chart, regarded as a point of the local carrier. -/
public def constructedCentralOrigin
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (upper : Bool) :
    LocalCarrier constructedModel W.localWitness.radius :=
  ⟨inclusion (upper, 0) 0, by
    change carrierHeight (inclusion (upper, 0) 0) ∈ Metric.ball 0 W.localWitness.radius
    rw [Metric.mem_ball, dist_zero_right, carrierHeight_inclusion]
    simpa [rawHeight] using W.localWitness.radius_pos⟩

public theorem constructedCentralOrigin_height
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (upper : Bool) :
    constructedModel.t (constructedCentralOrigin W upper) = 0 := by
  change carrierHeight (inclusion (upper, 0) 0) = 0
  rw [carrierHeight_inclusion]
  simp [rawHeight]

/-- Origins of lower and upper maximal-cone charts are distinct, independently of their lattice
labels. -/
public theorem lowerOrigin_ne_upperOrigin (v w : ToricLattice) :
    inclusion (false, v) (0 : RawCoordinates) ≠ inclusion (true, w) 0 := by
  intro h
  have hs := ((inclusion_eq_iff (false, v) (true, w) 0 0).mp h).1
  rw [chartChange_source] at hs
  have hnonneg (i j : Fin 3) :
      0 ≤ transitionMatrix (false, v) (true, w) i j := by
    by_contra hneg
    exact hs i j (lt_of_not_ge hneg) rfl
  have h00 := hnonneg 0 0
  have h01 := hnonneg 0 1
  have h02 := hnonneg 0 2
  have h10 := hnonneg 1 0
  have h11 := hnonneg 1 1
  have h12 := hnonneg 1 2
  have h20 := hnonneg 2 0
  have h21 := hnonneg 2 1
  have h22 := hnonneg 2 2
  simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
    heightOneRay, a2Triangle, Matrix.mul_apply, Fin.sum_univ_succ] at *
  omega

/-- A deck transformation translates the fan label of a chart origin and cannot change its
lower/upper label. -/
public theorem constructedCentralOrigin_smul_coe
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (g : Multiplicative ParameterLattice) (upper : Bool) :
    letI := actualLocalCuspQuotientAction W
    ((g • constructedCentralOrigin W upper :
      LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
      inclusion (translateChartIndex (Multiplicative.toAdd g) (upper, 0)) 0 := by
  let C :=
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N constructedModel W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  let _ := actualLocalCuspQuotientAction W
  change (((C.toCuspActionData W.localWitness.fixedPoint).psiMap
    (Multiplicative.toAdd g) (constructedCentralOrigin W upper) :
      LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) = _
  rw [← C.psiMap_eq_generic, C.psiMap_coe]
  change carrierTorusActionFun _
    (carrierFanShearFun (Multiplicative.toAdd g) (inclusion (upper, 0) 0)) = _
  rw [carrierFanShearFun_inclusion, carrierTorusActionFun_inclusion]
  simp

/-- A chart origin as a point of the invariant central subspace. -/
public def constructedCentralOriginPoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (upper : Bool) :
    actualLocalCuspCentralSubMulAction W :=
  ⟨constructedCentralOrigin W upper, constructedCentralOrigin_height W upper⟩

/-- The corresponding point of the central-fibre orbit quotient. -/
public def constructedCentralOriginOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (upper : Bool) :
    ActualLocalCuspCentralOrbitQuotient W := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact Quotient.mk _ (constructedCentralOriginPoint W upper)

/-- The lower and upper chart origins determine two distinct points after taking the lattice
orbit quotient. -/
public theorem constructedCentralOriginOrbit_ne
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedCentralOriginOrbit W false ≠ constructedCentralOriginOrbit W true := by
  intro h
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hrel : MulAction.orbitRel (Multiplicative ParameterLattice) S
      (constructedCentralOriginPoint W false) (constructedCentralOriginPoint W true) :=
    @Quotient.exact S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
      (constructedCentralOriginPoint W false) (constructedCentralOriginPoint W true) h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  have hcarrier := congrArg
    (fun p : S ↦ ((p : LocalCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier)) hg
  change ((g • constructedCentralOrigin W true :
    LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
      inclusion (false, 0) 0 at hcarrier
  rw [constructedCentralOrigin_smul_coe] at hcarrier
  exact lowerOrigin_ne_upperOrigin 0
    (translateChartIndex (Multiplicative.toAdd g) (true, 0)).2 hcarrier.symm

/-- The characteristic map of either zero-cell. -/
public def constructedCentralZeroCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    PartialEquiv (Fin 0 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) where
  toFun := fun _ ↦ constructedCentralOriginOrbit W (![false, true] i)
  invFun := fun _ ↦ 0
  source := Metric.ball 0 1
  target := {constructedCentralOriginOrbit W (![false, true] i)}
  map_source' := by
    intro x hx
    simp
  map_target' := by
    intro x hx
    simp
  left_inv' := by
    intro x hx
    exact Subsingleton.elim _ _
  right_inv' := by
    intro x hx
    simpa only [Set.mem_singleton_iff] using hx.symm

public theorem constructedCentralZeroCell_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    (constructedCentralZeroCell W i).source = Metric.ball 0 1 :=
  rfl

public theorem constructedCentralZeroCell_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    ContinuousOn (constructedCentralZeroCell W i) (Metric.closedBall 0 1) :=
  continuous_const.continuousOn

public theorem constructedCentralZeroCell_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    ContinuousOn (constructedCentralZeroCell W i).symm
      (constructedCentralZeroCell W i).target :=
  continuous_const.continuousOn

/-- The interiors of the two zero-cells are disjoint in the actual orbit quotient. -/
public theorem constructedCentralZeroCell_pairwiseDisjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Set.univ : Set (Fin 2)).PairwiseDisjoint
      (fun i ↦ constructedCentralZeroCell W i '' Metric.ball 0 1) := by
  intro i hi j hj hij
  have hi0 : i = 0 ∨ i = 1 := by omega
  have hj0 : j = 0 ∨ j = 1 := by omega
  rcases hi0 with rfl | rfl <;> rcases hj0 with rfl | rfl
  · exact (hij rfl).elim
  · change Disjoint _ _
    rw [Set.disjoint_left]
    intro x
    rintro ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    exact constructedCentralOriginOrbit_ne W (hax.trans hbx.symm)
  · change Disjoint _ _
    rw [Set.disjoint_left]
    intro x
    rintro ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    exact constructedCentralOriginOrbit_ne W (hbx.trans hax.symm)
  · exact (hij rfl).elim

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end
