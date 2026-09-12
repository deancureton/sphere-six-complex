module
public import SphereSixComplex.Paper.Topology.CuspFiniteFiberCoordinateTori
public import SphereSixComplex.Paper.Topology.LocalToricCircleSweep
public import SphereSixComplex.Prerequisites.Topology.UnitCircleExponential
public import SphereSixComplex.Paper.Topology.PaperCuspActualAffineFillingCoverSquare

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.CuspCollar
open ComplexTorus SphereSixComplex.Periods InfiniteA2Toric CuspLocalPhaseAction CuspFilling
open CuspPeriodExpansion CuspToricPhaseAction CuspPhaseEstimates
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

public theorem localPhaseActionEquiv_psiMap
    {r : ℝ} (C : LocalHolomorphicPhaseCoefficients M r) (c : Phase)
    (lambda : ParameterLattice) (p : localCarrier M r) :
    localPhaseActionEquiv M r c (C.psiMap lambda p) =
      C.psiMap lambda (localPhaseActionEquiv M r c p) := by
  apply Subtype.ext
  rw [localPhaseActionEquiv_coe, LocalHolomorphicPhaseCoefficients.psiMap_coe, LocalHolomorphicPhaseCoefficients.psiMap_coe, localPhaseActionEquiv_coe,
    ToricModel.phaseAction_preserves_t, ToricModel.fanShear_phase_commute]
  rw [← Equiv.Perm.mul_apply, ← map_mul, mul_comm, map_mul, Equiv.Perm.mul_apply]

public def cuspPeriodPhaseCircle (i : Fin 2) : C(UnitAddCircle,Phase) where
  toFun z := fun j ↦ if j = i then CircleExponential.toUnits z else 1
  continuous_toFun := by
    apply continuous_pi
    intro j
    by_cases h : j = i
    · simp only [h, ↓reduceIte]
      exact CircleExponential.toUnits.continuous
    · simp only [h, ↓reduceIte]
      exact continuous_const

public def localCuspPeriodCircle (W : ActualPuncturedCuspCollarWitness N M) (i : Fin 2) :
    C(UnitAddCircle × localCarrier M W.localWitness.radius,
      localCarrier M W.localWitness.radius) :=
  localHeightPreservingCircleAction M W.localWitness.radius
    ⟨fun z ↦ phaseEmbedding (cuspPeriodPhaseCircle i z), by
      apply continuous_pi
      intro j
      fin_cases j
      · change Continuous (fun z ↦ cuspPeriodPhaseCircle i z 0)
        exact (continuous_apply 0).comp (cuspPeriodPhaseCircle i).continuous
      · change Continuous (fun z ↦ cuspPeriodPhaseCircle i z 1)
        exact (continuous_apply 1).comp (cuspPeriodPhaseCircle i).continuous
      · exact continuous_const⟩ (fun _ ↦ rfl)

public theorem localCuspPeriodCircle_equivariant
    (W : ActualPuncturedCuspCollarWitness N M) (i : Fin 2) :
    letI := actualLocalCuspQuotientAction W
    ∀ (z : UnitAddCircle) (g : Multiplicative ParameterLattice)
      (p : localCarrier M W.localWitness.radius),
      localCuspPeriodCircle W i (z,g • p) = g • localCuspPeriodCircle W i (z,p) := by
  let _ := actualLocalCuspQuotientAction W
  intro z g p
  let C := NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
    N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  change localPhaseActionEquiv M W.localWitness.radius (cuspPeriodPhaseCircle i z)
    (C.toCuspActionData.psiMap (Multiplicative.toAdd g) p) =
    C.toCuspActionData.psiMap (Multiplicative.toAdd g)
      (localPhaseActionEquiv M W.localWitness.radius (cuspPeriodPhaseCircle i z) p)
  rw [← C.psiMap_eq_generic, ← C.psiMap_eq_generic]
  exact localPhaseActionEquiv_psiMap C _ _ _

public def cuspFillingPeriodCircle (W : ActualPuncturedCuspCollarWitness N M) (i : Fin 2) :
    C(UnitAddCircle × ActualLocalCuspFilling W,ActualLocalCuspFilling W) := by
  let _ := actualLocalCuspQuotientAction W
  refine ⟨fun p ↦ Quotient.map (fun q ↦ localCuspPeriodCircle W i (p.1,q)) ?_ p.2, ?_⟩
  · intro a b h
    rcases (MulAction.mem_orbit_iff).mp h with ⟨g,hg⟩
    exact (MulAction.mem_orbit_iff).mpr ⟨g,
      (localCuspPeriodCircle_equivariant W i _ g b).symm.trans
        (congrArg (fun q ↦ localCuspPeriodCircle W i (_,q)) hg)⟩
  · apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_quotient_mk'.comp (localCuspPeriodCircle W i).continuous

public theorem cuspFillingPeriodCircle_mk (W : ActualPuncturedCuspCollarWitness N M)
    (i : Fin 2) (z : UnitAddCircle) (p : localCarrier M W.localWitness.radius) :
    letI := actualLocalCuspQuotientAction W
    cuspFillingPeriodCircle W i (z,Quotient.mk _ p) =
      Quotient.mk _ (localCuspPeriodCircle W i (z,p)) := rfl

public theorem cuspPeriodPhaseCircle_dense (i : Fin 2) (t : ℝ)
    (s : ℂ) (v : ComplexTwoSpace) :
    phaseEmbedding (cuspPeriodPhaseCircle i (t : UnitAddCircle)) * denseCuspExponential v s =
      denseCuspExponential (v + Pi.single i (t : ℂ)) s := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [phaseEmbedding, cuspPeriodPhaseCircle, denseCuspExponential]
  all_goals
    rw [CircleExponential.toUnits_real]
    change Complex.exp _ * Complex.exp _ = Complex.exp _
    rw [← Complex.exp_add]
    congr 1
    ring

public theorem localCuspPeriodCircle_fillingLift
    (W : ActualPuncturedCuspCollarWitness N M) (i : Fin 2) (t : ℝ)
    (s : ℂ) (hs : ‖cuspQ s‖ < W.localWitness.radius) (v : ComplexTwoSpace) :
    localCuspPeriodCircle W i ((t : UnitAddCircle),additiveCuspFillingLift W ⟨(v,s),hs⟩) =
      additiveCuspFillingLift W ⟨(v + Pi.single i (t : ℂ),s),hs⟩ := by
  change _ = (additiveToPuncturedLocalHomeomorph _ _ (Quotient.mk _ _)).1
  rw [additiveToPuncturedLocalHomeomorph_mk]
  apply Subtype.ext
  change M.torusAction (phaseEmbedding (cuspPeriodPhaseCircle i (t : UnitAddCircle)))
    ((additiveToPuncturedLocalHomeomorph _ _ (Quotient.mk _ _)).1.1) = _
  rw [additiveToPuncturedLocalHomeomorph_mk]
  change M.torusAction (phaseEmbedding (cuspPeriodPhaseCircle i (t : UnitAddCircle)))
    (M.torusEmbedding (denseCuspExponential v s)) =
    M.torusEmbedding (denseCuspExponential (v + Pi.single i (t : ℂ)) s)
  rw [M.torusAction_torus]
  apply congrArg M.torusEmbedding
  exact cuspPeriodPhaseCircle_dense i t s v

public theorem cuspFillingPeriodCircle_periodPoint
    (W : ActualPuncturedCuspCollarWitness N M) (i : Fin 2) (t : ℝ)
    (s : ℂ) (hs : ‖cuspQ s‖ < W.localWitness.radius) (v : ComplexTwoSpace) :
    cuspFillingPeriodCircle W i ((t : UnitAddCircle),
      puncturedLocalCuspToFilling W (actualCuspCollarPeriodPoint W hs v)) =
      puncturedLocalCuspToFilling W
        (actualCuspCollarPeriodPoint W hs (v + Pi.single i (t : ℂ))) := by
  change cuspFillingPeriodCircle W i ((t : UnitAddCircle),
      puncturedLocalCuspToFilling W (additiveCuspBoundaryProjection W ⟨(v,s),hs⟩)) =
    puncturedLocalCuspToFilling W (additiveCuspBoundaryProjection W ⟨(_,s),hs⟩)
  rw [additiveCuspCoverSquare_commutes, additiveCuspCoverSquare_commutes]
  change cuspFillingPeriodCircle W i (_,Quotient.mk _ _) = Quotient.mk _ _
  rw [cuspFillingPeriodCircle_mk, localCuspPeriodCircle_fillingLift]

end SphereSixComplex.Geometry.CuspCollar
