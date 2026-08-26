module

public import SphereSixComplex.Geometry.CuspPuncturedCollarBridge
public import SphereSixComplex.Geometry.QuotientDeckFundamentalGroup
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Identity-period loops in the local toric cusp filling

The identity block of the normalized period lattice translates the additive cusp coordinate by
an integral vector.  Its exponential therefore gives a loop in the dense torus.  This file lifts
that loop to the base cone chart, observes that the cusp region there is star-convex, and proves
that the projected loop is null-homotopic in the actual phase-corrected local toric filling.
-/

@[expose] public section

open Topology

noncomputable section

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open StandardInfiniteA2ToricModel
open StandardInfiniteA2ToricModel.Model
open CuspLocalPhaseAction
open CuspFilling
open CuspPeriodExpansion

/-- The part of the base cone chart cut out by the local cusp radius. -/
public def baseConeCuspRegion (r : ℝ) : Set ComplexModel :=
  {z | ‖z 0 * z 1 * z 2‖ < r}

/-- Radial contraction toward the origin stays in the base-cone cusp region. -/
public theorem baseConeCuspRegion_starConvex (r : ℝ) :
    StarConvex ℝ (0 : ComplexModel) (baseConeCuspRegion r) := by
  intro z hz a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have hb3 : b ^ 3 ≤ 1 := pow_le_one₀ hb hb1
  change ‖(a • (0 : ComplexModel) + b • z) 0 *
      (a • (0 : ComplexModel) + b • z) 1 *
      (a • (0 : ComplexModel) + b • z) 2‖ < r
  simp only [smul_zero, zero_add, PiLp.smul_apply, Complex.real_smul]
  rw [show ((b : ℂ) * z 0) * ((b : ℂ) * z 1) * ((b : ℂ) * z 2) =
      (b : ℂ) ^ 3 * (z 0 * z 1 * z 2) by ring]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  exact (mul_le_of_le_one_left (norm_nonneg _) hb3).trans_lt hz

/-- The base-cone cusp region is contractible whenever its radius is positive. -/
public theorem baseConeCuspRegion_contractible (r : ℝ) (hr : 0 < r) :
    ContractibleSpace (baseConeCuspRegion r) := by
  apply (baseConeCuspRegion_starConvex r).contractibleSpace
  exact ⟨0, by simpa [baseConeCuspRegion] using hr⟩

/-- Inverse base-cone coordinates, restricted to the local toric cusp carrier. -/
public def baseConeCuspRegionToLocalCarrier (M : Model) (r : ℝ) :
    baseConeCuspRegion r → LocalCarrier M r := fun z => by
  have hzt : (z : ComplexModel) ∈ (M.toricChart false 0).target := by
    rw [M.toricChart_target]
    exact Set.mem_univ _
  refine ⟨(M.toricChart false 0).invFun z, ?_⟩
  rw [mem_cuspNeighborhood_iff, mem_ball_zero_iff]
  rw [M.toricChart_t false 0 ((M.toricChart false 0).invFun z)
    ((M.toricChart false 0).map_target hzt)]
  have hinv : (M.toricChart false 0).invFun z =
      (M.toricChart false 0).toPartialEquiv.symm z :=
    congrFun (M.toricChart false 0).toPartialEquiv.invFun_as_coe z
  rw [hinv, (M.toricChart false 0).toPartialEquiv.right_inv hzt]
  exact z.property

public theorem baseConeCuspRegionToLocalCarrier_continuous (M : Model) (r : ℝ) :
    Continuous (baseConeCuspRegionToLocalCarrier M r) := by
  unfold baseConeCuspRegionToLocalCarrier
  apply Continuous.subtype_mk
  apply (M.toricChart false 0).toOpenPartialHomeomorph.continuousOn_invFun.comp_continuous
    continuous_subtype_val
  intro z
  change (z : ComplexModel) ∈ (M.toricChart false 0).target
  rw [M.toricChart_target]
  exact Set.mem_univ _

public theorem additiveCuspRadiusCover_cuspQ_norm_lt {r : ℝ}
    (p : additiveCuspRadiusCover r) : ‖cuspQ p.1.2‖ < r := by
  exact p.2

/-- The integral identity-period translation, exponentiated to a loop in the local dense torus. -/
public def localIdentityPeriodLoop (M : Model) {r : ℝ}
    (p : additiveCuspRadiusCover r) (n : ParameterLattice) :
    Path
      (localCuspExponentialPoint M r p.1.1 p.1.2
        (mem_ball_zero_iff.mpr (additiveCuspRadiusCover_cuspQ_norm_lt p)))
      (localCuspExponentialPoint M r p.1.1 p.1.2
        (mem_ball_zero_iff.mpr (additiveCuspRadiusCover_cuspQ_norm_lt p))) where
  toFun t := localCuspExponentialPoint M r
    (p.1.1 + (t : ℝ) • (fun i => (n i : ℂ))) p.1.2
      (mem_ball_zero_iff.mpr (additiveCuspRadiusCover_cuspQ_norm_lt p))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply M.torus_openEmbedding.continuous.comp
    have hexp : Continuous denseCuspExponentialCover :=
      denseCuspExponentialCover_isQuotientMap.continuous
    change Continuous (denseCuspExponentialCover ∘ fun t : unitInterval =>
      (p.1.1 + (t : ℝ) • (fun i => (n i : ℂ)), p.1.2))
    apply hexp.comp
    exact (continuous_const.add
      (continuous_subtype_val.smul continuous_const)).prodMk continuous_const
  source' := by
    apply Subtype.ext
    simp [localCuspExponentialPoint]
  target' := by
    apply Subtype.ext
    rw [localCuspExponentialPoint_coe, localCuspExponentialPoint_coe]
    apply congrArg M.torusEmbedding
    simpa using denseCuspExponential_add_int p.1.1 p.1.2 n

/-- The initial point of the identity-period loop in base-cone coordinates. -/
public def localIdentityPeriodChartPoint (M : Model) {r : ℝ}
    (p : additiveCuspRadiusCover r) : baseConeCuspRegion r := ⟨
  M.toricChart false 0
    (localCuspExponentialPoint M r p.1.1 p.1.2
      (mem_ball_zero_iff.mpr (additiveCuspRadiusCover_cuspQ_norm_lt p))),
  by
    change ‖(M.toricChart false 0
      (localCuspExponentialPoint M r p.1.1 p.1.2
        (mem_ball_zero_iff.mpr (additiveCuspRadiusCover_cuspQ_norm_lt p)))) 0 *
      (M.toricChart false 0
        (localCuspExponentialPoint M r p.1.1 p.1.2
          (mem_ball_zero_iff.mpr (additiveCuspRadiusCover_cuspQ_norm_lt p)))) 1 *
      (M.toricChart false 0
        (localCuspExponentialPoint M r p.1.1 p.1.2
          (mem_ball_zero_iff.mpr (additiveCuspRadiusCover_cuspQ_norm_lt p)))) 2‖ < r
    have hx : (localCuspExponentialPoint M r p.1.1 p.1.2
        (mem_ball_zero_iff.mpr (additiveCuspRadiusCover_cuspQ_norm_lt p)) : M.Carrier) ∈
        (M.toricChart false 0).source := by
      rw [localCuspExponentialPoint_coe]
      exact M.torus_mem_toricChart false 0 _
    rw [← M.toricChart_t false 0 _ hx]
    exact mem_ball_zero_iff.mp
      (localCuspExponentialPoint M r p.1.1 p.1.2
        (mem_ball_zero_iff.mpr p.2)).property⟩

/-- The identity-period loop lifted through the base cone chart. -/
public def localIdentityPeriodChartLoop (M : Model) {r : ℝ}
    (p : additiveCuspRadiusCover r) (n : ParameterLattice) :
    Path (localIdentityPeriodChartPoint M p) (localIdentityPeriodChartPoint M p) := by
  let L := localIdentityPeriodLoop M p n
  exact
    { toFun := fun t => ⟨M.toricChart false 0 (L t), by
          change ‖(M.toricChart false 0 (L t)) 0 *
            (M.toricChart false 0 (L t)) 1 *
            (M.toricChart false 0 (L t)) 2‖ < r
          rw [← M.toricChart_t false 0 _ (by
            change M.torusEmbedding
                (denseCuspExponential
                  (p.1.1 + (t : ℝ) • (fun i => (n i : ℂ))) p.1.2) ∈
              (M.toricChart false 0).source
            exact M.torus_mem_toricChart false 0 _)]
          exact mem_ball_zero_iff.mp (L t).property⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply (M.toricChart false 0).toOpenPartialHomeomorph.continuousOn_toFun.comp_continuous
          (continuous_subtype_val.comp L.continuous)
        intro t
        change M.torusEmbedding
            (denseCuspExponential
              (p.1.1 + (t : ℝ) • (fun i => (n i : ℂ))) p.1.2) ∈
          (M.toricChart false 0).source
        exact M.torus_mem_toricChart false 0 _
      source' := by
        apply Subtype.ext
        exact congrArg (fun x : LocalCarrier M r =>
          M.toricChart false 0 (x : M.Carrier)) L.source
      target' := by
        apply Subtype.ext
        exact congrArg (fun x : LocalCarrier M r =>
          M.toricChart false 0 (x : M.Carrier)) L.target }

public theorem baseConeCuspRegionToLocalCarrier_localIdentityPeriodChartLoop
    (M : Model) {r : ℝ} (p : additiveCuspRadiusCover r) (n : ParameterLattice)
    (t : unitInterval) :
    baseConeCuspRegionToLocalCarrier M r (localIdentityPeriodChartLoop M p n t) =
      localIdentityPeriodLoop M p n t := by
  let L := localIdentityPeriodLoop M p n
  have hx : (L t : M.Carrier) ∈ (M.toricChart false 0).source := by
    change M.torusEmbedding
        (denseCuspExponential
          (p.1.1 + (t : ℝ) • (fun i => (n i : ℂ))) p.1.2) ∈
      (M.toricChart false 0).source
    exact M.torus_mem_toricChart false 0 _
  apply Subtype.ext
  change (M.toricChart false 0).invFun (M.toricChart false 0 (L t)) = (L t : M.Carrier)
  have hinv : (M.toricChart false 0).invFun (M.toricChart false 0 (L t)) =
      (M.toricChart false 0).toPartialEquiv.symm (M.toricChart false 0 (L t)) :=
    congrFun (M.toricChart false 0).toPartialEquiv.invFun_as_coe
      (M.toricChart false 0 (L t))
  rw [hinv]
  exact (M.toricChart false 0).toPartialEquiv.left_inv hx

/-- The base-cone region mapped into the actual phase-corrected local cusp filling. -/
public noncomputable def baseConeCuspRegionToFilling
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    C(baseConeCuspRegion W.localWitness.radius, actualLocalCuspFilling W) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  exact ⟨fun z => Quotient.mk _ (baseConeCuspRegionToLocalCarrier M _ z),
    continuous_quot_mk.comp (baseConeCuspRegionToLocalCarrier_continuous M _)⟩

/-- The quotient point represented by the initial local exponential point. -/
public noncomputable def localIdentityPeriodFillingBasepoint
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) : actualLocalCuspFilling W := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  exact Quotient.mk _
    (localCuspExponentialPoint M W.localWitness.radius p.1.1 p.1.2
      (mem_ball_zero_iff.mpr (additiveCuspRadiusCover_cuspQ_norm_lt p)))

/-- The chart lift projected into the actual local filling. -/
public noncomputable def localIdentityPeriodFillingLoop
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) (n : ParameterLattice) :
    Path (baseConeCuspRegionToFilling W (localIdentityPeriodChartPoint M p))
      (baseConeCuspRegionToFilling W (localIdentityPeriodChartPoint M p)) := by
  let K := localIdentityPeriodChartLoop M p n
  exact K.map (baseConeCuspRegionToFilling W).continuous

public theorem localIdentityPeriodFillingLoop_apply
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) (n : ParameterLattice)
    (t : unitInterval) :
    localIdentityPeriodFillingLoop W p n t =
      Quotient.mk _ (localIdentityPeriodLoop M p n t) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  exact congrArg (fun x : LocalCarrier M W.localWitness.radius =>
      (Quotient.mk _ x : actualLocalCuspFilling W))
    (baseConeCuspRegionToLocalCarrier_localIdentityPeriodChartLoop M p n t)

public theorem localIdentityPeriodFillingLoop_class_eq_one
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) (n : ParameterLattice) :
    pathLoopClass (localIdentityPeriodFillingLoop W p n) = 1 := by
  let _ : ContractibleSpace (baseConeCuspRegion W.localWitness.radius) :=
    baseConeCuspRegion_contractible W.localWitness.radius W.localWitness.radius_pos
  let K := localIdentityPeriodChartLoop M p n
  have hK : pathLoopClass K = 1 := Subsingleton.elim _ _
  let F := baseConeCuspRegionToFilling W
  have hmap := congrArg (FundamentalGroup.map F (localIdentityPeriodChartPoint M p)) hK
  exact hmap

public theorem localIdentityPeriodFillingLoop_basepoint_eq
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) (n : ParameterLattice) :
    baseConeCuspRegionToFilling W (localIdentityPeriodChartPoint M p) =
      localIdentityPeriodFillingBasepoint W p := by
  let L := localIdentityPeriodFillingLoop W p n
  exact L.source.symm.trans (by
    simpa [localIdentityPeriodFillingBasepoint] using
      localIdentityPeriodFillingLoop_apply W p n (0 : unitInterval))

/-- The projected identity-period loop, based at its original toric quotient point. -/
public noncomputable def projectedLocalIdentityPeriodLoop
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) (n : ParameterLattice) :
    Path (localIdentityPeriodFillingBasepoint W p)
      (localIdentityPeriodFillingBasepoint W p) :=
  (localIdentityPeriodFillingLoop W p n).cast
    (localIdentityPeriodFillingLoop_basepoint_eq W p n).symm
    (localIdentityPeriodFillingLoop_basepoint_eq W p n).symm

/-- Pointwise, the chart construction is exactly the quotient of the exponential period loop. -/
public theorem projectedLocalIdentityPeriodLoop_apply
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) (n : ParameterLattice)
    (t : unitInterval) :
    projectedLocalIdentityPeriodLoop W p n t =
      Quotient.mk _ (localIdentityPeriodLoop M p n t) := by
  change localIdentityPeriodFillingLoop W p n t = _
  exact localIdentityPeriodFillingLoop_apply W p n t

/-- Every integral identity-period loop vanishes in the actual local toric cusp filling. -/
public theorem projectedLocalIdentityPeriodLoop_class_eq_one
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) (n : ParameterLattice) :
    pathLoopClass (projectedLocalIdentityPeriodLoop W p n) = 1 := by
  let h := localIdentityPeriodFillingLoop_basepoint_eq W p n
  change pathLoopClass ((localIdentityPeriodFillingLoop W p n).cast h.symm h.symm) = 1
  rw [pathLoopClass_cast_eq_mapOfEq_id _ h,
    localIdentityPeriodFillingLoop_class_eq_one]
  exact map_one _

/-- The normalized additive representative and its punctured local quotient have exactly the
same image in the global cusp collar. -/
public theorem puncturedLocalCuspQuotientMap_additiveCuspRadiusToQuotient
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    puncturedLocalCuspQuotientMap W
        (additiveCuspRadiusToPuncturedLocalCuspQuotient W p) =
      additiveCuspCoverToGlobal W p := by
  rw [additiveCuspRadiusToPuncturedLocalCuspQuotient,
    puncturedLocalCuspQuotientMap_mk]
  dsimp only [puncturedLocalCuspPrequotientMap, Function.comp_apply]
  rw [Homeomorph.symm_apply_apply, additiveCuspQuotientToGlobal_mk]

/-- The normalized additive representative enters the full local filling at the quotient point
used to base its identity-period loops. -/
public theorem puncturedLocalCuspToFilling_additiveCuspRadiusToQuotient
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    puncturedLocalCuspToFilling W
        (additiveCuspRadiusToPuncturedLocalCuspQuotient W p) =
      localIdentityPeriodFillingBasepoint W p := by
  rw [additiveCuspRadiusToPuncturedLocalCuspQuotient]
  change Quotient.mk _
      ((additiveToPuncturedLocalHomeomorph M W.localWitness.radius
        (Quotient.mk _ p)).1) = _
  rw [additiveToPuncturedLocalHomeomorph_mk]
  rfl

/-! ## The filled base-circle cusp loop -/

/-- Adding a real number changes only the phase of the exponential cusp coordinate. -/
public theorem norm_cuspQ_add_real (s : ℂ) (a : ℝ) :
    ‖cuspQ (s + (a : ℂ))‖ = ‖cuspQ s‖ := by
  rw [norm_cuspQ, norm_cuspQ]
  simp

/-- Keep the additive fibre coordinate fixed and traverse one positive turn in the logarithmic
cusp coordinate.  Its exponential is a loop in the punctured local toric carrier. -/
public def localCuspBaseLoop (M : Model) {r : ℝ}
    (p : additiveCuspRadiusCover r) :
    Path
      (localCuspExponentialPoint M r p.1.1 p.1.2
        (mem_ball_zero_iff.mpr (additiveCuspRadiusCover_cuspQ_norm_lt p)))
      (localCuspExponentialPoint M r p.1.1 p.1.2
        (mem_ball_zero_iff.mpr (additiveCuspRadiusCover_cuspQ_norm_lt p))) where
  toFun t := localCuspExponentialPoint M r p.1.1
    (p.1.2 + (t : ℝ)) (mem_ball_zero_iff.mpr (by
      rw [norm_cuspQ_add_real]
      exact p.2))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply M.torus_openEmbedding.continuous.comp
    have hexp : Continuous denseCuspExponentialCover :=
      denseCuspExponentialCover_isQuotientMap.continuous
    change Continuous (denseCuspExponentialCover ∘ fun t : unitInterval =>
      (p.1.1, p.1.2 + (t : ℝ)))
    fun_prop
  source' := by
    apply Subtype.ext
    simp [localCuspExponentialPoint]
  target' := by
    apply Subtype.ext
    rw [localCuspExponentialPoint_coe, localCuspExponentialPoint_coe]
    apply congrArg M.torusEmbedding
    change denseCuspExponentialCover (p.1.1, p.1.2 + (1 : ℂ)) =
      denseCuspExponentialCover (p.1.1, p.1.2)
    apply (denseCuspExponentialCover_eq_iff _ _).2
    exact ⟨0, 0, 1, by simp, by simp, by push_cast; ring⟩

/-- Lift the positive logarithmic cusp loop through the base-cone chart. -/
public def localCuspBaseChartLoop (M : Model) {r : ℝ}
    (p : additiveCuspRadiusCover r) :
    Path (localIdentityPeriodChartPoint M p) (localIdentityPeriodChartPoint M p) := by
  let L := localCuspBaseLoop M p
  exact
    { toFun := fun t => ⟨M.toricChart false 0 (L t), by
          change ‖(M.toricChart false 0 (L t)) 0 *
            (M.toricChart false 0 (L t)) 1 *
            (M.toricChart false 0 (L t)) 2‖ < r
          rw [← M.toricChart_t false 0 _ (by
            change M.torusEmbedding
                (denseCuspExponential p.1.1 (p.1.2 + (t : ℝ))) ∈
              (M.toricChart false 0).source
            exact M.torus_mem_toricChart false 0 _)]
          exact mem_ball_zero_iff.mp (L t).property⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply (M.toricChart false 0).toOpenPartialHomeomorph.continuousOn_toFun.comp_continuous
          (continuous_subtype_val.comp L.continuous)
        intro t
        change M.torusEmbedding
            (denseCuspExponential p.1.1 (p.1.2 + (t : ℝ))) ∈
          (M.toricChart false 0).source
        exact M.torus_mem_toricChart false 0 _
      source' := by
        apply Subtype.ext
        exact congrArg (fun x : LocalCarrier M r =>
          M.toricChart false 0 (x : M.Carrier)) L.source
      target' := by
        apply Subtype.ext
        exact congrArg (fun x : LocalCarrier M r =>
          M.toricChart false 0 (x : M.Carrier)) L.target }

public theorem baseConeCuspRegionToLocalCarrier_localCuspBaseChartLoop
    (M : Model) {r : ℝ} (p : additiveCuspRadiusCover r) (t : unitInterval) :
    baseConeCuspRegionToLocalCarrier M r (localCuspBaseChartLoop M p t) =
      localCuspBaseLoop M p t := by
  let L := localCuspBaseLoop M p
  have hx : (L t : M.Carrier) ∈ (M.toricChart false 0).source := by
    change M.torusEmbedding
        (denseCuspExponential p.1.1 (p.1.2 + (t : ℝ))) ∈
      (M.toricChart false 0).source
    exact M.torus_mem_toricChart false 0 _
  apply Subtype.ext
  change (M.toricChart false 0).invFun (M.toricChart false 0 (L t)) = (L t : M.Carrier)
  have hinv : (M.toricChart false 0).invFun (M.toricChart false 0 (L t)) =
      (M.toricChart false 0).toPartialEquiv.symm (M.toricChart false 0 (L t)) :=
    congrFun (M.toricChart false 0).toPartialEquiv.invFun_as_coe
      (M.toricChart false 0 (L t))
  rw [hinv]
  exact (M.toricChart false 0).toPartialEquiv.left_inv hx

/-- The lifted base circle included into the full phase-corrected cusp filling. -/
public noncomputable def localCuspBaseFillingLoop
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    Path (baseConeCuspRegionToFilling W (localIdentityPeriodChartPoint M p))
      (baseConeCuspRegionToFilling W (localIdentityPeriodChartPoint M p)) :=
  (localCuspBaseChartLoop M p).map (baseConeCuspRegionToFilling W).continuous

public theorem localCuspBaseFillingLoop_apply
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) (t : unitInterval) :
    localCuspBaseFillingLoop W p t =
      Quotient.mk _ (localCuspBaseLoop M p t) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  exact congrArg (fun x : LocalCarrier M W.localWitness.radius =>
      (Quotient.mk _ x : actualLocalCuspFilling W))
    (baseConeCuspRegionToLocalCarrier_localCuspBaseChartLoop M p t)

public theorem localCuspBaseFillingLoop_class_eq_one
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    pathLoopClass (localCuspBaseFillingLoop W p) = 1 := by
  let _ : ContractibleSpace (baseConeCuspRegion W.localWitness.radius) :=
    baseConeCuspRegion_contractible W.localWitness.radius W.localWitness.radius_pos
  let K := localCuspBaseChartLoop M p
  have hK : pathLoopClass K = 1 := Subsingleton.elim _ _
  let F := baseConeCuspRegionToFilling W
  exact congrArg (FundamentalGroup.map F (localIdentityPeriodChartPoint M p)) hK

public theorem localCuspBaseFillingLoop_basepoint_eq
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    baseConeCuspRegionToFilling W (localIdentityPeriodChartPoint M p) =
      localIdentityPeriodFillingBasepoint W p := by
  let L := localCuspBaseFillingLoop W p
  exact L.source.symm.trans (by
    simpa [localIdentityPeriodFillingBasepoint] using
      localCuspBaseFillingLoop_apply W p (0 : unitInterval))

/-- The filled base-circle loop, displayed at the same local quotient basepoint used for fibre
period loops. -/
public noncomputable def projectedLocalCuspBaseLoop
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    Path (localIdentityPeriodFillingBasepoint W p)
      (localIdentityPeriodFillingBasepoint W p) :=
  (localCuspBaseFillingLoop W p).cast
    (localCuspBaseFillingLoop_basepoint_eq W p).symm
    (localCuspBaseFillingLoop_basepoint_eq W p).symm

public theorem projectedLocalCuspBaseLoop_apply
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) (t : unitInterval) :
    projectedLocalCuspBaseLoop W p t =
      Quotient.mk _ (localCuspBaseLoop M p t) := by
  change localCuspBaseFillingLoop W p t = _
  exact localCuspBaseFillingLoop_apply W p t

/-- The positive logarithmic base circle is null in the full toric cusp filling. -/
public theorem projectedLocalCuspBaseLoop_class_eq_one
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    pathLoopClass (projectedLocalCuspBaseLoop W p) = 1 := by
  let h := localCuspBaseFillingLoop_basepoint_eq W p
  change pathLoopClass ((localCuspBaseFillingLoop W p).cast h.symm h.symm) = 1
  rw [pathLoopClass_cast_eq_mapOfEq_id _ h,
    localCuspBaseFillingLoop_class_eq_one]
  exact map_one _

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
