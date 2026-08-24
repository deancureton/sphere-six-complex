module

public import SphereSixComplex.Geometry.CuspAnalyticFillingCollar
public import SphereSixComplex.Geometry.PaperStarCollarPairProperness

/-!
# Properness of the actual cusp collar pair

This module supplies the compact middle bands and central-end escape estimate for the cusp
collar of the concrete four-piece star.
-/

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.CuspCollarPairProperness

open Set SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex Geometry
open ComplexTorus AnalyticTorusFamily TorusFamily GlobalTorusFamily
open CuspCombinatorics CuspFilling CuspLocalPhaseAction CuspPeriodExpansion
open CuspPuncturedCollarBridge CuspAnalyticFillingCollar
open StandardInfiniteA2ToricModel EllipticWholeFiberCompactCover
open EllipticLinearCollarGlobalDescent

noncomputable section

/-- The source orbifold coordinate descended to the actual punctured global family. -/
@[expose] public noncomputable def centralCuspCoordinate
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E} :
    PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) → ℂ := by
  let _ := regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
  exact Quotient.lift
    (fun q : RegularTotalSpace (assembledFuchsianPeriodFunctions E D) ↦
      E.sourceCoordinate.coordinate
        (regularTotalSpaceBase (assembledFuchsianPeriodFunctions E D) q).1) (by
      intro p q hpq
      change MulAction.orbitRel Delta _ p q at hpq
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq
      obtain ⟨g, rfl⟩ := hpq
      change E.sourceCoordinate.coordinate
          (regularTotalSpaceBase (assembledFuchsianPeriodFunctions E D)
            (regularFamilyDeckMap (assembledFuchsianPeriodFunctions E D) g q)).1 = _
      rw [regularTotalSpaceBase_familyDeckMap]
      exact E.sourceCoordinate.coordinate_invariant g _)

public theorem centralCuspCoordinate_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E} :
    Continuous (centralCuspCoordinate (E := E) (D := D)) := by
  let _ := regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
  unfold centralCuspCoordinate
  apply continuous_quot_lift
  exact E.sourceCoordinate.coordinate_holomorphic.continuous.comp
    (continuous_subtype_val.comp
      (regularTotalSpaceBase_continuous (assembledFuchsianPeriodFunctions E D)))

public theorem centralCuspCoordinate_additiveCover
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    centralCuspCoordinate (additiveCuspCoverToGlobal W p) =
      normalizedModularJCoordinate
        ((assembledFuchsianPeriodFunctions E D).tau (N.lift p.1.2)) := by
  let _ := regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
  rw [additiveCuspCoverToGlobal_eq_quotientProjections]
  change E.sourceCoordinate.coordinate (N.lift p.1.2) = _
  unfold normalizedModularJCoordinate
  rw [(assembledFuchsianPeriodFunctions E D).modular_equation]
  change E.sourceCoordinate.coordinate (N.lift p.1.2) =
    1728 * E.modularParameter.coordinate (N.lift p.1.2) / 1728
  rw [E.induced_coordinate]
  ring

/-- A closed fundamental strip in a normalized cusp middle band. -/
public def fundamentalCuspBand (a b : ℝ) : Set ℂ :=
  {s | a ≤ ‖cuspQ s‖ ∧ ‖cuspQ s‖ ≤ b ∧ 0 ≤ s.re ∧ s.re ≤ 1}

public theorem fundamentalCuspBand_isCompact
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : ℝ) (ha : 0 < a) (hb : b < W.localWitness.radius) :
    IsCompact (fundamentalCuspBand a b) := by
  let lower := -Real.log W.localWitness.radius / (2 * Real.pi)
  let upper := -Real.log a / (2 * Real.pi)
  let rectangle : Set ℂ := Complex.equivRealProdCLM.toHomeomorph ⁻¹'
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc lower upper)
  have hrectangle : IsCompact rectangle :=
    Complex.equivRealProdCLM.toHomeomorph.isProperMap.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  have hclosed : IsClosed (fundamentalCuspBand a b) := by
    have hq : Continuous (fun s : ℂ ↦ ‖cuspQ s‖) := by
      unfold cuspQ
      fun_prop
    simpa only [fundamentalCuspBand, Set.ofPred_and, inter_assoc] using
      ((isClosed_le continuous_const hq).inter
      (isClosed_le hq continuous_const)).inter
        ((isClosed_le continuous_const Complex.continuous_re).inter
          (isClosed_le Complex.continuous_re continuous_const))
  apply hrectangle.of_isClosed_subset hclosed
  intro s hs
  change s.re ∈ Set.Icc (0 : ℝ) 1 ∧ s.im ∈ Set.Icc lower upper
  refine ⟨⟨hs.2.2.1, hs.2.2.2⟩, ?_⟩
  have hqnorm := norm_cuspQ s
  have hupperlog : Real.log a ≤ -2 * Real.pi * s.im := by
    apply (Real.log_le_iff_le_exp ha).2
    simpa only [hqnorm] using hs.1
  have hlowerlog : -2 * Real.pi * s.im < Real.log W.localWitness.radius := by
    apply (Real.lt_log_iff_exp_lt W.localWitness.radius_pos).2
    rw [← hqnorm]
    exact hs.2.1.trans_lt hb
  dsimp only [lower, upper]
  have hden : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  constructor
  · apply (div_le_iff₀ hden).2
    nlinarith
  · apply (le_div_iff₀ hden).2
    nlinarith

public theorem fundamentalCuspBand_subset_halfPlane
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : ℝ) (hb : b < W.localWitness.radius) :
    fundamentalCuspBand a b ⊆ cuspHalfPlane N.height := by
  intro s hs
  apply mem_cuspHalfPlane_of_norm_cuspQ_lt W.localWitness.radius_le
  exact hs.2.1.trans_lt hb

/-- A normalized logarithmic fundamental band together with one real period cube. -/
public def cuspBandCube (a b : ℝ) : Set (ℂ × RealPeriods) :=
  fundamentalCuspBand a b ×ˢ Set.Icc (0 : RealPeriods) 1

public theorem cuspBandCube_fst_mem (a b : ℝ) (p : cuspBandCube a b) :
    p.1.1 ∈ fundamentalCuspBand a b := by
  simpa only [cuspBandCube, mem_prod] using p.property |>.1

public theorem cuspBandCube_q_le (a b : ℝ) (p : cuspBandCube a b) :
    ‖cuspQ p.1.1‖ ≤ b := by
  have hp := cuspBandCube_fst_mem a b p
  simpa only [fundamentalCuspBand] using hp |>.2.1

public theorem cuspBandCube_q_ge (a b : ℝ) (p : cuspBandCube a b) :
    a ≤ ‖cuspQ p.1.1‖ := by
  have hp := cuspBandCube_fst_mem a b p
  simpa only [fundamentalCuspBand] using hp |>.1

/-- The compact fundamental band and period cube mapped into the global cusp collar. -/
@[expose] public noncomputable def cuspBandCubeToGlobal
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : ℝ) (hb : b < W.localWitness.radius) :
    cuspBandCube a b →
      PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) :=
  fun p ↦ additiveCuspCoverToGlobal W
    ⟨(((fullRankDomain (parameterMap (assembledFuchsianPeriodFunctions E D)
          (N.lift p.1.1))).realEquiv p.1.2), p.1.1),
      (cuspBandCube_q_le a b p).trans_lt hb⟩

public theorem cuspBandCubeToGlobal_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : ℝ) (hb : b < W.localWitness.radius) :
    Continuous (cuspBandCubeToGlobal W a b hb) := by
  let F := assembledFuchsianPeriodFunctions E D
  let S := cuspBandCube a b
  have hlift : Continuous (fun p : S ↦ N.lift p.1.1) :=
    N.lift_holomorphic.continuousOn.comp_continuous
      (continuous_fst.comp continuous_subtype_val)
      (fun p ↦ fundamentalCuspBand_subset_halfPlane W a b hb p.2.1)
  have hpair : Continuous (fun p : S ↦ (N.lift p.1.1, p.1.2)) :=
    hlift.prodMk (continuous_snd.comp continuous_subtype_val)
  have hzeta : Continuous (fun p : S ↦
      (fullRankDomain (parameterMap F (N.lift p.1.1))).realEquiv p.1.2) :=
    by
      convert (periodRealLinear_parameterMap_continuous F).comp hpair using 1
      funext p
      rw [fullRankDomain.eq_def]
      rw [FullRank.ofSetupInequalities_realEquiv_apply]
      rfl
  unfold cuspBandCubeToGlobal
  apply (additiveCuspCoverToGlobal_continuous W).comp
  apply Continuous.subtype_mk
  exact hzeta.prodMk (continuous_fst.comp continuous_subtype_val)

public theorem cuspBandCube_isCompact
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : ℝ) (ha : 0 < a) (hb : b < W.localWitness.radius) :
    IsCompact (cuspBandCube a b) :=
  (fundamentalCuspBand_isCompact W a b ha hb).prod isCompact_Icc

public theorem cuspBandCubeToGlobal_range_isCompact
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : ℝ) (ha : 0 < a) (hb : b < W.localWitness.radius) :
    IsCompact (Set.range (cuspBandCubeToGlobal W a b hb)) := by
  let _ : CompactSpace (cuspBandCube a b) :=
    isCompact_iff_compactSpace.mp (cuspBandCube_isCompact W a b ha hb)
  exact isCompact_range (cuspBandCubeToGlobal_continuous W a b hb)

private theorem actualPuncturedGlobalCuspPoint_eq_of_family_projection_eq
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (zeta zeta' : ComplexTwoSpace)
    (h : projection (parameterMap (assembledFuchsianPeriodFunctions E D))
          (N.lift s, zeta) =
        projection (parameterMap (assembledFuchsianPeriodFunctions E D))
          (N.lift s, zeta')) :
    actualPuncturedGlobalCuspPoint W s hs hq zeta =
      actualPuncturedGlobalCuspPoint W s hs hq zeta' := by
  let F := assembledFuchsianPeriodFunctions E D
  apply congrArg (Quotient.mk _)
  apply regularFamilyInclusion_injective F
  unfold regularCuspFamilyPoint regularCuspBundlePoint
  rw [regularFamilyInclusion_mk, regularFamilyInclusion_mk]
  exact h

private theorem actualPuncturedGlobalCuspPoint_eq_period_cube
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (zeta : ComplexTwoSpace) :
    ∃ u ∈ Set.Icc (0 : RealPeriods) 1,
      actualPuncturedGlobalCuspPoint W s hs hq zeta =
        actualPuncturedGlobalCuspPoint W s hs hq
          ((fullRankDomain (parameterMap
            (assembledFuchsianPeriodFunctions E D) (N.lift s))).realEquiv u) := by
  let F := assembledFuchsianPeriodFunctions E D
  have hzeta : projection (parameterMap F) (N.lift s, zeta) ∈
      familyFiber F (N.lift s) := ⟨zeta, rfl⟩
  rw [familyFiber_eq_image_unitCube F (N.lift s)] at hzeta
  obtain ⟨u, hu, heq⟩ := hzeta
  refine ⟨u, hu, ?_⟩
  apply actualPuncturedGlobalCuspPoint_eq_of_family_projection_eq W s hs hq
  simpa only [familyFiberRealParam] using heq.symm

public theorem additiveCuspCoverToGlobal_mem_cuspBandCube_range
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : ℝ) (hb : b < W.localWitness.radius)
    (p : additiveCuspRadiusCover W.localWitness.radius)
    (ha : a ≤ ‖cuspQ p.1.2‖) (hbq : ‖cuspQ p.1.2‖ ≤ b) :
    additiveCuspCoverToGlobal W p ∈
      Set.range (cuspBandCubeToGlobal W a b hb) := by
  let n : ℤ := -⌊p.1.2.re⌋
  let s' : ℂ := p.1.2 + n
  have hqeq : cuspQ s' = cuspQ p.1.2 := by
    exact cuspQ_add_int p.1.2 n
  have hs' : s' ∈ cuspHalfPlane N.height :=
    cuspHalfPlane_add_int
      (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) n
  have hq' : ‖cuspQ s'‖ < W.localWitness.radius := by
    rw [hqeq]
    exact p.2
  have hs'band : s' ∈ fundamentalCuspBand a b := by
    change a ≤ ‖cuspQ s'‖ ∧ ‖cuspQ s'‖ ≤ b ∧
      0 ≤ s'.re ∧ s'.re ≤ 1
    rw [hqeq]
    refine ⟨ha, hbq, ?_, ?_⟩
    · dsimp only [s', n]
      simp only [Int.cast_neg]
      exact sub_nonneg.mpr (Int.floor_le p.1.2.re)
    · dsimp only [s', n]
      simp only [Int.cast_neg]
      exact le_of_lt (sub_lt_iff_lt_add.mpr (by
        exact add_comm (⌊p.1.2.re⌋ : ℝ) 1 ▸ Int.lt_floor_add_one p.1.2.re))
  obtain ⟨u, hu, hcube⟩ := actualPuncturedGlobalCuspPoint_eq_period_cube
    W s' hs' hq' p.1.1
  let q : cuspBandCube a b := ⟨(s', u), ⟨hs'band, hu⟩⟩
  refine ⟨q, ?_⟩
  have hshift := actualPuncturedGlobalCuspPoint_add_int W p.1.2
    (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2 p.1.1 n hs' hq'
  unfold cuspBandCubeToGlobal additiveCuspCoverToGlobal
  exact hcube.symm.trans hshift

/-- The additive cusp cover mapped into the actual punctured local quotient. -/
@[expose] public noncomputable def additiveCuspCoverToPuncturedQuotient
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    additiveCuspRadiusCover W.localWitness.radius → puncturedLocalCuspQuotient W :=
  fun p ↦ Quotient.mk _
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius (Quotient.mk _ p))

public theorem puncturedLocalCuspQuotientMap_additiveCover
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    puncturedLocalCuspQuotientMap W (additiveCuspCoverToPuncturedQuotient W p) =
      additiveCuspCoverToGlobal W p := by
  rw [additiveCuspCoverToPuncturedQuotient, puncturedLocalCuspQuotientMap_mk]
  dsimp only [puncturedLocalCuspPrequotientMap, Function.comp_apply]
  rw [Homeomorph.symm_apply_apply, additiveCuspQuotientToGlobal_mk]

/-- The radial coordinate on the punctured local quotient. -/
@[expose] public noncomputable def puncturedLocalCuspRadius
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    puncturedLocalCuspQuotient W → ℝ :=
  actualLocalCuspFillingRadius W ∘ puncturedLocalCuspToFilling W

public theorem puncturedLocalCuspRadius_additiveCover
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    puncturedLocalCuspRadius W (additiveCuspCoverToPuncturedQuotient W p) =
      ‖cuspQ p.1.2‖ := by
  unfold puncturedLocalCuspRadius additiveCuspCoverToPuncturedQuotient
  change actualLocalCuspFillingRadius W
    (puncturedLocalCuspToFilling W
      (Quotient.mk _
        (additiveToPuncturedLocalHomeomorph M W.localWitness.radius
          (Quotient.mk _ p)))) = _
  rw [puncturedLocalCuspToFilling_mk]
  unfold actualLocalCuspFillingRadius
  change ‖M.t ((additiveToPuncturedLocalHomeomorph M W.localWitness.radius
    (Quotient.mk _ p)).1)‖ = _
  rw [show ((additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      (Quotient.mk _ p)).1 : LocalCarrier M W.localWitness.radius) =
        localCuspExponentialPoint M W.localWitness.radius p.1.1 p.1.2
          (mem_ball_zero_iff.mpr p.2) from
    additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius p]
  rw [localCuspExponentialPoint_t]

private theorem puncturedLocalCuspQuotient_exists_additive
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (q : puncturedLocalCuspQuotient W) :
    ∃ p : additiveCuspRadiusCover W.localWitness.radius,
      q = additiveCuspCoverToPuncturedQuotient W p := by
  induction q using Quotient.inductionOn with
  | _ x =>
    let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
    obtain ⟨v, hv⟩ := e.surjective x
    induction v using Quotient.inductionOn with
    | _ p =>
      refine ⟨p, ?_⟩
      unfold additiveCuspCoverToPuncturedQuotient
      exact congrArg (Quotient.mk _) hv.symm

public theorem puncturedLocalCuspRadiusBand_image
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : ℝ) (hb : b < W.localWitness.radius) :
    puncturedLocalCuspQuotientMap W ''
        {q | a ≤ puncturedLocalCuspRadius W q ∧ puncturedLocalCuspRadius W q ≤ b} =
      Set.range (cuspBandCubeToGlobal W a b hb) := by
  apply Set.Subset.antisymm
  · rintro y ⟨q, hq, rfl⟩
    obtain ⟨p, rfl⟩ := puncturedLocalCuspQuotient_exists_additive W q
    change a ≤ puncturedLocalCuspRadius W
      (additiveCuspCoverToPuncturedQuotient W p) ∧
      puncturedLocalCuspRadius W
        (additiveCuspCoverToPuncturedQuotient W p) ≤ b at hq
    rw [puncturedLocalCuspRadius_additiveCover] at hq
    rw [puncturedLocalCuspQuotientMap_additiveCover]
    exact additiveCuspCoverToGlobal_mem_cuspBandCube_range W a b hb p hq.1 hq.2
  · rintro y ⟨q, rfl⟩
    let p : additiveCuspRadiusCover W.localWitness.radius :=
      ⟨(((fullRankDomain (parameterMap (assembledFuchsianPeriodFunctions E D)
          (N.lift q.1.1))).realEquiv q.1.2), q.1.1),
        (cuspBandCube_q_le a b q).trans_lt hb⟩
    refine ⟨additiveCuspCoverToPuncturedQuotient W p, ?_, ?_⟩
    · change a ≤ puncturedLocalCuspRadius W
        (additiveCuspCoverToPuncturedQuotient W p) ∧
        puncturedLocalCuspRadius W
          (additiveCuspCoverToPuncturedQuotient W p) ≤ b
      rw [puncturedLocalCuspRadius_additiveCover]
      exact ⟨cuspBandCube_q_ge a b q, cuspBandCube_q_le a b q⟩
    · exact puncturedLocalCuspQuotientMap_additiveCover W p

public theorem puncturedLocalCuspRadiusBand_isCompact
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : ℝ) (ha : 0 < a) (hb : b < W.localWitness.radius) :
    IsCompact {q | a ≤ puncturedLocalCuspRadius W q ∧
      puncturedLocalCuspRadius W q ≤ b} := by
  rw [(puncturedLocalCuspQuotientMap_isOpenEmbedding W).isEmbedding.isCompact_iff,
    puncturedLocalCuspRadiusBand_image W a b hb]
  exact cuspBandCubeToGlobal_range_isCompact W a b ha hb

public theorem modularCuspQ_lift
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (s : ℂ) (hs : s ∈ cuspHalfPlane N.height) :
    modularCuspQ ((assembledFuchsianPeriodFunctions E D).tau (N.lift s)) =
      cuspQ s := by
  unfold modularCuspQ Function.Periodic.qParam cuspQ
  rw [N.lift_tau s hs]
  congr 1
  norm_num

/-- Compact subsets of the global family stay a positive normalized cusp radius away from the
completed central end. -/
public theorem additiveCuspRadius_compact_central_lowerTrap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    ∀ K : Set (PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D)), IsCompact K →
      ∃ a : ℝ, 0 < a ∧ ∀ p : additiveCuspRadiusCover W.localWitness.radius,
        additiveCuspCoverToGlobal W p ∈ K → a ≤ ‖cuspQ p.1.2‖ := by
  intro K hK
  let J := Classical.choice establishedExactNormalizedModularJUniformization
  let Cusp := J.cusp
  have hcoordCompact : IsCompact
      ((fun y ↦ ‖centralCuspCoordinate (E := E) (D := D) y‖) '' K) :=
    hK.image (continuous_norm.comp centralCuspCoordinate_continuous)
  obtain ⟨C, hC⟩ := hcoordCompact.bddAbove
  let C₁ := max C 0 + 1
  have hC₁pos : 0 < C₁ := by dsimp only [C₁]; linarith [le_max_right C 0]
  have hC₁bound : ∀ y ∈ K,
      ‖centralCuspCoordinate (E := E) (D := D) y‖ ≤ C₁ := by
    intro y hy
    exact (hC ⟨_, hy, rfl⟩).trans (by
      dsimp only [C₁]
      linarith [le_max_left C 0])
  let rho := Cusp.cuspRadius / 2
  have hrho_pos : 0 < rho := div_pos Cusp.cuspRadius_pos (by norm_num)
  have hrho_lt : rho < Cusp.cuspRadius := by
    dsimp only [rho]
    linarith [Cusp.cuspRadius_pos]
  have hunitContinuous : ContinuousOn Cusp.cuspUnit (Metric.closedBall (0 : ℂ) rho) := by
    intro q hq
    exact (Cusp.cuspUnit_holomorphic q (by
      rw [mem_ball_zero_iff]
      exact (mem_closedBall_zero_iff.mp hq).trans_lt hrho_lt)).continuousAt.continuousWithinAt
  obtain ⟨A, hA⟩ := (ProperSpace.isCompact_closedBall (0 : ℂ) rho)
    |>.exists_bound_of_continuousOn hunitContinuous
  let A₁ := max A 0 + 1
  have hA₁pos : 0 < A₁ := by dsimp only [A₁]; linarith [le_max_right A 0]
  have hA₁bound : ∀ q ∈ Metric.closedBall (0 : ℂ) rho,
      ‖Cusp.cuspUnit q‖ ≤ A₁ := by
    intro q hq
    exact (hA q hq).trans (by
      dsimp only [A₁]
      linarith [le_max_left A 0])
  have hevent : ∀ᶠ z in upperHalfPlaneAtInfinity,
      (normalizedModularJCoordinate z)⁻¹ =
          modularCuspQ z * Cusp.cuspUnit (modularCuspQ z) ∧
        normalizedModularJCoordinate z ≠ 0 := by
    filter_upwards [Cusp.reciprocal_factorization,
      Cusp.coordinate_eventually_ne_zero] with z hfactor hne
    exact ⟨hfactor, hne⟩
  rw [upperHalfPlaneAtInfinity, Filter.eventually_comap] at hevent
  obtain ⟨H, hH⟩ := Filter.eventually_atTop.1 hevent
  let deltaHeight := Real.exp (-2 * Real.pi * H)
  have hdeltaHeight_pos : 0 < deltaHeight := Real.exp_pos _
  let delta := min deltaHeight rho
  have hdelta_pos : 0 < delta := lt_min hdeltaHeight_pos hrho_pos
  let inverseBound := (C₁ * A₁)⁻¹
  have hinverseBound_pos : 0 < inverseBound := inv_pos.mpr (mul_pos hC₁pos hA₁pos)
  refine ⟨min delta inverseBound, lt_min hdelta_pos hinverseBound_pos, ?_⟩
  intro p hpK
  let z := (assembledFuchsianPeriodFunctions E D).tau (N.lift p.1.2)
  have hs := additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p
  have hqz : modularCuspQ z = cuspQ p.1.2 := modularCuspQ_lift p.1.2 hs
  have hJbound : ‖normalizedModularJCoordinate z‖ ≤ C₁ := by
    rw [← centralCuspCoordinate_additiveCover W p]
    exact hC₁bound _ hpK
  by_cases hlarge : delta ≤ ‖cuspQ p.1.2‖
  · exact (min_le_left delta inverseBound).trans hlarge
  · have hqdelta : ‖cuspQ p.1.2‖ < delta := lt_of_not_ge hlarge
    have hqheight : ‖cuspQ p.1.2‖ < deltaHeight :=
      hqdelta.trans_le (min_le_left deltaHeight rho)
    have hheight : H ≤ z.im := by
      have hexp : Real.exp (-2 * Real.pi * p.1.2.im) <
          Real.exp (-2 * Real.pi * H) := by
        rw [← norm_cuspQ]
        exact hqheight
      have hlinear := Real.exp_lt_exp.mp hexp
      have hsim : z.im = p.1.2.im := by
        change (((assembledFuchsianPeriodFunctions E D).tau
          (N.lift p.1.2) : UpperHalfPlane) : ℂ).im = p.1.2.im
        rw [N.lift_tau p.1.2 hs]
      rw [hsim]
      nlinarith [Real.pi_pos]
    obtain ⟨hfactor, hJne⟩ := hH z.im hheight z rfl
    have hqball : modularCuspQ z ∈ Metric.closedBall (0 : ℂ) rho := by
      rw [mem_closedBall_zero_iff, hqz]
      exact hqdelta.le.trans (min_le_right deltaHeight rho)
    have hunitBound : ‖Cusp.cuspUnit (modularCuspQ z)‖ ≤ A₁ :=
      hA₁bound _ hqball
    have hunitBound' : ‖Cusp.cuspUnit (cuspQ p.1.2)‖ ≤ A₁ := by
      rw [← hqz]
      exact hunitBound
    have hproduct : 1 = normalizedModularJCoordinate z *
        modularCuspQ z * Cusp.cuspUnit (modularCuspQ z) := by
      calc
        1 = normalizedModularJCoordinate z *
            (normalizedModularJCoordinate z)⁻¹ :=
          (mul_inv_cancel₀ hJne).symm
        _ = normalizedModularJCoordinate z *
            (modularCuspQ z * Cusp.cuspUnit (modularCuspQ z)) := by rw [hfactor]
        _ = _ := by ring
    have hnormProduct := congrArg norm hproduct
    simp only [norm_one, norm_mul] at hnormProduct
    have hboundProduct : 1 ≤ C₁ * ‖cuspQ p.1.2‖ * A₁ := by
      calc
        1 = ‖normalizedModularJCoordinate z‖ * ‖cuspQ p.1.2‖ *
            ‖Cusp.cuspUnit (cuspQ p.1.2)‖ := by
          rw [hqz] at hnormProduct
          exact hnormProduct
        _ ≤ C₁ * ‖cuspQ p.1.2‖ * A₁ := by gcongr
    have hinvle : inverseBound ≤ ‖cuspQ p.1.2‖ := by
      dsimp only [inverseBound]
      rw [inv_le_iff_one_le_mul₀' (mul_pos hC₁pos hA₁pos)]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hboundProduct
    exact (min_le_right delta inverseBound).trans hinvle

public theorem puncturedLocalCuspRadius_compact_central_lowerTrap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    ∀ K : Set (PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D)), IsCompact K →
      ∃ a : ℝ, 0 < a ∧ ∀ q : puncturedLocalCuspQuotient W,
        puncturedLocalCuspQuotientMap W q ∈ K → a ≤ puncturedLocalCuspRadius W q := by
  intro K hK
  obtain ⟨a, ha, htrap⟩ := additiveCuspRadius_compact_central_lowerTrap W K hK
  refine ⟨a, ha, ?_⟩
  intro q hq
  obtain ⟨p, rfl⟩ := puncturedLocalCuspQuotient_exists_additive W q
  rw [puncturedLocalCuspQuotientMap_additiveCover] at hq
  rw [puncturedLocalCuspRadius_additiveCover]
  exact htrap p hq

end

end SphereSixComplex.Geometry.CuspCollarPairProperness

namespace SphereSixComplex.Geometry.PaperAnalyticData

open Set SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex Geometry
open CuspPuncturedCollarBridge
open CuspCollarPairProperness

noncomputable section

variable (P : PaperAnalyticData)

/-- Compact middle bands in the cusp collar of the concrete star. -/
public theorem cuspStarCollarRadiusBand_isCompact
    (a b : ℝ) (ha : 0 < a) (hb : b < P.starCuspWitness.localWitness.radius) :
    IsCompact {s : P.starCollarSourceType (0 : Fin 3) |
      a ≤ P.starCollarRadius (0 : Fin 3) s ∧
        P.starCollarRadius (0 : Fin 3) s ≤ b} := by
  change IsCompact {s : puncturedLocalCuspQuotient P.starCuspWitness |
    a ≤ puncturedLocalCuspRadius P.starCuspWitness s ∧
      puncturedLocalCuspRadius P.starCuspWitness s ≤ b}
  exact puncturedLocalCuspRadiusBand_isCompact P.starCuspWitness a b ha hb

/-- Compact subsets of the central family stay a positive radius away from the cusp filling's
central fibre. -/
public theorem cuspStarCollarRadius_compact_lowerTrap :
    ∀ K : Set P.CentralFamily, IsCompact K →
      ∃ a : ℝ, 0 < a ∧ ∀ s : P.starCollarSourceType (0 : Fin 3),
        P.starToCentral (0 : Fin 3) s ∈ K →
          a ≤ P.starCollarRadius (0 : Fin 3) s := by
  change ∀ K : Set P.CentralFamily, IsCompact K →
    ∃ a : ℝ, 0 < a ∧ ∀ s : puncturedLocalCuspQuotient P.starCuspWitness,
      puncturedLocalCuspQuotientMap P.starCuspWitness s ∈ K →
        a ≤ puncturedLocalCuspRadius P.starCuspWitness s
  exact puncturedLocalCuspRadius_compact_central_lowerTrap P.starCuspWitness

/-- The paired cusp collar map is proper. -/
public theorem cuspCollarPairMap_isProper :
    IsProperMap (P.openEmbeddingStarData.collarPairMap (0 : Fin 3)) := by
  let _ := P.starCentralCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ P.CentralFamily :=
    P.starCentral_isManifold
  let _ : LocallyCompactSpace P.CentralFamily :=
    Manifold.locallyCompact_of_finiteDimensional
      (modelWithCornersSelf ℂ ComplexModel)
  let _ := P.starFillingCharts (0 : Fin 3)
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (P.starFillingType (0 : Fin 3)) := P.starFilling_isManifold (0 : Fin 3)
  let _ : LocallyCompactSpace (P.starFillingType (0 : Fin 3)) :=
    Manifold.locallyCompact_of_finiteDimensional
      (modelWithCornersSelf ℂ ComplexModel)
  let _ : T2Space P.openEmbeddingStarData.central := by
    change T2Space P.CentralFamily
    exact P.centralFamily_t2
  let _ : T2Space (P.openEmbeddingStarData.filling (0 : Fin 3)) := by
    change T2Space (P.starFillingType (0 : Fin 3))
    exact P.starFilling_t2 (0 : Fin 3)
  let _ : LocallyCompactSpace P.openEmbeddingStarData.central := by
    change LocallyCompactSpace P.CentralFamily
    infer_instance
  let _ : LocallyCompactSpace
      (P.openEmbeddingStarData.filling (0 : Fin 3)) := by
    change LocallyCompactSpace (P.starFillingType (0 : Fin 3))
    infer_instance
  apply P.openEmbeddingStarData.collarPairMap_isProper_of_twoEndedRadialTraps
    (0 : Fin 3) (P.starCollarRadius (0 : Fin 3))
    P.starCuspWitness.localWitness.radius
  · exact P.cuspStarCollarRadiusBand_isCompact
  · exact P.cuspStarCollarRadius_compact_lowerTrap
  · exact P.starCollarRadius_compact_upperTrap_lt (0 : Fin 3)

end

end SphereSixComplex.Geometry.PaperAnalyticData
