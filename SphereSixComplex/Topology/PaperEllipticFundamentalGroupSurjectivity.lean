module

public import SphereSixComplex.Geometry.PaperAnalyticFillingPieces
public import SphereSixComplex.Geometry.GlobalTorusFiberFundamentalGroup

/-!
# Fundamental-group surjectivity for the elliptic collar inclusions
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace SphereSixComplex.Geometry

open Set Topology SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open TorusFamily AnalyticTorusFamily GlobalTorusFamily ComplexTorus
open EllipticLocalCoordinates EllipticCayleyHomeomorph
open EllipticVaryingFamilyQuotient EllipticPuncturedCollarGaugeHomeomorph
open EllipticWholeFiberCompactCover
open EllipticLinearCollarGlobalDescent
open EquivariantQuotientHomeomorph

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

private def continuousSetInclusion {X : Type*} [TopologicalSpace X]
    {S T : Set X} (hST : S ⊆ T) : C(S, T) :=
  ⟨fun x ↦ ⟨x.1, hST x.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩

public abbrev ComplexDiscPuncturedBall (r : ℝ) :=
  {w : ComplexUnitDisc // 0 < ‖(w : ℂ)‖ ∧ ‖(w : ℂ)‖ < r}

public noncomputable def complexDiscPuncturedBallRadialCover
    {r : ℝ} (hr1 : r < 1) :
    Set.Ioo (0 : ℝ) r × Metric.sphere (0 : ℂ) 1 →
      ComplexDiscPuncturedBall r := fun p => by
  have hu : ‖p.2.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2.2
  have hn : ‖p.1.1 • p.2.1‖ = p.1.1 := by
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos p.1.2.1]
  exact ⟨⟨p.1.1 • p.2.1, by rw [hn]; exact p.1.2.2.trans hr1⟩,
    ⟨by rw [hn]; exact p.1.2.1, by rw [hn]; exact p.1.2.2⟩⟩

public theorem complexDiscPuncturedBallRadialCover_continuous
    {r : ℝ} (hr1 : r < 1) :
    Continuous (complexDiscPuncturedBallRadialCover hr1) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

public theorem complexDiscPuncturedBallRadialCover_surjective
    {r : ℝ} (hr1 : r < 1) :
    Function.Surjective (complexDiscPuncturedBallRadialCover hr1) := by
  rintro ⟨⟨w, hw1⟩, hw0, hwr⟩
  have hn : ‖w‖ ≠ 0 := ne_of_gt hw0
  let s : Set.Ioo (0 : ℝ) r := ⟨‖w‖, hw0, hwr⟩
  let u : Metric.sphere (0 : ℂ) 1 := ⟨‖w‖⁻¹ • w, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hw0), inv_mul_cancel₀ hn]⟩
  refine ⟨(s, u), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change ‖w‖ • (‖w‖⁻¹ • w) = w
  rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

public theorem complexDiscBall_contractible {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ContractibleSpace (ComplexDiscBall r) := by
  let _ : ContractibleSpace (Metric.ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).contractibleSpace (Metric.nonempty_ball.mpr hr)
  exact (complexDiscBallHomeomorph hr1).contractibleSpace

public theorem complexDiscBall_pathConnected {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace (ComplexDiscBall r) := by
  have hball : IsPathConnected (Metric.ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).isPathConnected (Metric.nonempty_ball.mpr hr)
  let _ : PathConnectedSpace (Metric.ball (0 : ℂ) r) :=
    isPathConnected_iff_pathConnectedSpace.mp hball
  exact (complexDiscBallHomeomorph hr1).symm.surjective.pathConnectedSpace
    (complexDiscBallHomeomorph hr1).symm.continuous

public theorem complexDiscPuncturedBall_pathConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace (ComplexDiscPuncturedBall r) := by
  have hIoo : IsPathConnected (Set.Ioo (0 : ℝ) r) :=
    (convex_Ioo (𝕜 := ℝ) 0 r).isPathConnected
      ⟨r / 2, half_pos hr, half_lt_self hr⟩
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank]
    norm_num [Complex.finrank_real_complex]
  have hsphere : IsPathConnected (Metric.sphere (0 : ℂ) 1) :=
    isPathConnected_sphere hrank 0 (by norm_num)
  let _ : PathConnectedSpace (Set.Ioo (0 : ℝ) r) :=
    isPathConnected_iff_pathConnectedSpace.mp hIoo
  let _ : PathConnectedSpace (Metric.sphere (0 : ℂ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp hsphere
  exact (complexDiscPuncturedBallRadialCover_surjective hr1).pathConnectedSpace
    (complexDiscPuncturedBallRadialCover_continuous hr1)

public noncomputable def orderThreePuncturedCoverMap (r : ℝ) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace →
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier := fun p =>
  ⟨Quotient.mk _ (orderThreeCayleyHomeomorph.symm p.1.1, p.2), by
    change 0 < orderThreeFamilyRadius A.periods
        (Quotient.mk _ (orderThreeCayleyHomeomorph.symm p.1.1, p.2)) ∧
      orderThreeFamilyRadius A.periods
        (Quotient.mk _ (orderThreeCayleyHomeomorph.symm p.1.1, p.2)) < r
    simpa only [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_mk,
      orderThreeCayleyHomeomorph.apply_symm_apply] using p.1.2⟩

public noncomputable def orderFourPuncturedCoverMap (r : ℝ) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace →
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier := fun p =>
  ⟨Quotient.mk _ (orderFourCayleyHomeomorph.symm p.1.1, p.2), by
    change 0 < orderFourFamilyRadius A.periods
        (Quotient.mk _ (orderFourCayleyHomeomorph.symm p.1.1, p.2)) ∧
      orderFourFamilyRadius A.periods
        (Quotient.mk _ (orderFourCayleyHomeomorph.symm p.1.1, p.2)) < r
    simpa only [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_mk,
      orderFourCayleyHomeomorph.apply_symm_apply] using p.1.2⟩

public theorem orderThreePuncturedCoverMap_continuous (r : ℝ) :
    Continuous (A.orderThreePuncturedCoverMap r) := by
  unfold orderThreePuncturedCoverMap
  apply Continuous.subtype_mk
  have hfst : Continuous
      (fun p : ComplexDiscPuncturedBall r × ComplexTwoSpace =>
        (p.1 : ComplexUnitDisc)) :=
    continuous_subtype_val.comp continuous_fst
  exact continuous_quot_mk.comp
    ((orderThreeCayleyHomeomorph.symm.continuous.comp hfst).prodMk continuous_snd)

public theorem orderFourPuncturedCoverMap_continuous (r : ℝ) :
    Continuous (A.orderFourPuncturedCoverMap r) := by
  unfold orderFourPuncturedCoverMap
  apply Continuous.subtype_mk
  have hfst : Continuous
      (fun p : ComplexDiscPuncturedBall r × ComplexTwoSpace =>
        (p.1 : ComplexUnitDisc)) :=
    continuous_subtype_val.comp continuous_fst
  exact continuous_quot_mk.comp
    ((orderFourCayleyHomeomorph.symm.continuous.comp hfst).prodMk continuous_snd)

public theorem orderThreePuncturedCoverMap_surjective (r : ℝ) :
    Function.Surjective (A.orderThreePuncturedCoverMap r) := by
  rintro ⟨q, hq⟩
  change 0 < orderThreeFamilyRadius A.periods q ∧
    orderThreeFamilyRadius A.periods q < r at hq
  induction q using Quotient.inductionOn with
  | _ p =>
    refine ⟨(⟨orderThreeCayleyHomeomorph p.1, ?_⟩, p.2), ?_⟩
    · simpa [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_mk] using hq
    · apply Subtype.ext
      rw [orderThreePuncturedCoverMap.eq_def]
      change Quotient.mk _
        (orderThreeCayleyHomeomorph.symm (orderThreeCayleyHomeomorph p.1), p.2) =
          Quotient.mk _ p
      rw [orderThreeCayleyHomeomorph.symm_apply_apply]

public theorem orderFourPuncturedCoverMap_surjective (r : ℝ) :
    Function.Surjective (A.orderFourPuncturedCoverMap r) := by
  rintro ⟨q, hq⟩
  change 0 < orderFourFamilyRadius A.periods q ∧
    orderFourFamilyRadius A.periods q < r at hq
  induction q using Quotient.inductionOn with
  | _ p =>
    refine ⟨(⟨orderFourCayleyHomeomorph p.1, ?_⟩, p.2), ?_⟩
    · simpa [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_mk] using hq
    · apply Subtype.ext
      rw [orderFourPuncturedCoverMap.eq_def]
      change Quotient.mk _
        (orderFourCayleyHomeomorph.symm (orderFourCayleyHomeomorph p.1), p.2) =
          Quotient.mk _ p
      rw [orderFourCayleyHomeomorph.symm_apply_apply]

public theorem orderThreeFillingOpen_pathConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace (A.orderThreeFillingOpen r) := by
  let _ : PathConnectedSpace (ComplexDiscBall r) := complexDiscBall_pathConnected hr hr1
  exact (A.orderThreeFillingCoverMap_surjective r).pathConnectedSpace
    (A.orderThreeFillingCoverMap_continuous r)

public theorem orderFourFillingOpen_pathConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace (A.orderFourFillingOpen r) := by
  let _ : PathConnectedSpace (ComplexDiscBall r) := complexDiscBall_pathConnected hr hr1
  exact (A.orderFourFillingCoverMap_surjective r).pathConnectedSpace
    (A.orderFourFillingCoverMap_continuous r)

public theorem orderThreeAffinePuncturedCarrier_pathConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace ((orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) := by
  let _ : PathConnectedSpace (ComplexDiscPuncturedBall r) :=
    complexDiscPuncturedBall_pathConnected hr hr1
  exact (A.orderThreePuncturedCoverMap_surjective r).pathConnectedSpace
    (A.orderThreePuncturedCoverMap_continuous r)

public theorem orderFourAffinePuncturedCarrier_pathConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace ((orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) := by
  let _ : PathConnectedSpace (ComplexDiscPuncturedBall r) :=
    complexDiscPuncturedBall_pathConnected hr hr1
  exact (A.orderFourPuncturedCoverMap_surjective r).pathConnectedSpace
    (A.orderFourPuncturedCoverMap_continuous r)

public noncomputable def cayleyBallVectorPreimageHomeomorph
    (e : UpperHalfPlane ≃ₜ ComplexUnitDisc) (r : ℝ) :
    ComplexDiscBall r × ComplexTwoSpace ≃ₜ
      {p : UpperHalfPlane × ComplexTwoSpace | ‖(e p.1 : ComplexUnitDisc).1‖ < r} where
  toFun p := ⟨(e.symm p.1.1, p.2), by
    change ‖((e (e.symm p.1.1) : ComplexUnitDisc) : ℂ)‖ < r
    rw [e.apply_symm_apply]
    exact p.1.2⟩
  invFun p := (⟨e p.1.1, p.2⟩, p.1.2)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact e.apply_symm_apply p.1.1
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact e.symm_apply_apply p.1.1
    · rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (e.symm.continuous.comp
      (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
  continuous_invFun := by
    exact (Continuous.subtype_mk
      (e.continuous.comp (continuous_fst.comp continuous_subtype_val)) _).prodMk
        (continuous_snd.comp continuous_subtype_val)

public noncomputable def cayleyPuncturedBallVectorPreimageHomeomorph
    (e : UpperHalfPlane ≃ₜ ComplexUnitDisc) (r : ℝ) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace ≃ₜ
      {p : UpperHalfPlane × ComplexTwoSpace |
        0 < ‖(e p.1 : ComplexUnitDisc).1‖ ∧ ‖(e p.1 : ComplexUnitDisc).1‖ < r} where
  toFun p := ⟨(e.symm p.1.1, p.2), by
    change 0 < ‖((e (e.symm p.1.1) : ComplexUnitDisc) : ℂ)‖ ∧
      ‖((e (e.symm p.1.1) : ComplexUnitDisc) : ℂ)‖ < r
    rw [e.apply_symm_apply]
    exact p.1.2⟩
  invFun p := (⟨e p.1.1, p.2⟩, p.1.2)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact e.apply_symm_apply p.1.1
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact e.symm_apply_apply p.1.1
    · rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (e.symm.continuous.comp
      (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
  continuous_invFun := by
    exact (Continuous.subtype_mk
      (e.continuous.comp (continuous_fst.comp continuous_subtype_val)) _).prodMk
        (continuous_snd.comp continuous_subtype_val)

public theorem orderThreeFillingCoverPreimage_eq (r : ℝ) :
    {p : UpperHalfPlane × ComplexTwoSpace |
        ‖(orderThreeCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r} =
      (projection (parameterMap A.periods)) ⁻¹'
        (A.orderThreeFillingOpen r : Set (TotalSpace (parameterMap A.periods))) := by
  ext p
  change ‖(orderThreeCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r ↔
    orderThreeFamilyRadius A.periods (Quotient.mk _ p) < r
  rw [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_mk]

public theorem orderFourFillingCoverPreimage_eq (r : ℝ) :
    {p : UpperHalfPlane × ComplexTwoSpace |
        ‖(orderFourCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r} =
      (projection (parameterMap A.periods)) ⁻¹'
        (A.orderFourFillingOpen r : Set (TotalSpace (parameterMap A.periods))) := by
  ext p
  change ‖(orderFourCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r ↔
    orderFourFamilyRadius A.periods (Quotient.mk _ p) < r
  rw [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_mk]

public theorem orderThreePuncturedCoverPreimage_eq (r : ℝ) :
    {p : UpperHalfPlane × ComplexTwoSpace |
        0 < ‖(orderThreeCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ ∧
          ‖(orderThreeCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r} =
      (projection (parameterMap A.periods)) ⁻¹'
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier := by
  ext p
  change (0 < ‖(orderThreeCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ ∧
      ‖(orderThreeCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r) ↔
    (0 < orderThreeFamilyRadius A.periods (Quotient.mk _ p) ∧
      orderThreeFamilyRadius A.periods (Quotient.mk _ p) < r)
  rw [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_mk]

public theorem orderFourPuncturedCoverPreimage_eq (r : ℝ) :
    {p : UpperHalfPlane × ComplexTwoSpace |
        0 < ‖(orderFourCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ ∧
          ‖(orderFourCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r} =
      (projection (parameterMap A.periods)) ⁻¹'
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier := by
  ext p
  change (0 < ‖(orderFourCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ ∧
      ‖(orderFourCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r) ↔
    (0 < orderFourFamilyRadius A.periods (Quotient.mk _ p) ∧
      orderFourFamilyRadius A.periods (Quotient.mk _ p) < r)
  rw [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_mk]

public noncomputable def orderThreeFillingCoverPreimageHomeomorph (r : ℝ) :
    ComplexDiscBall r × ComplexTwoSpace ≃ₜ
      (projection (parameterMap A.periods)) ⁻¹'
        (A.orderThreeFillingOpen r : Set (TotalSpace (parameterMap A.periods))) :=
  (cayleyBallVectorPreimageHomeomorph orderThreeCayleyHomeomorph r).trans
    (Homeomorph.setCongr (A.orderThreeFillingCoverPreimage_eq r))

public noncomputable def orderFourFillingCoverPreimageHomeomorph (r : ℝ) :
    ComplexDiscBall r × ComplexTwoSpace ≃ₜ
      (projection (parameterMap A.periods)) ⁻¹'
        (A.orderFourFillingOpen r : Set (TotalSpace (parameterMap A.periods))) :=
  (cayleyBallVectorPreimageHomeomorph orderFourCayleyHomeomorph r).trans
    (Homeomorph.setCongr (A.orderFourFillingCoverPreimage_eq r))

public noncomputable def orderThreePuncturedCoverPreimageHomeomorph (r : ℝ) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace ≃ₜ
      (projection (parameterMap A.periods)) ⁻¹'
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier :=
  (cayleyPuncturedBallVectorPreimageHomeomorph orderThreeCayleyHomeomorph r).trans
    (Homeomorph.setCongr (A.orderThreePuncturedCoverPreimage_eq r))

public noncomputable def orderFourPuncturedCoverPreimageHomeomorph (r : ℝ) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace ≃ₜ
      (projection (parameterMap A.periods)) ⁻¹'
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier :=
  (cayleyPuncturedBallVectorPreimageHomeomorph orderFourCayleyHomeomorph r).trans
    (Homeomorph.setCongr (A.orderFourPuncturedCoverPreimage_eq r))

public theorem familyProjection_isQuotientCoveringMap :
    letI := familyMulAction (parameterMap A.periods)
    IsQuotientCoveringMap (projection (parameterMap A.periods))
      (FamilyPeriodGroup (parameterMap A.periods)) := by
  let _ := familyMulAction (parameterMap A.periods)
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    (fun a ↦ (periodSection_contMDiff A.periods a 0).continuous)
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

public theorem orderThreePuncturedSourceToFillingSource_fundamentalGroup_surjective
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (x : UpperHalfPlane × ComplexTwoSpace)
    (hx : projection (parameterMap A.periods) x ∈
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨A.orderThreePuncturedSourceToFillingSource r,
          (A.orderThreePuncturedSourceToFillingSource_isOpenEmbedding r).continuous⟩ :
          C((orderThreeAffinePuncturedCarrier A.periods
              A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier,
            A.orderThreeFillingOpen r))
        (⟨projection (parameterMap A.periods) x, hx⟩ :
          (orderThreeAffinePuncturedCarrier A.periods
            A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier)) := by
  let f := projection (parameterMap A.periods)
  let W : Set (TotalSpace (parameterMap A.periods)) :=
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier
  let V : Set (TotalSpace (parameterMap A.periods)) := A.orderThreeFillingOpen r
  have hWV : W ⊆ V := A.orderThreePuncturedCarrier_subset_filling r
  let _ := familyMulAction (parameterMap A.periods)
  let hf : IsQuotientCoveringMap f (FamilyPeriodGroup (parameterMap A.periods)) :=
    A.familyProjection_isQuotientCoveringMap
  let _ : PathConnectedSpace (ComplexDiscPuncturedBall r) :=
    complexDiscPuncturedBall_pathConnected hr hr1
  let _ : PathConnectedSpace (f ⁻¹' W) :=
    (A.orderThreePuncturedCoverPreimageHomeomorph r).surjective.pathConnectedSpace
      (A.orderThreePuncturedCoverPreimageHomeomorph r).continuous
  let _ : ContractibleSpace (ComplexDiscBall r) := complexDiscBall_contractible hr hr1
  let _ : SimplyConnectedSpace (ComplexDiscBall r × ComplexTwoSpace) := inferInstance
  let _ : SimplyConnectedSpace (f ⁻¹' V) :=
    (A.orderThreeFillingCoverPreimageHomeomorph r).toHomotopyEquiv
      |>.simplyConnectedSpace_iff.mp inferInstance
  have hsource : Function.Surjective
      (FundamentalGroup.map
        (continuousSetInclusion (fun _ hz ↦ hWV hz) : C(f ⁻¹' W, f ⁻¹' V))
        (⟨x, hx⟩ : f ⁻¹' W)) := by
    intro q
    exact ⟨1, Subsingleton.elim _ q⟩
  have h := quotientCovering_restrict_inclusion_fundamentalGroup_surjective
    hf hWV x hx hsource
  let actual : C(W, V) :=
    ⟨A.orderThreePuncturedSourceToFillingSource r,
      (A.orderThreePuncturedSourceToFillingSource_isOpenEmbedding r).continuous⟩
  have hactual : actual = continuousSetInclusion hWV := by
    ext z
    rfl
  change Function.Surjective
    (FundamentalGroup.map actual
      (⟨projection (parameterMap A.periods) x, hx⟩ : W))
  rw [hactual]
  exact h

public theorem orderFourPuncturedSourceToFillingSource_fundamentalGroup_surjective
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (x : UpperHalfPlane × ComplexTwoSpace)
    (hx : projection (parameterMap A.periods) x ∈
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨A.orderFourPuncturedSourceToFillingSource r,
          (A.orderFourPuncturedSourceToFillingSource_isOpenEmbedding r).continuous⟩ :
          C((orderFourAffinePuncturedCarrier A.periods
              A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier,
            A.orderFourFillingOpen r))
        (⟨projection (parameterMap A.periods) x, hx⟩ :
          (orderFourAffinePuncturedCarrier A.periods
            A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier)) := by
  let f := projection (parameterMap A.periods)
  let W : Set (TotalSpace (parameterMap A.periods)) :=
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier
  let V : Set (TotalSpace (parameterMap A.periods)) := A.orderFourFillingOpen r
  have hWV : W ⊆ V := A.orderFourPuncturedCarrier_subset_filling r
  let _ := familyMulAction (parameterMap A.periods)
  let hf : IsQuotientCoveringMap f (FamilyPeriodGroup (parameterMap A.periods)) :=
    A.familyProjection_isQuotientCoveringMap
  let _ : PathConnectedSpace (ComplexDiscPuncturedBall r) :=
    complexDiscPuncturedBall_pathConnected hr hr1
  let _ : PathConnectedSpace (f ⁻¹' W) :=
    (A.orderFourPuncturedCoverPreimageHomeomorph r).surjective.pathConnectedSpace
      (A.orderFourPuncturedCoverPreimageHomeomorph r).continuous
  let _ : ContractibleSpace (ComplexDiscBall r) := complexDiscBall_contractible hr hr1
  let _ : SimplyConnectedSpace (ComplexDiscBall r × ComplexTwoSpace) := inferInstance
  let _ : SimplyConnectedSpace (f ⁻¹' V) :=
    (A.orderFourFillingCoverPreimageHomeomorph r).toHomotopyEquiv
      |>.simplyConnectedSpace_iff.mp inferInstance
  have hsource : Function.Surjective
      (FundamentalGroup.map
        (continuousSetInclusion (fun _ hz ↦ hWV hz) : C(f ⁻¹' W, f ⁻¹' V))
        (⟨x, hx⟩ : f ⁻¹' W)) := by
    intro q
    exact ⟨1, Subsingleton.elim _ q⟩
  have h := quotientCovering_restrict_inclusion_fundamentalGroup_surjective
    hf hWV x hx hsource
  let actual : C(W, V) :=
    ⟨A.orderFourPuncturedSourceToFillingSource r,
      (A.orderFourPuncturedSourceToFillingSource_isOpenEmbedding r).continuous⟩
  have hactual : actual = continuousSetInclusion hWV := by
    ext z
    rfl
  change Function.Surjective
    (FundamentalGroup.map actual
      (⟨projection (parameterMap A.periods) x, hx⟩ : W))
  rw [hactual]
  exact h

public theorem orderThreePuncturedCollarToFilling_fundamentalGroup_surjective
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (x : UpperHalfPlane × ComplexTwoSpace)
    (hx : projection (parameterMap A.periods) x ∈
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨A.orderThreePuncturedCollarToFilling r,
          A.orderThreePuncturedCollarToFilling_continuous r⟩ :
          C(Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
              (orderThreeAffinePuncturedCarrier A.periods
                A.modular.modularParameter.toTriangleUniformization_sourceAction r)),
            A.OrderThreeVaryingFilling r))
        (Quotient.mk _
          (⟨projection (parameterMap A.periods) x, hx⟩ :
            (orderThreeAffinePuncturedCarrier A.periods
              A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier))) := by
  let S := orderThreeAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let q : S.carrier := ⟨projection (parameterMap A.periods) x, hx⟩
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  let _ : LocallyCompactSpace (TotalSpace (parameterMap A.periods)) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : LocallyCompactSpace S.carrier := S.isOpen_carrier.locallyCompactSpace
  let _ : T2Space S.carrier := by infer_instance
  let _ : LocallyCompactSpace (A.orderThreeFillingOpen r) :=
    (A.orderThreeFillingOpen r).2.locallyCompactSpace
  let _ : T2Space (A.orderThreeFillingOpen r) := by infer_instance
  let hcontinuous :
      letI := orderThreeAffineFamilyAction A.periods
      ContinuousConstSMul (FiniteCyclic 3) (TotalSpace (parameterMap A.periods)) := by
    let _ := orderThreeAffineFamilyAction A.periods
    exact ⟨fun g ↦ (orderThreeAffineFamilyRepresentation_contMDiff A.periods
      A.totalSpace_projection_isLocalDiffeomorph g).continuous⟩
  let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods) S
  let _ : IsCancelSMul (FiniteCyclic 3) S.carrier :=
    restrictedIsCancelSMul (orderThreeAffineFamilyAction A.periods) S
      (orderThreeAffineFamilyAction_free A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let _ : ContinuousConstSMul (FiniteCyclic 3) S.carrier :=
    restrictedContinuousConstSMul (orderThreeAffineFamilyAction A.periods) S
      hcontinuous
  let _ := A.orderThreeFillingAction r
  let _ : IsCancelSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  let hfS : IsQuotientCoveringMap
      (Quotient.mk (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods) S))
      (FiniteCyclic 3) := by
    exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  let hfV : IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel (FiniteCyclic 3) (A.orderThreeFillingOpen r)))
      (FiniteCyclic 3) := by
    exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  let sourceMap : C(S.carrier, A.orderThreeFillingOpen r) :=
    ⟨A.orderThreePuncturedSourceToFillingSource r,
      (A.orderThreePuncturedSourceToFillingSource_isOpenEmbedding r).continuous⟩
  let targetMap : C(Quotient (restrictedOrbitRel
      (orderThreeAffineFamilyAction A.periods) S), A.OrderThreeVaryingFilling r) :=
    ⟨A.orderThreePuncturedCollarToFilling r,
      A.orderThreePuncturedCollarToFilling_continuous r⟩
  have hcomm (y : S.carrier) :
      targetMap (Quotient.mk _ y) = Quotient.mk _ (sourceMap y) := by
    exact A.orderThreePuncturedCollarToFilling_mk r y
  have hequiv (g : FiniteCyclic 3) (y : S.carrier) :
      sourceMap (g • y) = g • sourceMap y := by
    apply Subtype.ext
    rfl
  let _ : PathConnectedSpace S.carrier :=
    A.orderThreeAffinePuncturedCarrier_pathConnected hr hr1
  let _ : PathConnectedSpace (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingOpen_pathConnected hr hr1
  have hsource : Function.Surjective (FundamentalGroup.map sourceMap q) := by
    simpa [sourceMap, q, S] using
      A.orderThreePuncturedSourceToFillingSource_fundamentalGroup_surjective
        hr hr1 x hx
  have hmapOfEq := quotientCovering_equivariant_map_fundamentalGroup_surjective
    hfS hfV sourceMap targetMap hcomm hequiv q hsource
  exact fundamentalGroup_map_surjective_of_mapOfEq_surjective
    targetMap (Quotient.mk _ q) (Quotient.mk _ (sourceMap q)) (hcomm q) hmapOfEq

public theorem orderFourPuncturedCollarToFilling_fundamentalGroup_surjective
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (x : UpperHalfPlane × ComplexTwoSpace)
    (hx : projection (parameterMap A.periods) x ∈
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨A.orderFourPuncturedCollarToFilling r,
          A.orderFourPuncturedCollarToFilling_continuous r⟩ :
          C(Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
              (orderFourAffinePuncturedCarrier A.periods
                A.modular.modularParameter.toTriangleUniformization_sourceAction r)),
            A.OrderFourVaryingFilling r))
        (Quotient.mk _
          (⟨projection (parameterMap A.periods) x, hx⟩ :
            (orderFourAffinePuncturedCarrier A.periods
              A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier))) := by
  let S := orderFourAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let q : S.carrier := ⟨projection (parameterMap A.periods) x, hx⟩
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  let _ : LocallyCompactSpace (TotalSpace (parameterMap A.periods)) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : LocallyCompactSpace S.carrier := S.isOpen_carrier.locallyCompactSpace
  let _ : T2Space S.carrier := by infer_instance
  let _ : LocallyCompactSpace (A.orderFourFillingOpen r) :=
    (A.orderFourFillingOpen r).2.locallyCompactSpace
  let _ : T2Space (A.orderFourFillingOpen r) := by infer_instance
  let hcontinuous :
      letI := orderFourAffineFamilyAction A.periods
      ContinuousConstSMul (FiniteCyclic 4) (TotalSpace (parameterMap A.periods)) := by
    let _ := orderFourAffineFamilyAction A.periods
    exact ⟨fun g ↦ (orderFourAffineFamilyRepresentation_contMDiff A.periods
      A.totalSpace_projection_isLocalDiffeomorph g).continuous⟩
  let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods) S
  let _ : IsCancelSMul (FiniteCyclic 4) S.carrier :=
    restrictedIsCancelSMul (orderFourAffineFamilyAction A.periods) S
      (orderFourAffineFamilyAction_free A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let _ : ContinuousConstSMul (FiniteCyclic 4) S.carrier :=
    restrictedContinuousConstSMul (orderFourAffineFamilyAction A.periods) S
      hcontinuous
  let _ := A.orderFourFillingAction r
  let _ : IsCancelSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  let hfS : IsQuotientCoveringMap
      (Quotient.mk (restrictedOrbitRel (orderFourAffineFamilyAction A.periods) S))
      (FiniteCyclic 4) := by
    exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  let hfV : IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel (FiniteCyclic 4) (A.orderFourFillingOpen r)))
      (FiniteCyclic 4) := by
    exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  let sourceMap : C(S.carrier, A.orderFourFillingOpen r) :=
    ⟨A.orderFourPuncturedSourceToFillingSource r,
      (A.orderFourPuncturedSourceToFillingSource_isOpenEmbedding r).continuous⟩
  let targetMap : C(Quotient (restrictedOrbitRel
      (orderFourAffineFamilyAction A.periods) S), A.OrderFourVaryingFilling r) :=
    ⟨A.orderFourPuncturedCollarToFilling r,
      A.orderFourPuncturedCollarToFilling_continuous r⟩
  have hcomm (y : S.carrier) :
      targetMap (Quotient.mk _ y) = Quotient.mk _ (sourceMap y) := by
    exact A.orderFourPuncturedCollarToFilling_mk r y
  have hequiv (g : FiniteCyclic 4) (y : S.carrier) :
      sourceMap (g • y) = g • sourceMap y := by
    apply Subtype.ext
    rfl
  let _ : PathConnectedSpace S.carrier :=
    A.orderFourAffinePuncturedCarrier_pathConnected hr hr1
  let _ : PathConnectedSpace (A.orderFourFillingOpen r) :=
    A.orderFourFillingOpen_pathConnected hr hr1
  have hsource : Function.Surjective (FundamentalGroup.map sourceMap q) := by
    simpa [sourceMap, q, S] using
      A.orderFourPuncturedSourceToFillingSource_fundamentalGroup_surjective
        hr hr1 x hx
  have hmapOfEq := quotientCovering_equivariant_map_fundamentalGroup_surjective
    hfS hfV sourceMap targetMap hcomm hequiv q hsource
  exact fundamentalGroup_map_surjective_of_mapOfEq_surjective
    targetMap (Quotient.mk _ q) (Quotient.mk _ (sourceMap q)) (hcomm q) hmapOfEq

public theorem orderThreePuncturedCollarToFilling_fundamentalGroup_surjective_at
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (q : Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r))) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨A.orderThreePuncturedCollarToFilling r,
          A.orderThreePuncturedCollarToFilling_continuous r⟩ :
          C(Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
              (orderThreeAffinePuncturedCarrier A.periods
                A.modular.modularParameter.toTriangleUniformization_sourceAction r)),
            A.OrderThreeVaryingFilling r)) q) := by
  induction q using Quotient.inductionOn with
  | _ y =>
      rcases y with ⟨z, hz⟩
      induction z using Quotient.inductionOn with
      | _ x =>
          exact A.orderThreePuncturedCollarToFilling_fundamentalGroup_surjective
            hr hr1 x hz

public theorem orderFourPuncturedCollarToFilling_fundamentalGroup_surjective_at
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (q : Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r))) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨A.orderFourPuncturedCollarToFilling r,
          A.orderFourPuncturedCollarToFilling_continuous r⟩ :
          C(Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
              (orderFourAffinePuncturedCarrier A.periods
                A.modular.modularParameter.toTriangleUniformization_sourceAction r)),
            A.OrderFourVaryingFilling r)) q) := by
  induction q using Quotient.inductionOn with
  | _ y =>
      rcases y with ⟨z, hz⟩
      induction z using Quotient.inductionOn with
      | _ x =>
          exact A.orderFourPuncturedCollarToFilling_fundamentalGroup_surjective
            hr hr1 x hz

end PaperAnalyticData

end SphereSixComplex.Geometry
