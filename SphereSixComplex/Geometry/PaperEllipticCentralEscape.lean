module

public import SphereSixComplex.Geometry.PaperStarCollarPairProperness

/-!
# Elliptic collars escape compact subsets at the central end

The quotient projection of a free properly discontinuous action admits compact sets of local
representatives over compact subsets.  Combined with proper discontinuity on the upper
half-plane, this gives a positive Cayley-radius lower bound along either elliptic collar.
-/

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace SphereSixComplex

noncomputable section

/-- A compact subset of the target of a surjective local homeomorphism has a compact set of
local representatives. -/
public theorem IsLocalHomeomorph.exists_compact_source_cover
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) (hsurj : Function.Surjective f)
    {K : Set Y} (hK : IsCompact K) :
    ∃ L : Set X, IsCompact L ∧ K ⊆ f '' L := by
  choose x hx using fun y : K ↦ hsurj y
  let e (y : K) : OpenPartialHomeomorph Y X := hf.localInverseAt (x y)
  have hy_source (y : K) : (y : Y) ∈ (e y).source := by
    rw [← hx y]
    exact hf.apply_self_mem_localInverseAt_source
  choose C hCcompact hyC hCsource using fun y : K ↦
    exists_compact_subset (e y).open_source (hy_source y)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun y : K ↦ interior (C y)) (fun _ ↦ isOpen_interior) (by
      intro y hy
      exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hyC ⟨y, hy⟩⟩)
  let L : Set X := ⋃ y ∈ t, (e y) '' C y
  refine ⟨L, ?_, ?_⟩
  · exact t.isCompact_biUnion fun y _ ↦
      (hCcompact y).image_of_continuousOn ((e y).continuousOn.mono (hCsource y))
  · intro y hy
    obtain ⟨z, hzt, hyz⟩ := Set.mem_iUnion₂.mp (ht hy)
    refine ⟨e z y, ?_, ?_⟩
    · exact Set.mem_iUnion₂.mpr ⟨z, hzt,
        ⟨y, interior_subset hyz, rfl⟩⟩
    · exact hf.apply_localInverseAt_of_mem ((hCsource z) (interior_subset hyz))

/-- Proper discontinuity makes a positive continuous function uniformly positive on all
translates of a compact set that meet a second compact set. -/
public theorem properlyDiscontinuous_compact_translate_positiveLowerBound
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ProperlyDiscontinuousSMul G X] [ContinuousConstSMul G X]
    (rho : X → ℝ) (hrho : Continuous rho)
    {K V : Set X} (hK : IsCompact K) (hV : IsCompact V)
    (hpos : ∀ (g : G) (x : X), x ∈ K → 0 < rho (g • x)) :
    ∃ a : ℝ, 0 < a ∧ ∀ (g : G) (x : X), x ∈ K → g • x ∈ V → a ≤ rho (g • x) := by
  let S : Set G := {g | ((g • ·) '' K ∩ V).Nonempty}
  have hS : S.Finite := finite_disjoint_inter_image hK hV
  let T : Set X := ⋃ g ∈ hS.toFinset, (g • ·) '' K
  have hT : IsCompact T := hS.toFinset.isCompact_biUnion fun g _ ↦
    hK.image (continuous_const_smul g)
  by_cases hTne : T.Nonempty
  · obtain ⟨z, hzT, hzmin⟩ := hT.exists_isMinOn hTne hrho.continuousOn
    obtain ⟨g, hg, x, hx, rfl⟩ := Set.mem_iUnion₂.mp hzT
    refine ⟨rho (g • x), hpos g x hx, ?_⟩
    intro k y hyK hkyV
    have hkS : k ∈ S := ⟨k • y, ⟨⟨y, hyK, rfl⟩, hkyV⟩⟩
    apply hzmin
    exact Set.mem_iUnion₂.mpr ⟨k, by simpa [S] using hkS, ⟨y, hyK, rfl⟩⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro g x hxK hgV
    have hgS : g ∈ S := ⟨g • x, ⟨⟨x, hxK, rfl⟩, hgV⟩⟩
    exact False.elim (hTne ⟨g • x,
      Set.mem_iUnion₂.mpr ⟨g, by simpa [S] using hgS, ⟨x, hxK, rfl⟩⟩⟩)

namespace Geometry

open Set SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness
open TorusFamily AnalyticTorusFamily GlobalTorusFamily ComplexTorus
open EllipticVaryingFamilyQuotient EllipticCayleyHomeomorph
open EllipticLocalCoordinates EllipticHolomorphicLogCover
open EllipticLocalTrivialization
open EllipticLinearCollarGlobalDescent
open EllipticPuncturedCollarGaugeHomeomorph EquivariantQuotientHomeomorph
open PaperAnalyticData

/-- The canonical projection from the regular torus family to the paper's central quotient. -/
@[expose] public noncomputable def PaperAnalyticData.centralQuotientProjection
    (P : PaperAnalyticData) : RegularTotalSpace P.periods → P.CentralFamily := by
  let _ := regularFamilyDeckAction P.periods
  exact quotientProjection

/-- The central quotient projection is a local homeomorphism. -/
public theorem PaperAnalyticData.centralQuotientProjection_isLocalHomeomorph
    (P : PaperAnalyticData) : IsLocalHomeomorph P.centralQuotientProjection := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      P.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := P.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := P.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap P.periods)
  let _ := familyContinuousConstSMul (regularParameterMap P.periods)
    fun a ↦ (regularPeriodSection_contMDiff P.periods hproper a
      RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap P.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap P.periods)
      (regularParameterMap_compactUniformLowerBound P.periods))
  let htotal := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    P.periods hproper RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (RegularTotalSpace P.periods) := htotal.1
  let _ : LocallyCompactSpace (RegularTotalSpace P.periods) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (RegularTotalSpace P.periods) := by infer_instance
  let _ := regularFamilyDeckAction P.periods
  let _ : IsCancelSMul Delta (RegularTotalSpace P.periods) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian P.periods
      P.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace P.periods) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source P.periods hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace P.periods) :=
    regularFamilyDeckAction_continuousConstSMul P.periods hproper
  rw [centralQuotientProjection.eq_def]
  exact quotientProjection_isLocalHomeomorph

public theorem PaperAnalyticData.centralQuotientProjection_surjective
    (P : PaperAnalyticData) : Function.Surjective P.centralQuotientProjection := by
  rw [centralQuotientProjection.eq_def]
  exact Quotient.mk_surjective

/-- Every compact subset of the central quotient is covered by a compact set of regular-family
representatives. -/
public theorem PaperAnalyticData.centralCompact_has_compactRepresentatives
    (P : PaperAnalyticData) (K : Set P.CentralFamily) (hK : IsCompact K) :
    ∃ L : Set (RegularTotalSpace P.periods),
      IsCompact L ∧ K ⊆ P.centralQuotientProjection '' L := by
  let _ := P.starCentralCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ P.CentralFamily :=
    P.starCentral_isManifold
  let _ : LocallyCompactSpace P.CentralFamily :=
    Manifold.locallyCompact_of_finiteDimensional
      (modelWithCornersSelf ℂ ComplexModel)
  exact SphereSixComplex.IsLocalHomeomorph.exists_compact_source_cover
    P.centralQuotientProjection_isLocalHomeomorph
    P.centralQuotientProjection_surjective hK

public theorem PaperAnalyticData.orderThreeStarToCentral_mk
    (P : PaperAnalyticData)
    (q : (orderThreeAffinePuncturedCarrier P.periods
      P.modular.modularParameter.toTriangleUniformization_sourceAction
      P.starSeparation.orderThree.radius).carrier) :
    P.starToCentral (1 : Fin 3) (Quotient.mk _ q) =
      P.centralQuotientProjection
        (orderThreeCollarToRegular P.periods
          (sourceActionProperlyDiscontinuous_of_eq
            P.modular.modularParameter.toTriangleUniformization_sourceAction)
          P.starSeparation.orderThree.sourceData
          (orderThreePuncturedCollarGaugeEquiv P.periods
            P.starSeparation.orderThree.radius q)) := by
  let _ := P.totalSpaceCharts
  change P.orderThreePuncturedCollarToCentralFamily
      P.starSeparation.orderThree.sourceData (Quotient.mk _ q) = _
  rw [orderThreePuncturedCollarToCentralFamily.eq_def,
    centralQuotientProjection.eq_def]
  rfl

public theorem PaperAnalyticData.orderFourStarToCentral_mk
    (P : PaperAnalyticData)
    (q : (orderFourAffinePuncturedCarrier P.periods
      P.modular.modularParameter.toTriangleUniformization_sourceAction
      P.starSeparation.orderFour.radius).carrier) :
    P.starToCentral (2 : Fin 3) (Quotient.mk _ q) =
      P.centralQuotientProjection
        (orderFourCollarToRegular P.periods
          (sourceActionProperlyDiscontinuous_of_eq
            P.modular.modularParameter.toTriangleUniformization_sourceAction)
          P.starSeparation.orderFour.sourceData
          (orderFourPuncturedCollarGaugeEquiv P.periods
            P.starSeparation.orderFour.radius q)) := by
  let _ := P.totalSpaceCharts
  change P.orderFourPuncturedCollarToCentralFamily
      P.starSeparation.orderFour.sourceData (Quotient.mk _ q) = _
  rw [orderFourPuncturedCollarToCentralFamily.eq_def,
    centralQuotientProjection.eq_def]
  rfl

public theorem PaperAnalyticData.orderThreeStarCollarRadius_mk
    (P : PaperAnalyticData)
    (q : (orderThreeAffinePuncturedCarrier P.periods
      P.modular.modularParameter.toTriangleUniformization_sourceAction
      P.starSeparation.orderThree.radius).carrier) :
    P.starCollarRadius (1 : Fin 3) (Quotient.mk _ q) =
      orderThreeFamilyRadius P.periods q := by
  change P.orderThreeFillingRadius P.starSeparation.orderThree.radius
      (P.orderThreePuncturedCollarToFilling
        P.starSeparation.orderThree.radius (Quotient.mk _ q)) = _
  rw [P.orderThreePuncturedCollarToFilling_mk]
  rfl

public theorem PaperAnalyticData.orderFourStarCollarRadius_mk
    (P : PaperAnalyticData)
    (q : (orderFourAffinePuncturedCarrier P.periods
      P.modular.modularParameter.toTriangleUniformization_sourceAction
      P.starSeparation.orderFour.radius).carrier) :
    P.starCollarRadius (2 : Fin 3) (Quotient.mk _ q) =
      orderFourFamilyRadius P.periods q := by
  change P.orderFourFillingRadius P.starSeparation.orderFour.radius
      (P.orderFourPuncturedCollarToFilling
        P.starSeparation.orderFour.radius (Quotient.mk _ q)) = _
  rw [P.orderFourPuncturedCollarToFilling_mk]
  rfl

/-- A compact set of representatives for a central compact set gives a uniform positive
order-three Cayley radius for every representative lying in the selected collar. -/
public theorem PaperAnalyticData.orderThreeCentralOrbitRadius_lowerBound
    (P : PaperAnalyticData) (r : ℝ) (hr : r < 1)
    (K : Set P.CentralFamily) (L : Set (RegularTotalSpace P.periods))
    (hL : IsCompact L)
    (hcover : K ⊆ P.centralQuotientProjection '' L) :
    ∃ a : ℝ, 0 < a ∧ ∀ q : RegularTotalSpace P.periods,
      P.centralQuotientProjection q ∈ K →
      ‖(orderThreeCayleyHomeomorph
        (regularTotalSpaceBase P.periods q).1).1‖ < r →
      a ≤ ‖(orderThreeCayleyHomeomorph
        (regularTotalSpaceBase P.periods q).1).1‖ := by
  let U := P.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    P.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianProperlyDiscontinuous_of_source hsource
      (sourceActionProperlyDiscontinuous_of_eq hsource)
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g ↦ (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let B : Set UpperHalfPlane :=
    (fun x : RegularTotalSpace P.periods ↦
      (regularTotalSpaceBase P.periods x).1) '' L
  have hB : IsCompact B := hL.image
    (continuous_subtype_val.comp (regularTotalSpaceBase_continuous P.periods))
  let V : Set UpperHalfPlane := {z |
    0 ≤ ‖(orderThreeCayleyHomeomorph z).1‖ ∧
      ‖(orderThreeCayleyHomeomorph z).1‖ ≤ r}
  have hV : IsCompact V := orderThreeCayleyRadiusBand_isCompact 0 r hr
  obtain ⟨a, ha, haBound⟩ :=
    properlyDiscontinuous_compact_translate_positiveLowerBound
      (fun z : UpperHalfPlane ↦ ‖(orderThreeCayleyHomeomorph z).1‖)
      (continuous_norm.comp
        (continuous_subtype_val.comp orderThreeCayleyHomeomorph.continuous))
      hB hV (by
        intro (g : Delta) z hzB
        obtain ⟨x, hxL, rfl⟩ := hzB
        have hne : orderThreeCayleyHomeomorph
            (g • (regularTotalSpaceBase P.periods x).1) ≠ discCenter := by
          intro heq
          have hfixed : g • (regularTotalSpaceBase P.periods x).1 =
              fuchsianOneFixedPoint := by
            apply orderThreeCayleyHomeomorph.injective
            rw [heq, orderThreeCayleyHomeomorph_fixedPoint]
          have hreg := isRegularBasePoint_smul (U := U) g
            (regularTotalSpaceBase P.periods x).property
          have hnot := (isRegularBasePoint_iff_not_mem_orbits
            (U := U) (U.sourceAction g •
              (regularTotalSpaceBase P.periods x).1)).mp hreg
          apply hnot
          left
          have hfixedU : U.sourceAction g •
              (regularTotalSpaceBase P.periods x).1 = U.zOne := by
            rw [hsource, (ellipticFixedPoints_eq_of_fuchsian hsource).1]
            exact hfixed
          rw [hfixedU]
          simp only [sourceOrbitSet.eq_def, Set.mem_iUnion,
            Set.mem_singleton_iff]
          exact ⟨1, by simp⟩
        exact norm_pos_iff.mpr (coe_ne_zero_of_ne_center hne))
  refine ⟨a, ha, ?_⟩
  intro q hqK hqr
  obtain ⟨x, hxL, hxq⟩ := hcover hqK
  let _ := regularFamilyDeckAction P.periods
  rw [centralQuotientProjection.eq_def] at hxq
  have hrel := Quotient.exact hxq.symm
  change MulAction.orbitRel Delta _ q x at hrel
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  change regularFamilyDeckMap P.periods g x = q at hg
  have hxB : (regularTotalSpaceBase P.periods x).1 ∈ B := ⟨x, hxL, rfl⟩
  have hbase : g • (regularTotalSpaceBase P.periods x).1 =
      (regularTotalSpaceBase P.periods q).1 := by
    change fuchsianSourceAction g • (regularTotalSpaceBase P.periods x).1 = _
    rw [← hsource]
    calc
      U.sourceAction g • (regularTotalSpaceBase P.periods x).1 =
          (regularTotalSpaceBase P.periods
            (regularFamilyDeckMap P.periods g x)).1 :=
        congrArg Subtype.val
          (regularTotalSpaceBase_familyDeckMap P.periods g x).symm
      _ = (regularTotalSpaceBase P.periods q).1 :=
        congrArg (fun y ↦ (regularTotalSpaceBase P.periods y).1) hg
  have hVq : g • (regularTotalSpaceBase P.periods x).1 ∈ V := by
    rw [hbase]
    exact ⟨norm_nonneg _, hqr.le⟩
  simpa only [hbase] using
    haBound g (regularTotalSpaceBase P.periods x).1 hxB hVq

/-- A compact set of representatives for a central compact set gives a uniform positive
order-four Cayley radius for every representative lying in the selected collar. -/
public theorem PaperAnalyticData.orderFourCentralOrbitRadius_lowerBound
    (P : PaperAnalyticData) (r : ℝ) (hr : r < 1)
    (K : Set P.CentralFamily) (L : Set (RegularTotalSpace P.periods))
    (hL : IsCompact L)
    (hcover : K ⊆ P.centralQuotientProjection '' L) :
    ∃ a : ℝ, 0 < a ∧ ∀ q : RegularTotalSpace P.periods,
      P.centralQuotientProjection q ∈ K →
      ‖(orderFourCayleyHomeomorph
        (regularTotalSpaceBase P.periods q).1).1‖ < r →
      a ≤ ‖(orderFourCayleyHomeomorph
        (regularTotalSpaceBase P.periods q).1).1‖ := by
  let U := P.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    P.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianProperlyDiscontinuous_of_source hsource
      (sourceActionProperlyDiscontinuous_of_eq hsource)
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g ↦ (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let B : Set UpperHalfPlane :=
    (fun x : RegularTotalSpace P.periods ↦
      (regularTotalSpaceBase P.periods x).1) '' L
  have hB : IsCompact B := hL.image
    (continuous_subtype_val.comp (regularTotalSpaceBase_continuous P.periods))
  let V : Set UpperHalfPlane := {z |
    0 ≤ ‖(orderFourCayleyHomeomorph z).1‖ ∧
      ‖(orderFourCayleyHomeomorph z).1‖ ≤ r}
  have hV : IsCompact V := orderFourCayleyRadiusBand_isCompact 0 r hr
  obtain ⟨a, ha, haBound⟩ :=
    properlyDiscontinuous_compact_translate_positiveLowerBound
      (fun z : UpperHalfPlane ↦ ‖(orderFourCayleyHomeomorph z).1‖)
      (continuous_norm.comp
        (continuous_subtype_val.comp orderFourCayleyHomeomorph.continuous))
      hB hV (by
        intro (g : Delta) z hzB
        obtain ⟨x, hxL, rfl⟩ := hzB
        have hne : orderFourCayleyHomeomorph
            (g • (regularTotalSpaceBase P.periods x).1) ≠ discCenter := by
          intro heq
          have hfixed : g • (regularTotalSpaceBase P.periods x).1 =
              fuchsianTwoFixedPoint := by
            apply orderFourCayleyHomeomorph.injective
            rw [heq, orderFourCayleyHomeomorph_fixedPoint]
          have hreg := isRegularBasePoint_smul (U := U) g
            (regularTotalSpaceBase P.periods x).property
          have hnot := (isRegularBasePoint_iff_not_mem_orbits
            (U := U) (U.sourceAction g •
              (regularTotalSpaceBase P.periods x).1)).mp hreg
          apply hnot
          right
          have hfixedU : U.sourceAction g •
              (regularTotalSpaceBase P.periods x).1 = U.zTwo := by
            rw [hsource, (ellipticFixedPoints_eq_of_fuchsian hsource).2]
            exact hfixed
          rw [hfixedU]
          simp only [sourceOrbitSet.eq_def, Set.mem_iUnion,
            Set.mem_singleton_iff]
          exact ⟨1, by simp⟩
        exact norm_pos_iff.mpr (coe_ne_zero_of_ne_center hne))
  refine ⟨a, ha, ?_⟩
  intro q hqK hqr
  obtain ⟨x, hxL, hxq⟩ := hcover hqK
  let _ := regularFamilyDeckAction P.periods
  rw [centralQuotientProjection.eq_def] at hxq
  have hrel := Quotient.exact hxq.symm
  change MulAction.orbitRel Delta _ q x at hrel
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  change regularFamilyDeckMap P.periods g x = q at hg
  have hxB : (regularTotalSpaceBase P.periods x).1 ∈ B := ⟨x, hxL, rfl⟩
  have hbase : g • (regularTotalSpaceBase P.periods x).1 =
      (regularTotalSpaceBase P.periods q).1 := by
    change fuchsianSourceAction g • (regularTotalSpaceBase P.periods x).1 = _
    rw [← hsource]
    calc
      U.sourceAction g • (regularTotalSpaceBase P.periods x).1 =
          (regularTotalSpaceBase P.periods
            (regularFamilyDeckMap P.periods g x)).1 :=
        congrArg Subtype.val
          (regularTotalSpaceBase_familyDeckMap P.periods g x).symm
      _ = (regularTotalSpaceBase P.periods q).1 :=
        congrArg (fun y ↦ (regularTotalSpaceBase P.periods y).1) hg
  have hVq : g • (regularTotalSpaceBase P.periods x).1 ∈ V := by
    rw [hbase]
    exact ⟨norm_nonneg _, hqr.le⟩
  simpa only [hbase] using
    haBound g (regularTotalSpaceBase P.periods x).1 hxB hVq

/-- Compact subsets of the central piece stay a positive distance from the missing order-three
elliptic fibre along the actual affine collar. -/
public theorem PaperAnalyticData.orderThreeCentralPositiveLowerTrap
    (P : PaperAnalyticData) :
    ∀ K : Set P.CentralFamily, IsCompact K →
      ∃ a : ℝ, 0 < a ∧ ∀ s : P.starCollarSourceType (1 : Fin 3),
        P.starToCentral (1 : Fin 3) s ∈ K →
          a ≤ P.starCollarRadius (1 : Fin 3) s := by
  intro K hK
  obtain ⟨L, hL, hcover⟩ := P.centralCompact_has_compactRepresentatives K hK
  obtain ⟨a, ha, haBound⟩ := P.orderThreeCentralOrbitRadius_lowerBound
    P.starSeparation.orderThree.radius
    P.starSeparation.orderThree.radius_lt_one K L hL hcover
  refine ⟨a, ha, ?_⟩
  intro s hsK
  induction s using Quotient.inductionOn with
  | _ q =>
      let hproper : SourceActionProperlyDiscontinuous :=
        sourceActionProperlyDiscontinuous_of_eq
          P.modular.modularParameter.toTriangleUniformization_sourceAction
      let qlin := orderThreePuncturedCollarGaugeEquiv P.periods
        P.starSeparation.orderThree.radius q
      let qreg := orderThreeCollarToRegular P.periods hproper
        P.starSeparation.orderThree.sourceData qlin
      have hqregK : P.centralQuotientProjection qreg ∈ K := by
        rw [← P.orderThreeStarToCentral_mk q]
        exact hsK
      have hbase : ‖(orderThreeCayleyHomeomorph
          (regularTotalSpaceBase P.periods qreg).1).1‖ =
          orderThreeFamilyRadius P.periods qlin := by
        rw [orderThreeFamilyRadius.eq_def]
        exact congrArg (fun z : UpperHalfPlane ↦
          ‖(orderThreeCayleyHomeomorph z).1‖)
          (orderThreeCollarToRegular_base P.periods hproper
            P.modular.modularParameter.toTriangleUniformization_sourceAction
            P.starSeparation.orderThree.sourceData qlin)
      have hlt : ‖(orderThreeCayleyHomeomorph
          (regularTotalSpaceBase P.periods qreg).1).1‖ <
          P.starSeparation.orderThree.radius := by
        rw [hbase]
        exact qlin.property.2
      calc
        a ≤ ‖(orderThreeCayleyHomeomorph
            (regularTotalSpaceBase P.periods qreg).1).1‖ :=
          haBound qreg hqregK hlt
        _ = orderThreeFamilyRadius P.periods qlin := hbase
        _ = orderThreeFamilyRadius P.periods q :=
          orderThreeFamilyRadius_principalGauge P.periods q
        _ = P.starCollarRadius (1 : Fin 3) (Quotient.mk _ q) :=
          (P.orderThreeStarCollarRadius_mk q).symm

/-- Compact subsets of the central piece stay a positive distance from the missing order-four
elliptic fibre along the actual affine collar. -/
public theorem PaperAnalyticData.orderFourCentralPositiveLowerTrap
    (P : PaperAnalyticData) :
    ∀ K : Set P.CentralFamily, IsCompact K →
      ∃ a : ℝ, 0 < a ∧ ∀ s : P.starCollarSourceType (2 : Fin 3),
        P.starToCentral (2 : Fin 3) s ∈ K →
          a ≤ P.starCollarRadius (2 : Fin 3) s := by
  intro K hK
  obtain ⟨L, hL, hcover⟩ := P.centralCompact_has_compactRepresentatives K hK
  obtain ⟨a, ha, haBound⟩ := P.orderFourCentralOrbitRadius_lowerBound
    P.starSeparation.orderFour.radius
    P.starSeparation.orderFour.radius_lt_one K L hL hcover
  refine ⟨a, ha, ?_⟩
  intro s hsK
  induction s using Quotient.inductionOn with
  | _ q =>
      let hproper : SourceActionProperlyDiscontinuous :=
        sourceActionProperlyDiscontinuous_of_eq
          P.modular.modularParameter.toTriangleUniformization_sourceAction
      let qlin := orderFourPuncturedCollarGaugeEquiv P.periods
        P.starSeparation.orderFour.radius q
      let qreg := orderFourCollarToRegular P.periods hproper
        P.starSeparation.orderFour.sourceData qlin
      have hqregK : P.centralQuotientProjection qreg ∈ K := by
        rw [← P.orderFourStarToCentral_mk q]
        exact hsK
      have hbase : ‖(orderFourCayleyHomeomorph
          (regularTotalSpaceBase P.periods qreg).1).1‖ =
          orderFourFamilyRadius P.periods qlin := by
        rw [orderFourFamilyRadius.eq_def]
        exact congrArg (fun z : UpperHalfPlane ↦
          ‖(orderFourCayleyHomeomorph z).1‖)
          (orderFourCollarToRegular_base P.periods hproper
            P.modular.modularParameter.toTriangleUniformization_sourceAction
            P.starSeparation.orderFour.sourceData qlin)
      have hlt : ‖(orderFourCayleyHomeomorph
          (regularTotalSpaceBase P.periods qreg).1).1‖ <
          P.starSeparation.orderFour.radius := by
        rw [hbase]
        exact qlin.property.2
      calc
        a ≤ ‖(orderFourCayleyHomeomorph
            (regularTotalSpaceBase P.periods qreg).1).1‖ :=
          haBound qreg hqregK hlt
        _ = orderFourFamilyRadius P.periods qlin := hbase
        _ = orderFourFamilyRadius P.periods q :=
          orderFourFamilyRadius_principalGauge P.periods q
        _ = P.starCollarRadius (2 : Fin 3) (Quotient.mk _ q) :=
          (P.orderFourStarCollarRadius_mk q).symm

public theorem PaperAnalyticData.orderThreeCollarPairMap_isProper
    (P : PaperAnalyticData) :
    IsProperMap (P.openEmbeddingStarData.collarPairMap (1 : Fin 3)) :=
  P.orderThreeCollarPairMap_isProper_of_centralLowerTrap
    P.orderThreeCentralPositiveLowerTrap

public theorem PaperAnalyticData.orderFourCollarPairMap_isProper
    (P : PaperAnalyticData) :
    IsProperMap (P.openEmbeddingStarData.collarPairMap (2 : Fin 3)) :=
  P.orderFourCollarPairMap_isProper_of_centralLowerTrap
    P.orderFourCentralPositiveLowerTrap

end Geometry

end

end SphereSixComplex
