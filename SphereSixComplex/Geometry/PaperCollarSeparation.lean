module

public import SphereSixComplex.Geometry.CuspPuncturedCollarBridge
public import SphereSixComplex.Geometry.PaperAnalyticFillingPieces
import all SphereSixComplex.Geometry.CuspPuncturedCollarBridge
import all SphereSixComplex.Geometry.GlobalTorusFamily

/-!
# Pairwise separation of the three filling collars

The elliptic collars must be shrunk simultaneously: each avoids the closed orbit-saturation of
the selected cusp horodisc, and their images in the Fuchsian base quotient are disjoint.
-/

namespace SphereSixComplex.Geometry

open Set Topology SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open TorusFamily GlobalTorusFamily EllipticCayleyHomeomorph
open EllipticWholeFiberCompactCover EllipticPuncturedCollarGaugeHomeomorph
open EllipticVaryingFamilyQuotient EllipticAffineGlobalSeparation
open EllipticLinearCollarGlobalDescent StandardInfiniteA2ToricModel
open StandardInfiniteA2ToricQuantitativeRegions.BoundedPolydiscRegions
open CuspPuncturedCollarBridge EstablishedFuchsianCuspNeighborhood
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness

noncomputable section

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- Equality in the punctured global family forces the corresponding regular source points to
lie in one triangle-group orbit. -/
public theorem regularBase_orbit_of_global_eq
    {U : TriangleUniformization} (F : PeriodFunctions U)
    {x y : RegularTotalSpace F}
    (h : (Quotient.mk _ x : PuncturedGlobalFamily F) = Quotient.mk _ y) :
    ∃ g : Delta,
      U.sourceAction g • (regularTotalSpaceBase F y).1 =
        (regularTotalSpaceBase F x).1 := by
  let _ := regularFamilyDeckAction F
  have hrel := Quotient.exact h
  change MulAction.orbitRel Delta (RegularTotalSpace F) x y at hrel
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  refine ⟨g, ?_⟩
  change regularFamilyDeckMap F g y = x at hg
  calc
    U.sourceAction g • (regularTotalSpaceBase F y).1 =
        (regularTotalSpaceBase F (regularFamilyDeckMap F g y)).1 :=
      congrArg Subtype.val (regularTotalSpaceBase_familyDeckMap F g y).symm
    _ = (regularTotalSpaceBase F x).1 :=
      congrArg (fun z ↦ (regularTotalSpaceBase F z).1) hg

public theorem orderThreeCollarToRegular_base
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    {r : ℝ} (D : OrderThreeLinearCollarSourceData (U := U) r)
    (q : (orderThreeLinearPuncturedCarrier F hsource r).carrier) :
    (regularTotalSpaceBase F (orderThreeCollarToRegular F hproper D q)).1 =
      familyTotalSpaceBase F q := by
  have h := congrArg (familyTotalSpaceBase F)
    (regularFamilyInclusion_orderThreeCollarToRegular F hproper D q)
  rw [familyTotalSpaceBase_regularFamilyInclusion] at h
  exact h

public theorem orderFourCollarToRegular_base
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    {r : ℝ} (D : OrderFourLinearCollarSourceData (U := U) r)
    (q : (orderFourLinearPuncturedCarrier F hsource r).carrier) :
    (regularTotalSpaceBase F (orderFourCollarToRegular F hproper D q)).1 =
      familyTotalSpaceBase F q := by
  have h := congrArg (familyTotalSpaceBase F)
    (regularFamilyInclusion_orderFourCollarToRegular F hproper D q)
  rw [familyTotalSpaceBase_regularFamilyInclusion] at h
  exact h

/-- The quantitative local cusp witness attached to the selected analytic package. -/
@[expose] public noncomputable def actualLocalCuspWitness :
    ActualLocalCuspQuotientWitness A.cuspCoordinate A.toricModel :=
  Classical.choice (exists_actualLocalCuspQuotientWitness A.cuspCoordinate A.toricModel
    A.toricModel.toTorusActionPreservesComponents)

/-- The common-radius cusp witness, after imposing precise Fuchsian separation. -/
@[expose] public noncomputable def actualPuncturedCuspWitness :
    ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel :=
  Classical.choice (exists_actualPuncturedCuspCollarWitness A.actualLocalCuspWitness)

/-- Simultaneously shrunk elliptic radii, separated from one another and from the cusp orbit. -/
public structure CollarSeparationData
    (W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel) where
  orderThree : A.OrderThreeFillingPiece
  orderFour : A.OrderFourFillingPiece
  orderThree_avoids_cusp : ∀ z : UpperHalfPlane,
    ‖(orderThreeCayleyHomeomorph z : ℂ)‖ < orderThree.radius →
      z ∉ closure (⋃ g : Delta,
        (fun x : UpperHalfPlane ↦
          A.modular.modularParameter.toTriangleUniformization.sourceAction g • x) ''
            normalizedCuspRegion A.cuspCoordinate W.localWitness.radius)
  orderFour_avoids_cusp : ∀ z : UpperHalfPlane,
    ‖(orderFourCayleyHomeomorph z : ℂ)‖ < orderFour.radius →
      z ∉ closure (⋃ g : Delta,
        (fun x : UpperHalfPlane ↦
          A.modular.modularParameter.toTriangleUniformization.sourceAction g • x) ''
            normalizedCuspRegion A.cuspCoordinate W.localWitness.radius)
  orderThree_coordinate_bound : ∀ z : UpperHalfPlane,
    ‖(orderThreeCayleyHomeomorph z : ℂ)‖ < orderThree.radius →
      ‖A.modular.sourceCoordinate.coordinate z‖ < 1 / 3
  orderFour_coordinate_bound : ∀ z : UpperHalfPlane,
    ‖(orderFourCayleyHomeomorph z : ℂ)‖ < orderFour.radius →
      ‖A.modular.sourceCoordinate.coordinate z - 1‖ < 1 / 3
  elliptic_orbits_disjoint : ∀ z x : UpperHalfPlane,
    ‖(orderThreeCayleyHomeomorph z : ℂ)‖ < orderThree.radius →
    ‖(orderFourCayleyHomeomorph x : ℂ)‖ < orderFour.radius →
      ∀ g : Delta,
        A.modular.modularParameter.toTriangleUniformization.sourceAction g • x ≠ z

public theorem exists_collarSeparationData
    (W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel) :
    Nonempty (A.CollarSeparationData W) := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianProperlyDiscontinuous_of_source hsource hproper
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g ↦ (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let C : Set UpperHalfPlane := closure (⋃ g : Delta,
    (fun x : UpperHalfPlane ↦ U.sourceAction g • x) ''
      normalizedCuspRegion A.cuspCoordinate W.localWitness.radius)
  let Q := Quotient (MulAction.orbitRel Delta UpperHalfPlane)
  let q : UpperHalfPlane → Q := Quotient.mk _
  have hfixed := ellipticFixedPoints_eq_of_fuchsian hsource
  have hnotRegularOne : ¬IsRegularBasePoint (U := U) fuchsianOneFixedPoint := by
    intro h
    simp only [GlobalTorusFamily.IsRegularBasePoint] at h
    apply (h 1).1
    simpa using hfixed.1.symm
  have hnotRegularTwo : ¬IsRegularBasePoint (U := U) fuchsianTwoFixedPoint := by
    intro h
    simp only [GlobalTorusFamily.IsRegularBasePoint] at h
    apply (h 1).2
    simpa using hfixed.2.symm
  have hnotCOne : fuchsianOneFixedPoint ∉ C := fun h ↦
    hnotRegularOne (W.orbitClosure_region_regular h)
  have hnotCTwo : fuchsianTwoFixedPoint ∉ C := fun h ↦
    hnotRegularTwo (W.orbitClosure_region_regular h)
  have hquotientNe : q fuchsianOneFixedPoint ≠ q fuchsianTwoFixedPoint := by
    intro h
    have hr := Quotient.exact h
    change MulAction.orbitRel Delta UpperHalfPlane
      fuchsianOneFixedPoint fuchsianTwoFixedPoint at hr
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hr
    obtain ⟨g, hg⟩ := hr
    exact fuchsianTwo_orbit_ne_one g hg
  obtain ⟨S, T, hSopen, hTopen, hqOne, hqTwo, hST⟩ :=
    t2_separation hquotientNe
  let S' := q ⁻¹' S ∩ Cᶜ ∩
    {z | ‖A.modular.sourceCoordinate.coordinate z‖ < 1 / 3}
  let T' := q ⁻¹' T ∩ Cᶜ ∩
    {z | ‖A.modular.sourceCoordinate.coordinate z - 1‖ < 1 / 3}
  have hS'open : IsOpen S' :=
    ((hSopen.preimage continuous_quot_mk).inter isClosed_closure.isOpen_compl).inter
      (isOpen_lt
        (continuous_norm.comp A.modular.sourceCoordinate.coordinate_holomorphic.continuous)
        continuous_const)
  have hT'open : IsOpen T' :=
    ((hTopen.preimage continuous_quot_mk).inter isClosed_closure.isOpen_compl).inter
      (isOpen_lt
        (continuous_norm.comp
          (A.modular.sourceCoordinate.coordinate_holomorphic.continuous.sub continuous_const))
        continuous_const)
  have hOneS' : fuchsianOneFixedPoint ∈ S' := by
    refine ⟨⟨hqOne, hnotCOne⟩, ?_⟩
    change ‖A.modular.sourceCoordinate.coordinate fuchsianOneFixedPoint‖ < 1 / 3
    rw [A.modular.sourceCoordinate.coordinate_at_one]
    norm_num
  have hTwoT' : fuchsianTwoFixedPoint ∈ T' := by
    refine ⟨⟨hqTwo, hnotCTwo⟩, ?_⟩
    change ‖A.modular.sourceCoordinate.coordinate fuchsianTwoFixedPoint - 1‖ < 1 / 3
    rw [A.modular.sourceCoordinate.coordinate_at_two]
    norm_num
  obtain ⟨s₃, hs₃, hs₃one, hs₃S⟩ :=
    exists_cayleyRadius_subset fuchsianOneFixedPoint hS'open hOneS'
  obtain ⟨s₄, hs₄, hs₄one, hs₄T⟩ :=
    exists_cayleyRadius_subset fuchsianTwoFixedPoint hT'open hTwoT'
  obtain ⟨P₃⟩ := A.exists_orderThreeFillingPiece
  obtain ⟨P₄⟩ := A.exists_orderFourFillingPiece
  let r₃ := min P₃.radius s₃
  let r₄ := min P₄.radius s₄
  have hr₃ : 0 < r₃ := lt_min P₃.radius_pos hs₃
  have hr₄ : 0 < r₄ := lt_min P₄.radius_pos hs₄
  let P₃' : A.OrderThreeFillingPiece :=
    ⟨r₃, hr₃, (min_le_left _ _).trans_lt P₃.radius_lt_one,
      A.orderThreeLinearCollarSourceData_mono (min_le_left _ _) P₃.sourceData⟩
  let P₄' : A.OrderFourFillingPiece :=
    ⟨r₄, hr₄, (min_le_left _ _).trans_lt P₄.radius_lt_one,
      A.orderFourLinearCollarSourceData_mono (min_le_left _ _) P₄.sourceData⟩
  refine ⟨⟨P₃', P₄', ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro z hz
    exact (hs₃S z (hz.trans_le (min_le_right _ _))).1.2
  · intro z hz
    exact (hs₄T z (hz.trans_le (min_le_right _ _))).1.2
  · intro z hz
    exact (hs₃S z (hz.trans_le (min_le_right _ _))).2
  · intro z hz
    exact (hs₄T z (hz.trans_le (min_le_right _ _))).2
  · intro z x hz hx g hg
    have hzS : q z ∈ S := (hs₃S z (hz.trans_le (min_le_right _ _))).1.1
    have hxT : q x ∈ T := (hs₄T x (hx.trans_le (min_le_right _ _))).1.1
    have hqxz : q x = q z := by
      apply Quotient.sound
      change MulAction.orbitRel Delta UpperHalfPlane x z
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨g⁻¹, ?_⟩
      rw [← hg]
      change fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • x) = x
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    exact Set.disjoint_left.mp hST hzS (hqxz ▸ hxT)

namespace CollarSeparationData

variable {A : PaperAnalyticData}
  {W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel}

/-- The two simultaneously shrunk elliptic collar images are disjoint in the central family. -/
public theorem elliptic_centralRanges_disjoint (S : A.CollarSeparationData W) :
    Disjoint
      (Set.range (A.orderThreePuncturedCollarToCentralFamily S.orderThree.sourceData))
      (Set.range (A.orderFourPuncturedCollarToCentralFamily S.orderFour.sourceData)) := by
  rw [Set.disjoint_left]
  rintro p ⟨q₃, rfl⟩ ⟨q₄, hp⟩
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := A.totalSpaceCharts
  let _ := regularFamilyDeckAction A.periods
  change orderFourLinearCollarToPuncturedGlobalFamily A.periods hproper hsource
      S.orderFour.sourceData
        (orderFourPuncturedCollarQuotientHomeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph hsource S.orderFour.radius q₄) =
    orderThreeLinearCollarToPuncturedGlobalFamily A.periods hproper hsource
      S.orderThree.sourceData
        (orderThreePuncturedCollarQuotientHomeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph hsource S.orderThree.radius q₃) at hp
  generalize hQ₃ : orderThreePuncturedCollarQuotientHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph hsource S.orderThree.radius q₃ = Q₃ at hp
  generalize hQ₄ : orderFourPuncturedCollarQuotientHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph hsource S.orderFour.radius q₄ = Q₄ at hp
  induction Q₃ using Quotient.inductionOn with
  | _ x₃ =>
    induction Q₄ using Quotient.inductionOn with
    | _ x₄ =>
      rw [orderFourLinearCollarToPuncturedGlobalFamily_mk,
        orderThreeLinearCollarToPuncturedGlobalFamily_mk] at hp
      obtain ⟨g, hg⟩ := regularBase_orbit_of_global_eq A.periods hp
      rw [orderFourCollarToRegular_base A.periods hproper hsource
          S.orderFour.sourceData,
        orderThreeCollarToRegular_base A.periods hproper hsource
          S.orderThree.sourceData] at hg
      have hx₃ : ‖(orderThreeCayleyHomeomorph
          (familyTotalSpaceBase A.periods x₃) : ℂ)‖ < S.orderThree.radius := by
        simpa only [orderThreeLinearPuncturedCarrier.eq_def,
          orderThreePuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
          orderThreeFamilyRadius.eq_def] using x₃.property.2
      have hx₄ : ‖(orderFourCayleyHomeomorph
          (familyTotalSpaceBase A.periods x₄) : ℂ)‖ < S.orderFour.radius := by
        simpa only [orderFourLinearPuncturedCarrier.eq_def,
          orderFourPuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
          orderFourFamilyRadius.eq_def] using x₄.property.2
      apply S.elliptic_orbits_disjoint (familyTotalSpaceBase A.periods x₃)
        (familyTotalSpaceBase A.periods x₄) hx₃ hx₄ g⁻¹
      calc
        U.sourceAction g⁻¹ • familyTotalSpaceBase A.periods x₄ =
            U.sourceAction g⁻¹ •
              (U.sourceAction g • familyTotalSpaceBase A.periods x₃) :=
          congrArg _ hg.symm
        _ = familyTotalSpaceBase A.periods x₃ := by
          rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

/-- The cusp collar image is disjoint from the simultaneously shrunk order-three image. -/
public theorem cusp_orderThree_centralRanges_disjoint (S : A.CollarSeparationData W) :
    Disjoint
      (Set.range (puncturedLocalCuspQuotientMap W))
      (Set.range (A.orderThreePuncturedCollarToCentralFamily S.orderThree.sourceData)) := by
  rw [Set.disjoint_left]
  rintro p ⟨q₀, rfl⟩ ⟨q₃, hp⟩
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := A.totalSpaceCharts
  let _ := regularFamilyDeckAction A.periods
  have hcusp : puncturedLocalCuspQuotientMap W q₀ ∈ puncturedGlobalCuspCollar W := by
    rw [← puncturedLocalCuspQuotientMap_range W]
    exact ⟨q₀, rfl⟩
  change puncturedLocalCuspQuotientMap W q₀ ∈
    quotientProjection '' regularCuspFamilyRegion W at hcusp
  obtain ⟨y, hy, hyq⟩ := hcusp
  have hglobal : (Quotient.mk _ y : A.CentralFamily) =
      A.orderThreePuncturedCollarToCentralFamily S.orderThree.sourceData q₃ := by
    simpa only [quotientProjection.eq_def] using hyq.trans hp.symm
  change (Quotient.mk _ y : A.CentralFamily) =
    orderThreeLinearCollarToPuncturedGlobalFamily A.periods hproper hsource
      S.orderThree.sourceData
        (orderThreePuncturedCollarQuotientHomeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph hsource S.orderThree.radius q₃) at hglobal
  generalize hQ₃ : orderThreePuncturedCollarQuotientHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph hsource S.orderThree.radius q₃ = Q₃ at hglobal
  induction Q₃ using Quotient.inductionOn with
  | _ x₃ =>
    rw [orderThreeLinearCollarToPuncturedGlobalFamily_mk] at hglobal
    obtain ⟨g, hg⟩ := regularBase_orbit_of_global_eq A.periods hglobal
    rw [orderThreeCollarToRegular_base A.periods hproper hsource
      S.orderThree.sourceData] at hg
    change (regularTotalSpaceBase A.periods y).1 ∈
      normalizedCuspRegion A.cuspCoordinate W.localWitness.radius at hy
    have hx₃ : ‖(orderThreeCayleyHomeomorph
        (familyTotalSpaceBase A.periods x₃) : ℂ)‖ < S.orderThree.radius := by
      simpa only [orderThreeLinearPuncturedCarrier.eq_def,
        orderThreePuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
        orderThreeFamilyRadius.eq_def] using x₃.property.2
    apply S.orderThree_avoids_cusp (familyTotalSpaceBase A.periods x₃) hx₃
    apply subset_closure
    apply Set.mem_iUnion.mpr
    refine ⟨g⁻¹, (Set.mem_image _ _ _).mpr ⟨(regularTotalSpaceBase A.periods y).1,
      hy, ?_⟩⟩
    calc
      U.sourceAction g⁻¹ • (regularTotalSpaceBase A.periods y).1 =
          U.sourceAction g⁻¹ •
            (U.sourceAction g • familyTotalSpaceBase A.periods x₃) :=
        congrArg _ hg.symm
      _ = familyTotalSpaceBase A.periods x₃ := by
        rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

/-- The cusp collar image is disjoint from the simultaneously shrunk order-four image. -/
public theorem cusp_orderFour_centralRanges_disjoint (S : A.CollarSeparationData W) :
    Disjoint
      (Set.range (puncturedLocalCuspQuotientMap W))
      (Set.range (A.orderFourPuncturedCollarToCentralFamily S.orderFour.sourceData)) := by
  rw [Set.disjoint_left]
  rintro p ⟨q₀, rfl⟩ ⟨q₄, hp⟩
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := A.totalSpaceCharts
  let _ := regularFamilyDeckAction A.periods
  have hcusp : puncturedLocalCuspQuotientMap W q₀ ∈ puncturedGlobalCuspCollar W := by
    rw [← puncturedLocalCuspQuotientMap_range W]
    exact ⟨q₀, rfl⟩
  change puncturedLocalCuspQuotientMap W q₀ ∈
    quotientProjection '' regularCuspFamilyRegion W at hcusp
  obtain ⟨y, hy, hyq⟩ := hcusp
  have hglobal : (Quotient.mk _ y : A.CentralFamily) =
      A.orderFourPuncturedCollarToCentralFamily S.orderFour.sourceData q₄ := by
    simpa only [quotientProjection.eq_def] using hyq.trans hp.symm
  change (Quotient.mk _ y : A.CentralFamily) =
    orderFourLinearCollarToPuncturedGlobalFamily A.periods hproper hsource
      S.orderFour.sourceData
        (orderFourPuncturedCollarQuotientHomeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph hsource S.orderFour.radius q₄) at hglobal
  generalize hQ₄ : orderFourPuncturedCollarQuotientHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph hsource S.orderFour.radius q₄ = Q₄ at hglobal
  induction Q₄ using Quotient.inductionOn with
  | _ x₄ =>
    rw [orderFourLinearCollarToPuncturedGlobalFamily_mk] at hglobal
    obtain ⟨g, hg⟩ := regularBase_orbit_of_global_eq A.periods hglobal
    rw [orderFourCollarToRegular_base A.periods hproper hsource
      S.orderFour.sourceData] at hg
    change (regularTotalSpaceBase A.periods y).1 ∈
      normalizedCuspRegion A.cuspCoordinate W.localWitness.radius at hy
    have hx₄ : ‖(orderFourCayleyHomeomorph
        (familyTotalSpaceBase A.periods x₄) : ℂ)‖ < S.orderFour.radius := by
      simpa only [orderFourLinearPuncturedCarrier.eq_def,
        orderFourPuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
        orderFourFamilyRadius.eq_def] using x₄.property.2
    apply S.orderFour_avoids_cusp (familyTotalSpaceBase A.periods x₄) hx₄
    apply subset_closure
    apply Set.mem_iUnion.mpr
    refine ⟨g⁻¹, (Set.mem_image _ _ _).mpr ⟨(regularTotalSpaceBase A.periods y).1,
      hy, ?_⟩⟩
    calc
      U.sourceAction g⁻¹ • (regularTotalSpaceBase A.periods y).1 =
          U.sourceAction g⁻¹ •
            (U.sourceAction g • familyTotalSpaceBase A.periods x₄) :=
        congrArg _ hg.symm
      _ = familyTotalSpaceBase A.periods x₄ := by
        rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

end CollarSeparationData

/-- A fixed simultaneous choice of the three pairwise separated collar radii. -/
@[expose] public noncomputable def collarSeparationData :
    A.CollarSeparationData A.actualPuncturedCuspWitness :=
  Classical.choice (A.exists_collarSeparationData A.actualPuncturedCuspWitness)

end PaperAnalyticData

end

end SphereSixComplex.Geometry
