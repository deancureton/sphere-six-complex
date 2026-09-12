module

public import SphereSixComplex.Prerequisites.Topology.EquivariantHomotopyEquivalenceDescent
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineSideHomotopyEquivalence
public import SphereSixComplex.Prerequisites.Topology.RestrictedOrbitQuotientOpenEmbedding

/-!
# Regular-cover lifts of the affine side regions

The affine radial homotopy lives most naturally on the regular upper-half-plane cover.  This
file defines the four exact invariant carriers lying over the order-three and order-four
punctured disc and half-plane regions.  Their orbit quotients retain the full triangle-group
monodromy of the torus family.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

open GlobalTorusFamily TorusFamily
open EquivariantQuotientHomeomorph
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.OpenUnionHomotopy

variable (A : AnalyticData)

/-- The regular total-space lift of the order-three punctured affine disc. -/
public noncomputable def orderThreeAffineDiscLiftCarrier (r : ℝ) :
    InvariantOpenCarrier (regularFamilyDeckAction A.periods) where
  carrier := {q | ‖(A.regularCoordinate
    (regularTotalSpaceBase A.periods q)).1‖ < r}
  isOpen_carrier := by
    apply isOpen_lt
    · exact continuous_norm.comp
        (continuous_subtype_val.comp
          (A.regularCoordinate_isLocalHomeomorph.continuous.comp
            (regularTotalSpaceBase_continuous A.periods)))
    · exact continuous_const
  invariant g q hq := by
    change ‖(A.regularCoordinate
      (regularTotalSpaceBase A.periods (regularFamilyDeckMap A.periods g q))).1‖ < r
    rw [regularTotalSpaceBase_familyDeckMap]
    change ‖A.modular.sourceCoordinate.coordinate
      (fuchsianSourceAction g • (regularTotalSpaceBase A.periods q).1)‖ < r
    rw [A.modular.sourceCoordinate.coordinate_invariant]
    exact hq

/-- The regular total-space lift of the order-three punctured left half-plane. -/
public noncomputable def orderThreeAffineHalfPlaneLiftCarrier :
    InvariantOpenCarrier (regularFamilyDeckAction A.periods) where
  carrier := {q | (A.regularCoordinate
    (regularTotalSpaceBase A.periods q)).1.re < 2 / 3}
  isOpen_carrier := by
    apply isOpen_lt
    · exact Complex.continuous_re.comp
        (continuous_subtype_val.comp
          (A.regularCoordinate_isLocalHomeomorph.continuous.comp
            (regularTotalSpaceBase_continuous A.periods)))
    · exact continuous_const
  invariant g q hq := by
    change (A.regularCoordinate
      (regularTotalSpaceBase A.periods (regularFamilyDeckMap A.periods g q))).1.re < 2 / 3
    rw [regularTotalSpaceBase_familyDeckMap]
    change (A.modular.sourceCoordinate.coordinate
      (fuchsianSourceAction g • (regularTotalSpaceBase A.periods q).1)).re < 2 / 3
    rw [A.modular.sourceCoordinate.coordinate_invariant]
    exact hq

/-- The regular total-space lift of the order-four punctured affine disc at one. -/
public noncomputable def orderFourAffineDiscLiftCarrier (r : ℝ) :
    InvariantOpenCarrier (regularFamilyDeckAction A.periods) where
  carrier := {q | ‖(A.regularCoordinate
    (regularTotalSpaceBase A.periods q)).1 - 1‖ < r}
  isOpen_carrier := by
    apply isOpen_lt
    · exact continuous_norm.comp
        ((continuous_subtype_val.comp
          (A.regularCoordinate_isLocalHomeomorph.continuous.comp
            (regularTotalSpaceBase_continuous A.periods))).sub continuous_const)
    · exact continuous_const
  invariant g q hq := by
    change ‖(A.regularCoordinate
      (regularTotalSpaceBase A.periods (regularFamilyDeckMap A.periods g q))).1 - 1‖ < r
    rw [regularTotalSpaceBase_familyDeckMap]
    change ‖A.modular.sourceCoordinate.coordinate
      (fuchsianSourceAction g • (regularTotalSpaceBase A.periods q).1) - 1‖ < r
    rw [A.modular.sourceCoordinate.coordinate_invariant]
    exact hq

/-- The regular total-space lift of the order-four punctured right half-plane. -/
public noncomputable def orderFourAffineHalfPlaneLiftCarrier :
    InvariantOpenCarrier (regularFamilyDeckAction A.periods) where
  carrier := {q | 1 / 3 < (A.regularCoordinate
    (regularTotalSpaceBase A.periods q)).1.re}
  isOpen_carrier := by
    apply isOpen_lt
    · exact continuous_const
    · exact Complex.continuous_re.comp
        (continuous_subtype_val.comp
          (A.regularCoordinate_isLocalHomeomorph.continuous.comp
            (regularTotalSpaceBase_continuous A.periods)))
  invariant g q hq := by
    change 1 / 3 < (A.regularCoordinate
      (regularTotalSpaceBase A.periods (regularFamilyDeckMap A.periods g q))).1.re
    rw [regularTotalSpaceBase_familyDeckMap]
    change 1 / 3 < (A.modular.sourceCoordinate.coordinate
      (fuchsianSourceAction g • (regularTotalSpaceBase A.periods q).1)).re
    rw [A.modular.sourceCoordinate.coordinate_invariant]
    exact hq

public theorem orderThreeAffineDiscLiftCarrier_subset_halfPlane
    {r : ℝ} (hr : r ≤ 2 / 3) :
    (A.orderThreeAffineDiscLiftCarrier r).carrier ⊆
      A.orderThreeAffineHalfPlaneLiftCarrier.carrier := by
  intro q hq
  exact (Complex.re_le_norm _).trans_lt (hq.trans_le hr)

public theorem orderFourAffineDiscLiftCarrier_subset_halfPlane
    {r : ℝ} (hr : r ≤ 1 - 1 / 3) :
    (A.orderFourAffineDiscLiftCarrier r).carrier ⊆
      A.orderFourAffineHalfPlaneLiftCarrier.carrier := by
  intro q hq
  change ‖(A.regularCoordinate
    (regularTotalSpaceBase A.periods q)).1 - 1‖ < r at hq
  have hre := Complex.abs_re_le_norm
    ((A.regularCoordinate (regularTotalSpaceBase A.periods q)).1 - 1)
  simp only [Complex.sub_re, Complex.one_re] at hre
  have hlower : -‖(A.regularCoordinate
      (regularTotalSpaceBase A.periods q)).1 - 1‖ ≤
      (A.regularCoordinate (regularTotalSpaceBase A.periods q)).1.re - 1 :=
    (abs_le.mp hre).1
  have hnorm : ‖(A.regularCoordinate
      (regularTotalSpaceBase A.periods q)).1 - 1‖ < 2 / 3 := by
    norm_num at hr ⊢
    exact hq.trans_le hr
  change 1 / 3 < (A.regularCoordinate
    (regularTotalSpaceBase A.periods q)).1.re
  norm_num at ⊢
  linarith

/-- Literal inclusion of the order-three disc lift into its half-plane lift. -/
public def orderThreeAffineDiscLiftInclusion {r : ℝ} (hr : r ≤ 2 / 3) :
    (A.orderThreeAffineDiscLiftCarrier r).carrier →
      A.orderThreeAffineHalfPlaneLiftCarrier.carrier :=
  fun q ↦ ⟨q.1, A.orderThreeAffineDiscLiftCarrier_subset_halfPlane hr q.2⟩

/-- Literal inclusion of the order-four disc lift into its half-plane lift. -/
public def orderFourAffineDiscLiftInclusion {r : ℝ} (hr : r ≤ 1 - 1 / 3) :
    (A.orderFourAffineDiscLiftCarrier r).carrier →
      A.orderFourAffineHalfPlaneLiftCarrier.carrier :=
  fun q ↦ ⟨q.1, A.orderFourAffineDiscLiftCarrier_subset_halfPlane hr q.2⟩

public theorem orderThreeAffineDiscLiftInclusion_continuous {r : ℝ} (hr : r ≤ 2 / 3) :
    Continuous (A.orderThreeAffineDiscLiftInclusion hr) :=
  continuous_subtype_val.subtype_mk _


@[instance_reducible] public noncomputable def orderThreeAffineDiscLiftAction (r : ℝ) :=
  restrictedMulAction (regularFamilyDeckAction A.periods)
    (A.orderThreeAffineDiscLiftCarrier r)

@[instance_reducible] public noncomputable def orderThreeAffineHalfPlaneLiftAction :=
  restrictedMulAction (regularFamilyDeckAction A.periods)
    A.orderThreeAffineHalfPlaneLiftCarrier

@[instance_reducible] public noncomputable def orderFourAffineDiscLiftAction (r : ℝ) :=
  restrictedMulAction (regularFamilyDeckAction A.periods)
    (A.orderFourAffineDiscLiftCarrier r)

@[instance_reducible] public noncomputable def orderFourAffineHalfPlaneLiftAction :=
  restrictedMulAction (regularFamilyDeckAction A.periods)
    A.orderFourAffineHalfPlaneLiftCarrier

public theorem orderThreeAffineDiscLiftAction_continuous (r : ℝ) :
    letI := A.orderThreeAffineDiscLiftAction r
    ContinuousConstSMul Delta (A.orderThreeAffineDiscLiftCarrier r).carrier := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  exact restrictedContinuousConstSMul _ _
    (regularFamilyDeckAction_continuousConstSMul A.periods hproper)

public theorem orderThreeAffineHalfPlaneLiftAction_continuous :
    letI := A.orderThreeAffineHalfPlaneLiftAction
    ContinuousConstSMul Delta A.orderThreeAffineHalfPlaneLiftCarrier.carrier := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  exact restrictedContinuousConstSMul _ _
    (regularFamilyDeckAction_continuousConstSMul A.periods hproper)

public theorem orderFourAffineDiscLiftAction_continuous (r : ℝ) :
    letI := A.orderFourAffineDiscLiftAction r
    ContinuousConstSMul Delta (A.orderFourAffineDiscLiftCarrier r).carrier := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  exact restrictedContinuousConstSMul _ _
    (regularFamilyDeckAction_continuousConstSMul A.periods hproper)

public theorem orderFourAffineHalfPlaneLiftAction_continuous :
    letI := A.orderFourAffineHalfPlaneLiftAction
    ContinuousConstSMul Delta A.orderFourAffineHalfPlaneLiftCarrier.carrier := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  exact restrictedContinuousConstSMul _ _
    (regularFamilyDeckAction_continuousConstSMul A.periods hproper)

/-- The literal order-three lift inclusion descended to the restricted orbit quotients. -/
public theorem orderThreeAffineDiscLiftInclusion_respects
    {r : ℝ} (hr : r ≤ 2 / 3) :
    ∀ x y,
      orbitRelOf (A.orderThreeAffineDiscLiftAction r) x y →
        orbitRelOf A.orderThreeAffineHalfPlaneLiftAction
          (A.orderThreeAffineDiscLiftInclusion hr x)
          (A.orderThreeAffineDiscLiftInclusion hr y) := by
  intro x y hxy
  change ∃ g : Delta,
    actionMap (A.orderThreeAffineDiscLiftAction r) g y = x at hxy
  change ∃ g : Delta,
    actionMap A.orderThreeAffineHalfPlaneLiftAction g
      (A.orderThreeAffineDiscLiftInclusion hr y) =
        A.orderThreeAffineDiscLiftInclusion hr x
  obtain ⟨g, hg⟩ := hxy
  refine ⟨g, ?_⟩
  change restrictedActionMap A.orderThreeAffineHalfPlaneLiftCarrier g
      (A.orderThreeAffineDiscLiftInclusion hr y) =
    A.orderThreeAffineDiscLiftInclusion hr x
  apply Subtype.ext
  change actionMap (regularFamilyDeckAction A.periods) g y.1 = x.1
  change restrictedActionMap (A.orderThreeAffineDiscLiftCarrier r) g y = x at hg
  exact congrArg Subtype.val hg

public noncomputable def orderThreeAffineDiscLiftQuotientInclusion
    {r : ℝ} (hr : r ≤ 2 / 3) :
    Quotient (orbitRelOf (A.orderThreeAffineDiscLiftAction r)) →
      Quotient (orbitRelOf A.orderThreeAffineHalfPlaneLiftAction) :=
  Quotient.map (A.orderThreeAffineDiscLiftInclusion hr)
    (A.orderThreeAffineDiscLiftInclusion_respects hr)

/-- The literal order-four lift inclusion descended to the restricted orbit quotients. -/
public theorem orderFourAffineDiscLiftInclusion_respects
    {r : ℝ} (hr : r ≤ 1 - 1 / 3) :
    ∀ x y,
      orbitRelOf (A.orderFourAffineDiscLiftAction r) x y →
        orbitRelOf A.orderFourAffineHalfPlaneLiftAction
          (A.orderFourAffineDiscLiftInclusion hr x)
          (A.orderFourAffineDiscLiftInclusion hr y) := by
  intro x y hxy
  change ∃ g : Delta,
    actionMap (A.orderFourAffineDiscLiftAction r) g y = x at hxy
  change ∃ g : Delta,
    actionMap A.orderFourAffineHalfPlaneLiftAction g
      (A.orderFourAffineDiscLiftInclusion hr y) =
        A.orderFourAffineDiscLiftInclusion hr x
  obtain ⟨g, hg⟩ := hxy
  refine ⟨g, ?_⟩
  change restrictedActionMap A.orderFourAffineHalfPlaneLiftCarrier g
      (A.orderFourAffineDiscLiftInclusion hr y) =
    A.orderFourAffineDiscLiftInclusion hr x
  apply Subtype.ext
  change actionMap (regularFamilyDeckAction A.periods) g y.1 = x.1
  change restrictedActionMap (A.orderFourAffineDiscLiftCarrier r) g y = x at hg
  exact congrArg Subtype.val hg

public noncomputable def orderFourAffineDiscLiftQuotientInclusion
    {r : ℝ} (hr : r ≤ 1 - 1 / 3) :
    Quotient (orbitRelOf (A.orderFourAffineDiscLiftAction r)) →
      Quotient (orbitRelOf A.orderFourAffineHalfPlaneLiftAction) :=
  Quotient.map (A.orderFourAffineDiscLiftInclusion hr)
    (A.orderFourAffineDiscLiftInclusion_respects hr)



public theorem regularFamilyDeckAction_continuous :
    letI := regularFamilyDeckAction A.periods
    ContinuousConstSMul Delta (RegularTotalSpace A.periods) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  exact regularFamilyDeckAction_continuousConstSMul A.periods hproper

/-- The order-three lifted half-plane quotient mapped into the actual central family. -/
public noncomputable def orderThreeAffineHalfPlaneLiftQuotientToCentralFamily :
    Quotient (orbitRelOf A.orderThreeAffineHalfPlaneLiftAction) → A.CentralFamily :=
  restrictedOrbitQuotientInclusion (regularFamilyDeckAction A.periods)
    A.orderThreeAffineHalfPlaneLiftCarrier

/-- The order-four lifted half-plane quotient mapped into the actual central family. -/
public noncomputable def orderFourAffineHalfPlaneLiftQuotientToCentralFamily :
    Quotient (orbitRelOf A.orderFourAffineHalfPlaneLiftAction) → A.CentralFamily :=
  restrictedOrbitQuotientInclusion (regularFamilyDeckAction A.periods)
    A.orderFourAffineHalfPlaneLiftCarrier

public theorem orderThreeAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding :
    IsOpenEmbedding A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily :=
  restrictedOrbitQuotientInclusion_isOpenEmbedding _ _ A.regularFamilyDeckAction_continuous

public theorem orderFourAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding :
    IsOpenEmbedding A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily :=
  restrictedOrbitQuotientInclusion_isOpenEmbedding _ _ A.regularFamilyDeckAction_continuous

/-- The order-three lifted half-plane quotient is exactly its open image in the actual central
family. -/
public noncomputable def orderThreeAffineHalfPlaneLiftQuotientHomeomorphRange :
    Quotient (orbitRelOf A.orderThreeAffineHalfPlaneLiftAction) ≃ₜ
      Set.range A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily :=
  A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding.isEmbedding.toHomeomorph

/-- The order-four lifted half-plane quotient is exactly its open image in the actual central
family. -/
public noncomputable def orderFourAffineHalfPlaneLiftQuotientHomeomorphRange :
    Quotient (orbitRelOf A.orderFourAffineHalfPlaneLiftAction) ≃ₜ
      Set.range A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily :=
  A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding.isEmbedding.toHomeomorph

public theorem range_orderThreeAffineHalfPlaneLiftQuotientToCentralFamily :
    Set.range A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily =
      {q : A.CentralFamily | (A.centralFamilyCoordinate q).1.re < 2 / 3} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.inductionOn with
    | _ x => exact x.2
  · intro hq
    induction q using Quotient.inductionOn with
    | _ q =>
      refine ⟨Quotient.mk _ ⟨q, ?_⟩, rfl⟩
      exact hq

public theorem range_orderFourAffineHalfPlaneLiftQuotientToCentralFamily :
    Set.range A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily =
      {q : A.CentralFamily | 1 / 3 < (A.centralFamilyCoordinate q).1.re} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.inductionOn with
    | _ x => exact x.2
  · intro hq
    induction q using Quotient.inductionOn with
    | _ q =>
      refine ⟨Quotient.mk _ ⟨q, ?_⟩, rfl⟩
      exact hq

public noncomputable def centralHeightLowerRegionHomeomorph
    (height : A.ellipticCentralImage → ℝ) (upper : ℝ) :
    {x : A.ellipticCentralImage | height x < upper} ≃ₜ
      ↥(centralHeightLowerRegion height upper) :=
  ((IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).toHomeomorph).trans
    (Homeomorph.setCongr (by
      ext x
      simp [centralHeightLowerRegion]))

public noncomputable def centralHeightUpperRegionHomeomorph
    (height : A.ellipticCentralImage → ℝ) (lower : ℝ) :
    {x : A.ellipticCentralImage | lower < height x} ≃ₜ
      ↥(centralHeightUpperRegion height lower) :=
  ((IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).toHomeomorph).trans
    (Homeomorph.setCongr (by
      ext x
      simp [centralHeightUpperRegion]))

/-- The actual order-three central region, expressed as the quotient of its full-deck-action
half-plane lift. -/
public noncomputable def affineOrderThreeCentralRegionQuotientHomeomorph :
    A.affineOrderThreeCentralRegion ≃ₜ
      Quotient (orbitRelOf A.orderThreeAffineHalfPlaneLiftAction) :=
  (centralHeightLowerRegionHomeomorph A A.ellipticCentralHeight (2 / 3 : ℝ)).symm |>.trans
    (A.ellipticCentralImageHomeomorph.subtype fun _ ↦ Iff.rfl) |>.trans
    (Homeomorph.setCongr
      A.range_orderThreeAffineHalfPlaneLiftQuotientToCentralFamily.symm) |>.trans
    A.orderThreeAffineHalfPlaneLiftQuotientHomeomorphRange.symm

/-- The actual order-four central region, expressed as the quotient of its full-deck-action
half-plane lift. -/
public noncomputable def affineOrderFourCentralRegionQuotientHomeomorph :
    A.affineOrderFourCentralRegion ≃ₜ
      Quotient (orbitRelOf A.orderFourAffineHalfPlaneLiftAction) :=
  (centralHeightUpperRegionHomeomorph A A.ellipticCentralHeight (1 / 3 : ℝ)).symm |>.trans
    (A.ellipticCentralImageHomeomorph.subtype fun _ ↦ Iff.rfl) |>.trans
    (Homeomorph.setCongr
      A.range_orderFourAffineHalfPlaneLiftQuotientToCentralFamily.symm) |>.trans
    A.orderFourAffineHalfPlaneLiftQuotientHomeomorphRange.symm

public theorem quotientToFun_eq_orderThreeAffineDiscLiftQuotientInclusion
    {r : ℝ} (hr : r ≤ 2 / 3)
    (E : EquivariantHomotopyEquivData
      (A.orderThreeAffineDiscLiftAction r) A.orderThreeAffineHalfPlaneLiftAction)
    (hE : (E.toFun : (A.orderThreeAffineDiscLiftCarrier r).carrier →
      A.orderThreeAffineHalfPlaneLiftCarrier.carrier) =
        A.orderThreeAffineDiscLiftInclusion hr) :
    E.quotientToFun = A.orderThreeAffineDiscLiftQuotientInclusion hr := by
  funext q
  induction q using Quotient.inductionOn with
  | _ x =>
    change Quotient.mk _ (E.toFun x) =
      Quotient.mk _ (A.orderThreeAffineDiscLiftInclusion hr x)
    rw [hE]

public theorem quotientToFun_eq_orderFourAffineDiscLiftQuotientInclusion
    {r : ℝ} (hr : r ≤ 1 - 1 / 3)
    (E : EquivariantHomotopyEquivData
      (A.orderFourAffineDiscLiftAction r) A.orderFourAffineHalfPlaneLiftAction)
    (hE : (E.toFun : (A.orderFourAffineDiscLiftCarrier r).carrier →
      A.orderFourAffineHalfPlaneLiftCarrier.carrier) =
        A.orderFourAffineDiscLiftInclusion hr) :
    E.quotientToFun = A.orderFourAffineDiscLiftQuotientInclusion hr := by
  funext q
  induction q using Quotient.inductionOn with
  | _ x =>
    change Quotient.mk _ (E.toFun x) =
      Quotient.mk _ (A.orderFourAffineDiscLiftInclusion hr x)
    rw [hE]





end SphereSixComplex.Geometry.AnalyticData
