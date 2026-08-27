module

public import SphereSixComplex.Topology.PaperSectionSevenAffineRegularLiftCarriers

/-!
# The order-four affine overlap quotient identification

The orbit quotient of the order-four affine disc lift is identified with its open image in the
actual central family, and that image is computed to be the exact affine coordinate disc region.
Reducing along the fixed central-region quotient homeomorphism then shows that the order-four
overlap quotient identification exists exactly when the actual order-four star overlap is, on the
nose, an affine coordinate disc region.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open GlobalTorusFamily TorusFamily
open EquivariantQuotientHomeomorph
open SphereSixComplex.OpenUnionHomotopy

variable (A : PaperAnalyticData)

/-- The order-four lifted disc quotient mapped into the actual central family. -/
public noncomputable def orderFourAffineDiscLiftQuotientToCentralFamily (r : ℝ) :
    Quotient (orbitRelOf (A.orderFourAffineDiscLiftAction r)) → A.CentralFamily :=
  restrictedOrbitQuotientInclusion (regularFamilyDeckAction A.periods)
    (A.orderFourAffineDiscLiftCarrier r)

/-- The disc lift quotient is exactly the affine coordinate disc region of the central family. -/
public theorem range_orderFourAffineDiscLiftQuotientToCentralFamily (r : ℝ) :
    Set.range (A.orderFourAffineDiscLiftQuotientToCentralFamily r) =
      {q : A.CentralFamily | ‖(A.centralFamilyCoordinate q).1 - 1‖ < r} := by
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

/-- The disc lift quotient inclusion is compatible with the two central-family inclusions. -/
public theorem orderFourAffineHalfPlaneLiftQuotientToCentralFamily_discInclusion
    {r : ℝ} (hr : r ≤ 1 - 1 / 3)
    (q : Quotient (orbitRelOf (A.orderFourAffineDiscLiftAction r))) :
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
        (A.orderFourAffineDiscLiftQuotientInclusion hr q) =
      A.orderFourAffineDiscLiftQuotientToCentralFamily r q := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- Undoing the half-plane range homeomorphism returns the underlying central-family point. -/
public theorem orderFourAffineHalfPlaneLiftQuotientToCentralFamily_homeomorphRange_symm
    (w : Set.range A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily) :
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
        (A.orderFourAffineHalfPlaneLiftQuotientHomeomorphRange.symm w) =
      (w : A.CentralFamily) := by
  have h := Topology.IsEmbedding.toHomeomorph_apply_coe
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding.isEmbedding
    (A.orderFourAffineHalfPlaneLiftQuotientHomeomorphRange.symm w)
  exact h.symm.trans (congrArg Subtype.val
    (A.orderFourAffineHalfPlaneLiftQuotientHomeomorphRange.apply_symm_apply w))

/-- The fixed central-region quotient homeomorphism is the identity in central-family
coordinates. -/
public theorem orderFourAffineHalfPlaneLiftQuotientToCentralFamily_centralRegionQuotient
    (x : A.sectionSevenEllipticCentralImage)
    (hx : (1 : ℝ) / 3 < A.sectionSevenEllipticCentralHeight x) :
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
        (A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph ⟨x.1, ⟨x, hx, rfl⟩⟩) =
      A.sectionSevenEllipticCentralImageHomeomorph x := by
  have h1 : (centralHeightUpperRegionHomeomorph A A.sectionSevenEllipticCentralHeight
      (1 / 3 : ℝ)).symm ⟨x.1, ⟨x, hx, rfl⟩⟩ = ⟨x, hx⟩ := by
    rw [Homeomorph.symm_apply_eq]
    rfl
  simp only [sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph,
    Homeomorph.trans_apply,
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_homeomorphRange_symm, h1]
  rfl


/-- The image of the order-four disc lift quotient inside the half-plane lift quotient is exactly
the affine coordinate disc region. -/
public theorem range_orderFourAffineDiscLiftQuotientInclusion {r : ℝ} (hr : r ≤ 1 - 1 / 3) :
    Set.range (A.orderFourAffineDiscLiftQuotientInclusion hr) =
      {q : Quotient (orbitRelOf A.orderFourAffineHalfPlaneLiftAction) |
        ‖(A.centralFamilyCoordinate
          (A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily q)).1 - 1‖ < r} := by
  have hinj : Function.Injective A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily :=
    restrictedOrbitQuotientInclusion_injective _ _
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    have hmem : A.orderFourAffineDiscLiftQuotientToCentralFamily r p ∈
        Set.range (A.orderFourAffineDiscLiftQuotientToCentralFamily r) := ⟨p, rfl⟩
    rw [A.range_orderFourAffineDiscLiftQuotientToCentralFamily] at hmem
    show ‖(A.centralFamilyCoordinate
      (A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily _)).1 - 1‖ < r
    rw [A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_discInclusion hr p]
    exact hmem
  · intro hq
    have hmem : A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily q ∈
        Set.range (A.orderFourAffineDiscLiftQuotientToCentralFamily r) := by
      rw [A.range_orderFourAffineDiscLiftQuotientToCentralFamily]
      exact hq
    obtain ⟨p, hp⟩ := hmem
    refine ⟨p, hinj ?_⟩
    rw [A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_discInclusion hr p, hp]

/-- The order-four disc lift quotient is a subspace of the half-plane lift quotient. -/
public theorem orderFourAffineDiscLiftQuotientInclusion_isEmbedding
    {r : ℝ} (hr : r ≤ 1 - 1 / 3) :
    Topology.IsEmbedding (A.orderFourAffineDiscLiftQuotientInclusion hr) := by
  refine Topology.IsEmbedding.of_comp (f := A.orderFourAffineDiscLiftQuotientInclusion hr)
    (g := A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily)
    (A.orderFourAffineDiscLiftQuotientInclusion_continuous hr)
    (restrictedOrbitQuotientInclusion_continuous _ _) ?_
  have h : A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily ∘
      A.orderFourAffineDiscLiftQuotientInclusion hr =
      A.orderFourAffineDiscLiftQuotientToCentralFamily r :=
    funext fun p ↦ A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_discInclusion hr p
  rw [h]
  exact (restrictedOrbitQuotientInclusion_isOpenEmbedding _ _
    A.regularFamilyDeckAction_continuous).isEmbedding


/-- The order-four overlap quotient identification, given the exact point-set description of the
actual order-four star overlap as an affine coordinate disc region. -/
public theorem orderFourOverlapQuotientIdentification_nonempty_of_overlap_eq
    {n r : ℝ} (hn : 0 < n) (hnr : n < r) (hr : r ≤ 1 - 1 / 3)
    (hoverlap : A.sectionSevenOrderFourFillingImage ∩
        A.sectionSevenAffineOrderFourCentralRegion =
      Subtype.val '' {z : A.sectionSevenEllipticCentralImage |
        ‖(A.sectionSevenEllipticCentralCoordinate z).1 - 1‖ < r}) :
    Nonempty A.SectionSevenAffineOrderFourOverlapQuotientIdentification := by
  have key : ∀ v : ↥A.sectionSevenAffineOrderFourCentralRegion,
      v.1 ∈ A.sectionSevenOrderFourFillingImage ↔
        A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph v ∈
          Set.range (A.orderFourAffineDiscLiftQuotientInclusion hr) := by
    rintro ⟨y, hy⟩
    obtain ⟨z, hz, rfl⟩ := hy
    rw [A.range_orderFourAffineDiscLiftQuotientInclusion hr]
    show _ ↔ ‖(A.centralFamilyCoordinate
      (A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
        (A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph ⟨z.1, _⟩))).1 - 1‖ < r
    rw [A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_centralRegionQuotient z hz]
    constructor
    · intro hmem
      have : (z : A.SectionSevenEllipticInterior) ∈
          A.sectionSevenOrderFourFillingImage ∩
            A.sectionSevenAffineOrderFourCentralRegion := ⟨hmem, ⟨z, hz, rfl⟩⟩
      rw [hoverlap] at this
      obtain ⟨w, hw, hwz⟩ := this
      have : w = z := Subtype.ext hwz
      subst this
      exact hw
    · intro hlt
      have : (z : A.SectionSevenEllipticInterior) ∈
          A.sectionSevenOrderFourFillingImage ∩
            A.sectionSevenAffineOrderFourCentralRegion := by
        rw [hoverlap]
        exact ⟨z, hlt, rfl⟩
      exact this.1
  let e₁ : ↥(A.sectionSevenOrderFourFillingImage ∩
      A.sectionSevenAffineOrderFourCentralRegion) ≃ₜ
      {v : ↥A.sectionSevenAffineOrderFourCentralRegion //
        v.1 ∈ A.sectionSevenOrderFourFillingImage} :=
    { toFun := fun x ↦ ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      invFun := fun v ↦ ⟨v.1.1, ⟨v.2, v.1.2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let e₂ := A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph.subtype key
  let e₃ := (A.orderFourAffineDiscLiftQuotientInclusion_isEmbedding hr).toHomeomorph
  refine ⟨{
    normalizationRadius := n
    affineDiscRadius := r
    normalizationRadius_pos := hn
    normalizationRadius_lt_disc := hnr
    affineDiscRadius_le_halfPlane := hr
    overlapModel := e₁.trans (e₂.trans e₃.symm)
    commutes := ?_ }⟩
  funext x
  show A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph ⟨x.1, x.2.2⟩ =
    A.orderFourAffineDiscLiftQuotientInclusion hr (e₃.symm (e₂ (e₁ x)))
  have h := Topology.IsEmbedding.toHomeomorph_apply_coe
    (A.orderFourAffineDiscLiftQuotientInclusion_isEmbedding hr) (e₃.symm (e₂ (e₁ x)))
  rw [← h]
  exact (congrArg Subtype.val (e₃.apply_symm_apply (e₂ (e₁ x)))).symm


/-- Conversely, any order-four overlap quotient identification forces the actual order-four star
overlap to be exactly the affine coordinate disc region of its own radius. -/
public theorem SectionSevenAffineOrderFourOverlapQuotientIdentification.overlap_eq
    (Q : A.SectionSevenAffineOrderFourOverlapQuotientIdentification) :
    A.sectionSevenOrderFourFillingImage ∩ A.sectionSevenAffineOrderFourCentralRegion =
      Subtype.val '' {z : A.sectionSevenEllipticCentralImage |
        ‖(A.sectionSevenEllipticCentralCoordinate z).1 - 1‖ < Q.affineDiscRadius} := by
  have hmemIff : ∀ (z : A.sectionSevenEllipticCentralImage)
      (hz : (1 : ℝ) / 3 < A.sectionSevenEllipticCentralHeight z),
      (A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph ⟨z.1, ⟨z, hz, rfl⟩⟩ ∈
        Set.range (A.orderFourAffineDiscLiftQuotientInclusion
          Q.affineDiscRadius_le_halfPlane)) ↔
        ‖(A.sectionSevenEllipticCentralCoordinate z).1 - 1‖ < Q.affineDiscRadius := by
    intro z hz
    rw [A.range_orderFourAffineDiscLiftQuotientInclusion Q.affineDiscRadius_le_halfPlane]
    show ‖(A.centralFamilyCoordinate
      (A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
        (A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph
          ⟨z.1, ⟨z, hz, rfl⟩⟩))).1 - 1‖ < Q.affineDiscRadius ↔ _
    rw [A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_centralRegionQuotient z hz]
    exact Iff.rfl
  ext y
  constructor
  · rintro ⟨hyU, hyV⟩
    obtain ⟨z, hz, rfl⟩ := hyV
    refine ⟨z, (hmemIff z hz).mp ⟨Q.overlapModel ⟨z.1, ⟨hyU, ⟨z, hz, rfl⟩⟩⟩, ?_⟩, rfl⟩
    exact (congrFun Q.commutes ⟨z.1, ⟨hyU, ⟨z, hz, rfl⟩⟩⟩).symm
  · rintro ⟨z, hz, rfl⟩
    have hre : (1 : ℝ) / 3 < A.sectionSevenEllipticCentralHeight z := by
      have habs := Complex.abs_re_le_norm
        ((A.sectionSevenEllipticCentralCoordinate z).1 - 1)
      simp only [Complex.sub_re, Complex.one_re] at habs
      have hlow : -‖(A.sectionSevenEllipticCentralCoordinate z).1 - 1‖ ≤
          (A.sectionSevenEllipticCentralCoordinate z).1.re - 1 := (abs_le.mp habs).1
      have hbound := Q.affineDiscRadius_le_halfPlane
      show (1 : ℝ) / 3 < (A.sectionSevenEllipticCentralCoordinate z).1.re
      have hlt : ‖(A.sectionSevenEllipticCentralCoordinate z).1 - 1‖ < Q.affineDiscRadius := hz
      norm_num at hbound ⊢
      linarith
    obtain ⟨p, hp⟩ := (hmemIff z hre).mpr hz
    refine ⟨?_, ⟨z, hre, rfl⟩⟩
    have hx := congrFun Q.commutes (Q.overlapModel.symm p)
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply] at hx
    have hval : (⟨(Q.overlapModel.symm p).1, (Q.overlapModel.symm p).2.2⟩ :
        ↥A.sectionSevenAffineOrderFourCentralRegion) = ⟨z.1, ⟨z, hre, rfl⟩⟩ :=
      A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph.injective
        (hx.trans hp)
    have : (Q.overlapModel.symm p).1 = (z : A.SectionSevenEllipticInterior) :=
      congrArg Subtype.val hval
    rw [← this]
    exact (Q.overlapModel.symm p).2.1

end SphereSixComplex.Geometry.PaperAnalyticData

end
