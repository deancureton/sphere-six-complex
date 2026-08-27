module

public import SphereSixComplex.Topology.PaperSectionSevenAffineRegularLiftCarriers

/-!
# The order-three affine overlap quotient identification

The order-three star overlap is the intersection of the actual order-three filling image with the
order-three affine central region.  This file builds the order-three affine disc region of the
regular central family together with its full-deck-action disc-lift quotient model, and proves
that the overlap quotient identification exists exactly when the star overlap *is* that affine
disc region.  Both directions of the equivalence are proved, so the identification is reduced to
a single point-set statement about the selected order-three collar.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open GlobalTorusFamily TorusFamily
open EquivariantQuotientHomeomorph
open SphereSixComplex.TriangleGroup
open SphereSixComplex.OpenUnionHomotopy

variable (A : PaperAnalyticData)

/-- The order-three lifted affine disc quotient mapped into the actual central family. -/
public noncomputable def orderThreeAffineDiscLiftQuotientToCentralFamily (r : ℝ) :
    Quotient (orbitRelOf (A.orderThreeAffineDiscLiftAction r)) → A.CentralFamily :=
  restrictedOrbitQuotientInclusion (regularFamilyDeckAction A.periods)
    (A.orderThreeAffineDiscLiftCarrier r)

public theorem orderThreeAffineDiscLiftQuotientToCentralFamily_isOpenEmbedding (r : ℝ) :
    IsOpenEmbedding (A.orderThreeAffineDiscLiftQuotientToCentralFamily r) :=
  restrictedOrbitQuotientInclusion_isOpenEmbedding _ _ A.regularFamilyDeckAction_continuous

/-- The order-three lifted affine disc quotient is exactly its open image in the actual central
family. -/
public noncomputable def orderThreeAffineDiscLiftQuotientHomeomorphRange (r : ℝ) :
    Quotient (orbitRelOf (A.orderThreeAffineDiscLiftAction r)) ≃ₜ
      Set.range (A.orderThreeAffineDiscLiftQuotientToCentralFamily r) :=
  (A.orderThreeAffineDiscLiftQuotientToCentralFamily_isOpenEmbedding r).isEmbedding.toHomeomorph

public theorem range_orderThreeAffineDiscLiftQuotientToCentralFamily (r : ℝ) :
    Set.range (A.orderThreeAffineDiscLiftQuotientToCentralFamily r) =
      {q : A.CentralFamily | ‖(A.centralFamilyCoordinate q).1‖ < r} := by
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

/-- The affine-coordinate radius of a point of the regular central image. -/
public noncomputable def sectionSevenEllipticCentralRadius :
    A.sectionSevenEllipticCentralImage → ℝ :=
  fun x ↦ ‖(A.sectionSevenEllipticCentralCoordinate x).1‖

/-- The affine disc region of radius `r` inside the regular central image. -/
public noncomputable def sectionSevenAffineOrderThreeDiscRegion (r : ℝ) :
    Set A.SectionSevenEllipticInterior :=
  centralHeightLowerRegion A.sectionSevenEllipticCentralRadius r

/-- The affine disc region, expressed as the quotient of its full-deck-action disc lift. -/
public noncomputable def sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph (r : ℝ) :
    ↥(A.sectionSevenAffineOrderThreeDiscRegion r) ≃ₜ
      Quotient (orbitRelOf (A.orderThreeAffineDiscLiftAction r)) :=
  (centralHeightLowerRegionHomeomorph A A.sectionSevenEllipticCentralRadius r).symm |>.trans
    (A.sectionSevenEllipticCentralImageHomeomorph.subtype fun _ ↦ Iff.rfl) |>.trans
    (Homeomorph.setCongr
      (A.range_orderThreeAffineDiscLiftQuotientToCentralFamily r).symm) |>.trans
    (A.orderThreeAffineDiscLiftQuotientHomeomorphRange r).symm

public theorem mem_centralImage_of_mem_centralHeightLowerRegion
    (height : A.sectionSevenEllipticCentralImage → ℝ) (upper : ℝ)
    {x : A.SectionSevenEllipticInterior}
    (hx : x ∈ centralHeightLowerRegion height upper) :
    x ∈ A.sectionSevenEllipticCentralImage := by
  obtain ⟨y, _, rfl⟩ := hx
  exact y.2

public theorem coe_centralHeightLowerRegionHomeomorph_symm
    (height : A.sectionSevenEllipticCentralImage → ℝ) (upper : ℝ)
    (x : ↥(centralHeightLowerRegion height upper)) :
    (((centralHeightLowerRegionHomeomorph A height upper).symm x).1).1 = x.1 :=
  congrArg Subtype.val
    ((centralHeightLowerRegionHomeomorph A height upper).apply_symm_apply x)

public theorem toCentralFamily_orderThreeAffineDiscLiftQuotientHomeomorphRange_symm (r : ℝ)
    (c : Set.range (A.orderThreeAffineDiscLiftQuotientToCentralFamily r)) :
    A.orderThreeAffineDiscLiftQuotientToCentralFamily r
        ((A.orderThreeAffineDiscLiftQuotientHomeomorphRange r).symm c) = c.1 :=
  congrArg Subtype.val
    ((A.orderThreeAffineDiscLiftQuotientHomeomorphRange r).apply_symm_apply c)

public theorem toCentralFamily_orderThreeAffineHalfPlaneLiftQuotientHomeomorphRange_symm
    (c : Set.range A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily) :
    A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily
        (A.orderThreeAffineHalfPlaneLiftQuotientHomeomorphRange.symm c) = c.1 :=
  congrArg Subtype.val
    (A.orderThreeAffineHalfPlaneLiftQuotientHomeomorphRange.apply_symm_apply c)

/-- The disc-region quotient model is compatible with the central-family coordinates. -/
public theorem toCentralFamily_sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph
    (r : ℝ) (x : ↥(A.sectionSevenAffineOrderThreeDiscRegion r)) :
    A.orderThreeAffineDiscLiftQuotientToCentralFamily r
        (A.sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph r x) =
      A.sectionSevenEllipticCentralImageHomeomorph
        ⟨x.1, A.mem_centralImage_of_mem_centralHeightLowerRegion
          A.sectionSevenEllipticCentralRadius r x.2⟩ := by
  refine (A.toCentralFamily_orderThreeAffineDiscLiftQuotientHomeomorphRange_symm r _).trans ?_
  exact congrArg A.sectionSevenEllipticCentralImageHomeomorph
    (Subtype.ext (A.coe_centralHeightLowerRegionHomeomorph_symm
      A.sectionSevenEllipticCentralRadius r x))

/-- The central-region quotient model is compatible with the central-family coordinates. -/
public theorem toCentralFamily_sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph
    (x : ↥A.sectionSevenAffineOrderThreeCentralRegion) :
    A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily
        (A.sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph x) =
      A.sectionSevenEllipticCentralImageHomeomorph
        ⟨x.1, A.mem_centralImage_of_mem_centralHeightLowerRegion
          A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ) x.2⟩ := by
  refine (A.toCentralFamily_orderThreeAffineHalfPlaneLiftQuotientHomeomorphRange_symm _).trans ?_
  exact congrArg A.sectionSevenEllipticCentralImageHomeomorph
    (Subtype.ext (A.coe_centralHeightLowerRegionHomeomorph_symm
      A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ) x))

/-- Including the disc lift quotient into the half-plane lift quotient and then into the actual
central family is the direct disc-lift inclusion. -/
public theorem toCentralFamily_orderThreeAffineDiscLiftQuotientInclusion
    {r : ℝ} (hr : r ≤ 2 / 3) (q : Quotient (orbitRelOf (A.orderThreeAffineDiscLiftAction r))) :
    A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily
        (A.orderThreeAffineDiscLiftQuotientInclusion hr q) =
      A.orderThreeAffineDiscLiftQuotientToCentralFamily r q := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- If the actual order-three star overlap is the affine disc region of the regular central
family, then the order-three overlap quotient identification exists. -/
public theorem orderThreeOverlapQuotientIdentification_nonempty_of_overlap_eq
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ 2 / 3)
    (hoverlap :
      A.sectionSevenOrderThreeFillingImage ∩ A.sectionSevenAffineOrderThreeCentralRegion =
        A.sectionSevenAffineOrderThreeDiscRegion r) :
    Nonempty A.SectionSevenAffineOrderThreeOverlapQuotientIdentification := by
  refine ⟨{ normalizationRadius := s
            affineDiscRadius := r
            normalizationRadius_pos := hs
            normalizationRadius_lt_disc := hsr
            affineDiscRadius_le_halfPlane := hr
            overlapModel := (Homeomorph.setCongr hoverlap).trans
              (A.sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph r)
            commutes := ?_ }⟩
  funext x
  apply (A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding).injective
  rw [Function.comp_apply, Function.comp_apply,
    A.toCentralFamily_orderThreeAffineDiscLiftQuotientInclusion hr,
    A.toCentralFamily_sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph]
  exact (A.toCentralFamily_sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph r
    (Homeomorph.setCongr hoverlap x)).symm

/-- Any overlap quotient identification computes the central-family point of an overlap point. -/
public theorem toCentralFamily_overlapModel
    (Q : A.SectionSevenAffineOrderThreeOverlapQuotientIdentification)
    (u : ↥(A.sectionSevenOrderThreeFillingImage ∩
      A.sectionSevenAffineOrderThreeCentralRegion)) :
    A.orderThreeAffineDiscLiftQuotientToCentralFamily Q.affineDiscRadius (Q.overlapModel u) =
      A.sectionSevenEllipticCentralImageHomeomorph
        ⟨u.1, A.mem_centralImage_of_mem_centralHeightLowerRegion
          A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ) u.2.2⟩ := by
  have h := congrFun Q.commutes u
  simp only [Function.comp_apply] at h
  rw [← A.toCentralFamily_orderThreeAffineDiscLiftQuotientInclusion
    Q.affineDiscRadius_le_halfPlane, ← h]
  exact A.toCentralFamily_sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph _

/-- Conversely, an overlap quotient identification forces the actual order-three star overlap to
be the affine disc region of its own radius.  The identification is therefore exactly equivalent
to that set equality. -/
public theorem overlap_eq_sectionSevenAffineOrderThreeDiscRegion
    (Q : A.SectionSevenAffineOrderThreeOverlapQuotientIdentification) :
    A.sectionSevenOrderThreeFillingImage ∩ A.sectionSevenAffineOrderThreeCentralRegion =
      A.sectionSevenAffineOrderThreeDiscRegion Q.affineDiscRadius := by
  ext x
  constructor
  · intro hx
    have hmem := A.mem_centralImage_of_mem_centralHeightLowerRegion
      A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ) hx.2
    refine ⟨⟨x, hmem⟩, ?_, rfl⟩
    have hrange : A.orderThreeAffineDiscLiftQuotientToCentralFamily Q.affineDiscRadius
        (Q.overlapModel ⟨x, hx⟩) ∈
          Set.range (A.orderThreeAffineDiscLiftQuotientToCentralFamily Q.affineDiscRadius) :=
      Set.mem_range_self _
    rw [A.range_orderThreeAffineDiscLiftQuotientToCentralFamily,
      A.toCentralFamily_overlapModel Q ⟨x, hx⟩] at hrange
    exact hrange
  · rintro ⟨y, hy, rfl⟩
    have hrange : A.sectionSevenEllipticCentralImageHomeomorph y ∈
        Set.range (A.orderThreeAffineDiscLiftQuotientToCentralFamily Q.affineDiscRadius) := by
      rw [A.range_orderThreeAffineDiscLiftQuotientToCentralFamily]
      exact hy
    obtain ⟨q, hq⟩ := hrange
    refine (Q.overlapModel.symm q).2 |>.imp ?_ ?_ <;> intro h <;>
      · have hpoint : ((Q.overlapModel.symm q : ↥(A.sectionSevenOrderThreeFillingImage ∩
            A.sectionSevenAffineOrderThreeCentralRegion)) : A.SectionSevenEllipticInterior) =
            y.1 := by
          have := A.toCentralFamily_overlapModel Q (Q.overlapModel.symm q)
          rw [Q.overlapModel.apply_symm_apply, hq] at this
          exact congrArg Subtype.val
            (A.sectionSevenEllipticCentralImageHomeomorph.injective this.symm)
        rwa [hpoint] at h

end SphereSixComplex.Geometry.PaperAnalyticData
