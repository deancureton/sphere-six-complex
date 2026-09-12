module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineRegularLiftCarriers

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

namespace SphereSixComplex.Geometry.AnalyticData

open GlobalTorusFamily TorusFamily
open EquivariantQuotientHomeomorph
open SphereSixComplex.TriangleGroup
open SphereSixComplex.OpenUnionHomotopy

variable (A : AnalyticData)

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
public noncomputable def ellipticCentralRadius :
    A.ellipticCentralImage → ℝ :=
  fun x ↦ ‖(A.ellipticCentralCoordinate x).1‖

/-- The affine disc region of radius `r` inside the regular central image. -/
public noncomputable def affineOrderThreeDiscRegion (r : ℝ) :
    Set A.ellipticInterior :=
  centralHeightLowerRegion A.ellipticCentralRadius r

/-- The affine disc region, expressed as the quotient of its full-deck-action disc lift. -/
public noncomputable def affineOrderThreeDiscRegionQuotientHomeomorph (r : ℝ) :
    ↥(A.affineOrderThreeDiscRegion r) ≃ₜ
      Quotient (orbitRelOf (A.orderThreeAffineDiscLiftAction r)) :=
  (centralHeightLowerRegionHomeomorph A A.ellipticCentralRadius r).symm |>.trans
    (A.ellipticCentralImageHomeomorph.subtype fun _ ↦ Iff.rfl) |>.trans
    (Homeomorph.setCongr
      (A.range_orderThreeAffineDiscLiftQuotientToCentralFamily r).symm) |>.trans
    (A.orderThreeAffineDiscLiftQuotientHomeomorphRange r).symm

public theorem mem_centralImage_of_mem_centralHeightLowerRegion
    (height : A.ellipticCentralImage → ℝ) (upper : ℝ)
    {x : A.ellipticInterior}
    (hx : x ∈ centralHeightLowerRegion height upper) :
    x ∈ A.ellipticCentralImage := by
  obtain ⟨y, _, rfl⟩ := hx
  exact y.2

public theorem coe_centralHeightLowerRegionHomeomorph_symm
    (height : A.ellipticCentralImage → ℝ) (upper : ℝ)
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
public theorem toCentralFamily_affineOrderThreeDiscRegionQuotientHomeomorph
    (r : ℝ) (x : ↥(A.affineOrderThreeDiscRegion r)) :
    A.orderThreeAffineDiscLiftQuotientToCentralFamily r
        (A.affineOrderThreeDiscRegionQuotientHomeomorph r x) =
      A.ellipticCentralImageHomeomorph
        ⟨x.1, A.mem_centralImage_of_mem_centralHeightLowerRegion
          A.ellipticCentralRadius r x.2⟩ := by
  refine (A.toCentralFamily_orderThreeAffineDiscLiftQuotientHomeomorphRange_symm r _).trans ?_
  exact congrArg A.ellipticCentralImageHomeomorph
    (Subtype.ext (A.coe_centralHeightLowerRegionHomeomorph_symm
      A.ellipticCentralRadius r x))

/-- The central-region quotient model is compatible with the central-family coordinates. -/
public theorem toCentralFamily_affineOrderThreeCentralRegionQuotientHomeomorph
    (x : ↥A.affineOrderThreeCentralRegion) :
    A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily
        (A.affineOrderThreeCentralRegionQuotientHomeomorph x) =
      A.ellipticCentralImageHomeomorph
        ⟨x.1, A.mem_centralImage_of_mem_centralHeightLowerRegion
          A.ellipticCentralHeight (2 / 3 : ℝ) x.2⟩ := by
  refine (A.toCentralFamily_orderThreeAffineHalfPlaneLiftQuotientHomeomorphRange_symm _).trans ?_
  exact congrArg A.ellipticCentralImageHomeomorph
    (Subtype.ext (A.coe_centralHeightLowerRegionHomeomorph_symm
      A.ellipticCentralHeight (2 / 3 : ℝ) x))

/-- Including the disc lift quotient into the half-plane lift quotient and then into the actual
central family is the direct disc-lift inclusion. -/
public theorem toCentralFamily_orderThreeAffineDiscLiftQuotientInclusion
    {r : ℝ} (hr : r ≤ 2 / 3) (q : Quotient (orbitRelOf (A.orderThreeAffineDiscLiftAction r))) :
    A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily
        (A.orderThreeAffineDiscLiftQuotientInclusion hr q) =
      A.orderThreeAffineDiscLiftQuotientToCentralFamily r q := by
  induction q using Quotient.inductionOn with
  | _ x => rfl




end SphereSixComplex.Geometry.AnalyticData
