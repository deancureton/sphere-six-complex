module

public import SphereSixComplex.Geometry.PaperCentralCompactCore
public import SphereSixComplex.Topology.PaperSectionSevenCentralBandSplit

/-!
# A concrete base split for the Section 7 elliptic interior

The invariant modular coordinate descends from the regular family to its central quotient.  Two
overlapping real half-planes in the twice-punctured affine coordinate line then give the open
central allocation used by the two-disc cover.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily

variable (A : PaperAnalyticData)

/-- The modular base coordinate is constant on triangle-group orbits of the regular torus
family. -/
public theorem centralFamilyCoordinate_respects
    (x y : RegularTotalSpace A.periods)
    (h : (@MulAction.orbitRel SphereSixComplex.TriangleGroup.Delta _ _
      (regularFamilyDeckAction A.periods)) x y) :
    A.regularCoordinate (regularTotalSpaceBase A.periods x) =
      A.regularCoordinate (regularTotalSpaceBase A.periods y) := by
  let _ := regularFamilyDeckAction A.periods
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, rfl⟩ := h
  apply Subtype.ext
  change A.modular.sourceCoordinate.coordinate
      (regularTotalSpaceBase A.periods (regularFamilyDeckMap A.periods g y)).1 = _
  rw [regularTotalSpaceBase_familyDeckMap]
  exact A.modular.sourceCoordinate.coordinate_invariant g _

/-- The exact affine coordinate on the base of the actual central family. -/
public noncomputable def centralFamilyCoordinate :
    A.CentralFamily → RegularCoordinateBase := by
  letI := regularFamilyDeckAction A.periods
  exact Quotient.lift
    (fun x ↦ A.regularCoordinate (regularTotalSpaceBase A.periods x))
    A.centralFamilyCoordinate_respects

public theorem centralFamilyCoordinate_centralQuotientProjection
    (x : RegularTotalSpace A.periods) :
    A.centralFamilyCoordinate (A.centralQuotientProjection x) =
      A.regularCoordinate (regularTotalSpaceBase A.periods x) :=
  rfl

public theorem centralFamilyCoordinate_continuous :
    Continuous A.centralFamilyCoordinate := by
  let _ := regularFamilyDeckAction A.periods
  apply continuous_quot_lift A.centralFamilyCoordinate_respects
  exact A.regularCoordinate_isLocalHomeomorph.continuous.comp
    (regularTotalSpaceBase_continuous A.periods)

public theorem centralFamilyCoordinate_surjective :
    Function.Surjective A.centralFamilyCoordinate := by
  intro z
  obtain ⟨u, hu⟩ := A.regularCoordinate_surjective z
  let q : RegularTotalSpace A.periods :=
    projection (regularParameterMap A.periods) (u, 0)
  refine ⟨A.centralQuotientProjection q, ?_⟩
  rw [A.centralFamilyCoordinate_centralQuotientProjection]
  change A.regularCoordinate u = z
  exact hu

public theorem sectionSevenCentralPiece_subset_ellipticInterior :
    A.SectionSevenEllipticCover.piece 0 ⊆
      A.SectionSevenEllipticCover.stage (2 : Fin 4) := by
  intro x hx
  rw [FourPieceOpenCover.stage]
  exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨by decide, hx⟩⟩

/-- Forgetting the elliptic-interior subtype identifies its central image with the central cover
piece. -/
public def sectionSevenEllipticCentralImageToPiece :
    A.sectionSevenEllipticCentralImage ≃ₜ A.SectionSevenEllipticCover.piece 0 where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, A.sectionSevenCentralPiece_subset_ellipticInterior x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The central image inside the elliptic interior is the actual central family. -/
public noncomputable def sectionSevenEllipticCentralImageHomeomorph :
    A.sectionSevenEllipticCentralImage ≃ₜ A.CentralFamily :=
  A.sectionSevenEllipticCentralImageToPiece.trans
    A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.symm

/-- A point of the central image inherits the exact affine base coordinate. -/
public noncomputable def sectionSevenEllipticCentralCoordinate :
    A.sectionSevenEllipticCentralImage → RegularCoordinateBase :=
  fun x ↦ A.centralFamilyCoordinate (A.sectionSevenEllipticCentralImageHomeomorph x)

public theorem sectionSevenEllipticCentralCoordinate_continuous :
    Continuous A.sectionSevenEllipticCentralCoordinate :=
  A.centralFamilyCoordinate_continuous.comp
    A.sectionSevenEllipticCentralImageHomeomorph.continuous

/-- The real part of the affine base coordinate supplies the central splitting height. -/
public noncomputable def sectionSevenEllipticCentralHeight :
    A.sectionSevenEllipticCentralImage → ℝ :=
  fun x ↦ (A.sectionSevenEllipticCentralCoordinate x).1.re

public theorem sectionSevenEllipticCentralHeight_continuous :
    Continuous A.sectionSevenEllipticCentralHeight :=
  Complex.continuous_re.comp
    (continuous_subtype_val.comp A.sectionSevenEllipticCentralCoordinate_continuous)

/-- The only separation facts needed to turn the affine half-plane cut into the actual central
allocation. -/
public structure SectionSevenAffineCentralSeparation : Prop where
  orderThreeFilling_disjoint_upper :
    Disjoint A.sectionSevenOrderThreeFillingImage
      (centralHeightUpperRegion A.sectionSevenEllipticCentralHeight (1 / 3 : ℝ))
  orderFourFilling_disjoint_lower :
    Disjoint A.sectionSevenOrderFourFillingImage
      (centralHeightLowerRegion A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ))

/-- The overlapping half-planes `re < 2/3` and `1/3 < re` give the concrete central height
split. -/
public noncomputable def sectionSevenAffineCentralHeightSplit
    (S : A.SectionSevenAffineCentralSeparation) :
    A.SectionSevenCentralHeightSplit where
  height := A.sectionSevenEllipticCentralHeight
  height_continuous := A.sectionSevenEllipticCentralHeight_continuous
  lower := 1 / 3
  upper := 2 / 3
  lower_lt_upper := by norm_num
  orderThreeFilling_disjoint_upper := S.orderThreeFilling_disjoint_upper
  orderFourFilling_disjoint_lower := S.orderFourFilling_disjoint_lower

end SphereSixComplex.Geometry.PaperAnalyticData
