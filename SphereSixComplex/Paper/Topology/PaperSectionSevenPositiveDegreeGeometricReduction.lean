module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenPositiveDegreeRealization

/-!
# Geometric reduction of the Section 7 positive-degree input

The regular central image can be assigned to both elliptic sides, so the allocation itself is
canonical.  The remaining radial input is the contraction and band-trivialization package.  Once
any two-disc cover and its marked cycles have been realized, they directly supply the production
positive-degree homology assembly.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set Topology
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.EllipticFilling
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

variable (A : AnalyticData)


/-- A nested subspace is canonically homeomorphic to the same set in the original ambient
space. -/
public def nestedSubtypeHomeomorph {X : Type*} [TopologicalSpace X]
    (U V : Set X) (hVU : V ⊆ U) :
    (Subtype.val ⁻¹' V : Set U) ≃ₜ V where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, hVU x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Full-rank period bases canonically identify their additive four-tori. -/
public noncomputable def fullRankAdditiveTorusHomeomorph
    (x y : Parameters) (hx : FullRank x) (hy : FullRank y) :
    AdditiveTorus x ≃ₜ AdditiveTorus y :=
  let e : ComplexTwoSpace ≃L[ℝ] ComplexTwoSpace :=
    hx.realEquiv.symm.trans hy.realEquiv
  Homeomorph.Quotient.congr e.toHomeomorph fun z w => by
    apply SphereSixComplex.Geometry.FamilyEquivariance.orbitRel_iff_of_period_equivariant
      x y (AddEquiv.refl IntegerPeriods) e.toLinearEquiv.toAddEquiv
    intro n
    change e (periodVector x n) = periodVector y n
    rw [← hx.map_integer, ← hy.map_integer]
    simp [e]





/-- The two distinct filling images in the star are disjoint. -/
public theorem ellipticFillingImages_disjoint :
    A.orderThreeFillingImage ∩
      A.orderFourFillingImage = ∅ := by
  ext x
  constructor
  · rintro ⟨h₃, h₄⟩
    change x.1 ∈ A.starCover.piece 1 at h₃
    change x.1 ∈ A.starCover.piece 2 at h₄
    have h :
        x.1 ∈ A.starCover.piece 1 ∩
          A.starCover.piece 2 :=
      ⟨h₃, h₄⟩
    have hdisjoint :
        A.starCover.piece 1 ∩
          A.starCover.piece 2 = ∅ := by
      simpa [starCover,
        OpenEmbeddingStarData.sectionSevenMayerVietorisCover,
        sectionSevenMayerVietorisOpenCover, sectionSevenMayerVietorisOrder] using
        A.openEmbeddingStarData.fillingPiece_inter_fillingPiece
          (i := 1) (j := 2) (by decide)
    rw [hdisjoint] at h
    exact h.elim
  · simp




/-- Use the order-three fixed period lattice as the common band parameter. -/
public def duplicatedSectionSevenBandParameter : Parameters :=
  (SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne).1

/-- The canonical band parameter has full rank. -/
public noncomputable def duplicatedSectionSevenBandFullRank :
    FullRank A.duplicatedSectionSevenBandParameter :=
  let p := SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne
  FullRank.ofSetupInequalities p.1 p.2

/-- Real period coordinates identify the order-three and order-four central four-tori. -/
public noncomputable def duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph :
    AdditiveTorus A.duplicatedSectionSevenBandParameter ≃ₜ
      AdditiveTorus
        (SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 :=
  let p₄ := SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zTwo
  fullRankAdditiveTorusHomeomorph
    A.duplicatedSectionSevenBandParameter p₄.1
    A.duplicatedSectionSevenBandFullRank
    (FullRank.ofSetupInequalities p₄.1 p₄.2)

/-- The order-three restricted covering source is the canonical band torus. -/
public noncomputable def duplicatedSectionSevenBandToOrderThreeCoverSource :
    AdditiveTorus A.duplicatedSectionSevenBandParameter ≃ₜ
      RadialEllipticActionData.CentralFiberCoverSource
        (orderThreeRadialActionData A.periods) :=
  (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
    (orderThreeRadialActionData A.periods)).symm

/-- Transport the canonical band torus to the order-four restricted covering source. -/
public noncomputable def duplicatedSectionSevenBandToOrderFourCoverSource :
    AdditiveTorus A.duplicatedSectionSevenBandParameter ≃ₜ
      RadialEllipticActionData.CentralFiberCoverSource
        (orderFourRadialActionData A.periods) :=
  A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph.trans
    (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
      (orderFourRadialActionData A.periods)).symm


end SphereSixComplex.Geometry.AnalyticData
