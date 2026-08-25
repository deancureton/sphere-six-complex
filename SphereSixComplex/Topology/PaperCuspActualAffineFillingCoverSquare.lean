module

public import SphereSixComplex.Geometry.CuspAnalyticFillingCollar
public import SphereSixComplex.Topology.PaperActualFillingCoverSquares
public import SphereSixComplex.Topology.PaperVanKampenAlgebraAdapter

/-!
# The explicit cover square for the actual cusp filling

This file isolates the parts of the cusp regular-cover square that follow directly from the
normalized additive coordinates.  The additive source covers the punctured collar, its canonical
map into the full local carrier commutes with the collar-to-filling map, and the full local
projection is the already proved parameter-lattice quotient covering.

The two remaining universal-cover inputs are deliberately not asserted here: the exact deck
classification of the additive collar projection and simple connectivity of the full local
carrier.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex

open Geometry Geometry.ComplexTorus Geometry.CuspPuncturedCollarBridge
open Geometry.StandardInfiniteA2ToricModel

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates.CuspPeriodExpansion

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
variable {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- The explicit additive cover mapped to the punctured local carrier before the
parameter-lattice quotient. -/
public noncomputable def additiveCuspCoverToPuncturedCarrier
    (W : ActualPuncturedCuspCollarWitness N M) :
    C(additiveCuspRadiusCover W.localWitness.radius,
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0}) :=
  ⟨fun p ↦ additiveToPuncturedLocalHomeomorph M W.localWitness.radius (Quotient.mk _ p),
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius).continuous.comp
      continuous_quot_mk⟩

/-- The explicit additive cover projected to the actual punctured cusp quotient. -/
public noncomputable def additiveCuspBoundaryProjection
    (W : ActualPuncturedCuspCollarWitness N M) :
    C(additiveCuspRadiusCover W.localWitness.radius, puncturedLocalCuspQuotient W) :=
  ⟨fun p ↦ Quotient.mk _ (additiveCuspCoverToPuncturedCarrier W p),
    continuous_quot_mk.comp (additiveCuspCoverToPuncturedCarrier W).continuous⟩

/-- The explicit map from the additive collar cover into the full local toric carrier. -/
public noncomputable def additiveCuspFillingLift
    (W : ActualPuncturedCuspCollarWitness N M) :
    C(additiveCuspRadiusCover W.localWitness.radius,
      LocalCarrier M W.localWitness.radius) :=
  ⟨fun p ↦ (additiveCuspCoverToPuncturedCarrier W p).1,
    continuous_subtype_val.comp (additiveCuspCoverToPuncturedCarrier W).continuous⟩

/-- The full local carrier projected to the actual toric cusp filling. -/
public noncomputable def actualCuspFillingProjection
    (W : ActualPuncturedCuspCollarWitness N M) :
    C(LocalCarrier M W.localWitness.radius, actualLocalCuspFilling W) :=
  ⟨Quotient.mk _, continuous_quot_mk⟩

/-- The explicit additive lift gives a commutative collar-to-filling cover square. -/
public theorem additiveCuspCoverSquare_commutes
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    puncturedLocalCuspToFilling W (additiveCuspBoundaryProjection W p) =
      actualCuspFillingProjection W (additiveCuspFillingLift W p) := by
  exact puncturedLocalCuspToFilling_mk W (additiveCuspCoverToPuncturedCarrier W p)

/-- The additive source in the actual cusp square is simply connected. -/
public theorem additiveCuspBoundaryCover_simplyConnected
    (W : ActualPuncturedCuspCollarWitness N M) :
    SimplyConnectedSpace (additiveCuspRadiusCover W.localWitness.radius) :=
  additiveCuspRadiusCover_simplyConnected W.localWitness.radius_pos

/-- The filling side of the explicit cusp square is the proved parameter-lattice quotient
covering. -/
public theorem actualCuspFillingProjection_isQuotientCoveringMap
    (W : ActualPuncturedCuspCollarWitness N M) :
    let C :=
      NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
        N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
    letI := (C.toCuspActionData W.localWitness.fixedPoint).psiAction
    IsQuotientCoveringMap (actualCuspFillingProjection W)
      (Multiplicative ParameterLattice) := by
  exact W.localWitness.quotient_isQuotientCoveringMap

end Geometry.CuspPuncturedCollarBridge

namespace Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPhaseEstimates.CuspPeriodExpansion

variable (A : PaperAnalyticData)

/-- The actual cusp collar source is canonically the central--cusp overlap in the glued star. -/
public noncomputable def cuspCollarToStarOverlapHomeomorph :
    A.openEmbeddingStarData.collarSource 0 ≃ₜ
      ((sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 0 ∩
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 1 :
          Set (GluedSpace
            A.openEmbeddingStarData.toFourPieceStarGluingData.glueData)) := by
  let S := A.openEmbeddingStarData
  let e : S.collarSource 0 ≃ₜ Set.range (S.collarSourceToGlued 0) :=
    (S.collarSourceToGlued_isOpenEmbedding 0).isEmbedding.toHomeomorph
  exact e.trans (Homeomorph.setCongr (S.range_collarSourceToGlued 0))

@[simp]
public theorem cuspCollarToStarOverlapHomeomorph_coe
    (x : A.openEmbeddingStarData.collarSource 0) :
    (A.cuspCollarToStarOverlapHomeomorph x).1 =
      A.openEmbeddingStarData.collarSourceToGlued 0 x :=
  rfl

/-- The actual cusp filling is canonically its open image in the glued star. -/
public noncomputable def cuspFillingToStarPieceHomeomorph :
    A.openEmbeddingStarData.filling 0 ≃ₜ
      (sectionSevenStarOpenCover
        A.openEmbeddingStarData.toFourPieceStarGluingData).piece 1 := by
  let S := A.openEmbeddingStarData
  let e : S.filling 0 ≃ₜ Set.range
      (S.toFourPieceStarGluingData.glueData.toGlueData.ι (some 0)) :=
    (S.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding (some 0)).isEmbedding.toHomeomorph
  exact e.trans (Homeomorph.setCongr rfl)

@[simp]
public theorem cuspFillingToStarPieceHomeomorph_coe
    (x : A.openEmbeddingStarData.filling 0) :
    (A.cuspFillingToStarPieceHomeomorph x).1 =
      A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι (some 0) x :=
  rfl

/-- The normalized additive projection transported to the exact cusp overlap of the glued star. -/
public noncomputable def actualCuspBoundaryProjection :
    C(additiveCuspRadiusCover A.starCuspWitness.localWitness.radius,
      ((sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 0 ∩
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 1 :
          Set (GluedSpace
            A.openEmbeddingStarData.toFourPieceStarGluingData.glueData))) :=
  (⟨A.cuspCollarToStarOverlapHomeomorph,
    A.cuspCollarToStarOverlapHomeomorph.continuous⟩ : C(_, _)).comp
      (additiveCuspBoundaryProjection A.starCuspWitness)

/-- The full local-carrier projection transported to the exact cusp piece of the glued star. -/
public noncomputable def actualCuspFillingProjectionToStar :
    C(LocalCarrier A.toricModel A.starCuspWitness.localWitness.radius,
      (sectionSevenStarOpenCover
        A.openEmbeddingStarData.toFourPieceStarGluingData).piece 1) :=
  (⟨A.cuspFillingToStarPieceHomeomorph,
    A.cuspFillingToStarPieceHomeomorph.continuous⟩ : C(_, _)).comp
      (actualCuspFillingProjection A.starCuspWitness)

/-- Inclusion of the actual central--cusp overlap into the cusp piece. -/
public def actualCuspOverlapToFillingPiece :
    C(((sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 0 ∩
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 1 :
          Set (GluedSpace
            A.openEmbeddingStarData.toFourPieceStarGluingData.glueData)),
      (sectionSevenStarOpenCover
        A.openEmbeddingStarData.toFourPieceStarGluingData).piece 1) where
  toFun x := ⟨x.1, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The transported additive lift commutes with the actual overlap inclusion in the glued
star. -/
public theorem actualCuspCoverSquare_commutes
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.actualCuspOverlapToFillingPiece (A.actualCuspBoundaryProjection p) =
      A.actualCuspFillingProjectionToStar
        (additiveCuspFillingLift A.starCuspWitness p) := by
  let S := A.openEmbeddingStarData
  let q : S.collarSource 0 := additiveCuspBoundaryProjection A.starCuspWitness p
  let y : S.filling 0 := actualCuspFillingProjection A.starCuspWitness
    (additiveCuspFillingLift A.starCuspWitness p)
  have hfill : S.toFilling 0 q = y :=
    additiveCuspCoverSquare_commutes A.starCuspWitness p
  apply Subtype.ext
  change (A.cuspCollarToStarOverlapHomeomorph
      q).1 =
    (A.cuspFillingToStarPieceHomeomorph
      y).1
  rw [A.cuspCollarToStarOverlapHomeomorph_coe,
    A.cuspFillingToStarPieceHomeomorph_coe, ← hfill]
  change S.toFourPieceStarGluingData.glueData.toGlueData.ι none (S.toCentral 0 q) =
    S.toFourPieceStarGluingData.glueData.toGlueData.ι (some 0) (S.toFilling 0 q)
  symm
  apply (S.toFourPieceStarGluingData.glueData.ι_eq_iff_rel
    (some 0) none (S.toFilling 0 q) (S.toCentral 0 q)).mpr
  exact ⟨S.fillingCollarPoint 0 q, rfl, by
    change ((S.collarEquiv 0).symm (S.fillingCollarPoint 0 q)).1 = S.toCentral 0 q
    rw [S.collarEquiv_symm_toFilling]
    rfl⟩

/-- The filling projection transported to the glued cusp piece remains a quotient covering. -/
public theorem actualCuspFillingProjectionToStar_isQuotientCoveringMap :
    let C :=
      NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
        A.cuspCoordinate A.toricModel A.starCuspWitness.localWitness.radius
          A.starCuspWitness.localWitness.radius_pos A.starCuspWitness.localWitness.radius_le
    letI := (C.toCuspActionData A.starCuspWitness.localWitness.fixedPoint).psiAction
    IsQuotientCoveringMap A.actualCuspFillingProjectionToStar
      (Multiplicative ParameterLattice) := by
  let C :=
    NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      A.cuspCoordinate A.toricModel A.starCuspWitness.localWitness.radius
        A.starCuspWitness.localWitness.radius_pos A.starCuspWitness.localWitness.radius_le
  let _ := (C.toCuspActionData A.starCuspWitness.localWitness.fixedPoint).psiAction
  exact (actualCuspFillingProjection_isQuotientCoveringMap A.starCuspWitness).homeomorph_comp
    A.cuspFillingToStarPieceHomeomorph

end Geometry.PaperAnalyticData

namespace Topology

open LatticeData
open SphereSixComplex.Geometry.CuspFilling

/-- The toric vanishing map is the inclusion of the paper's last-two-coordinate sublattice. -/
public def paperCuspVanishing : paperToricSubgroup →+ Lattice :=
  paperToricSubgroup.subtype

/-- The selected vanishing map reaches every lattice vector in the toric sublattice. -/
public theorem paperCuspVanishing_onto (a : Lattice) (ha : a ∈ paperToricSubgroup) :
    ∃ k, paperCuspVanishing k = a :=
  ⟨⟨a, ha⟩, rfl⟩

/-- The two surviving cusp coordinates after the toric sublattice is filled. -/
public def paperCuspResidualProjection : Lattice →+ ParameterLattice where
  toFun a := ![a 0, a 1]
  map_zero' := by funext i; fin_cases i <;> rfl
  map_add' a b := by funext i; fin_cases i <;> rfl

/-- The residual two-coordinate projection is onto. -/
public theorem paperCuspResidualProjection_surjective :
    Function.Surjective paperCuspResidualProjection := by
  intro a
  refine ⟨![a 0, a 1, 0, 0], ?_⟩
  funext i
  fin_cases i <;> rfl

/-- Its kernel is exactly the last-two-coordinate toric sublattice killed by the cusp filling. -/
public theorem paperCuspResidualProjection_ker :
    paperCuspResidualProjection.ker = paperToricSubgroup := by
  ext a
  simp [paperCuspResidualProjection, paperToricSubgroup]

/-- The lattice quotient left by the toric cusp filling is the two-dimensional parameter
lattice used by the actual filling deck action. -/
public noncomputable def paperCuspResidualQuotientEquiv :
    Lattice ⧸ paperToricSubgroup ≃+ ParameterLattice :=
  (QuotientAddGroup.quotientAddEquivOfEq paperCuspResidualProjection_ker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective paperCuspResidualProjection
      paperCuspResidualProjection_surjective)

end Topology

end SphereSixComplex

end
