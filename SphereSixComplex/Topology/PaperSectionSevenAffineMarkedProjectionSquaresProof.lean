module

public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandSquares
public import SphereSixComplex.Topology.PaperSectionSevenAffineBandTrivialization

/-!
# Marking the affine central-band fibre coordinate

`sectionSevenAffineCentralBandProductHomeomorph` is the marked trivialization attached to the
unique strip lift through the selected actual cusp crossing and its explicit regular-base point,
namely `sectionSevenAffineNamedStripLift`.  Its base coordinate is the affine band projection and
its fibre coordinate is therefore fixed by the marking.

This module also records why the marking is necessary: forgetting it leaves the fibre coordinate
undetermined, since composing with any self-homeomorphism of the band torus gives another witness
of the unmarked product-trivialization statement.  Trivializations attached to two strip lifts are
compared by a fibrewise self-homeomorphism over the strip.
-/

@[expose] public section

noncomputable section

open Set Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable {A : PaperAnalyticData}

/-- The base coordinate of the named marked product homeomorphism is the affine band
projection. -/
public theorem sectionSevenAffineCentralBandProductHomeomorph_fst
    (S : A.SectionSevenAffineCentralSeparation)
    (x : centralHeightBand
      (A.sectionSevenAffineCentralHeightSplit S).height
      (A.sectionSevenAffineCentralHeightSplit S).lower
      (A.sectionSevenAffineCentralHeightSplit S).upper) :
    (A.sectionSevenAffineCentralBandProductHomeomorph S x).1 =
      A.sectionSevenAffineCentralBandProjection S x :=
  A.sectionSevenAffineCentralBandMarkedProductHomeomorph_fst S x

/-- The unmarked trivialization statement does not determine the fibre coordinate: composing the
named marked fibre coordinate with an arbitrary self-homeomorphism of the band torus again
produces a witness of `SectionSevenAffineCentralBandProductTrivialization`. -/
public theorem exists_productTrivialization_fiberCoordinate_comp
    (S : A.SectionSevenAffineCentralSeparation)
    (M : AdditiveTorus A.duplicatedSectionSevenBandParameter ≃ₜ
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    ∃ e : centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper ≃ₜ
      sectionSevenAffineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter,
      (∀ x, (e x).1 = A.sectionSevenAffineCentralBandProjection S x) ∧
        ∀ x, (e x).2 = M (A.sectionSevenAffineCentralBandFiberCoordinate S x) := by
  refine ⟨(A.sectionSevenAffineCentralBandProductHomeomorph S).trans
    ((Homeomorph.refl sectionSevenAffineVerticalStrip).prodCongr M), fun x ↦ ?_, fun x ↦ rfl⟩
  exact sectionSevenAffineCentralBandProductHomeomorph_fst S x

/-- The marked trivialization attached to a strip lift also has the affine band projection as its
base coordinate. -/
public theorem sectionSevenAffineCentralBandProductHomeomorphOfLift_symm_fst
    (S : A.SectionSevenAffineCentralSeparation) (L : A.SectionSevenAffineStripLift)
    (x : centralHeightBand
      (A.sectionSevenAffineCentralHeightSplit S).height
      (A.sectionSevenAffineCentralHeightSplit S).lower
      (A.sectionSevenAffineCentralHeightSplit S).upper) :
    ((A.sectionSevenAffineCentralBandProductHomeomorphOfLift S L).symm x).1 =
      A.sectionSevenAffineCentralBandProjection S x := by
  have hkey := A.sectionSevenAffineCentralBandProductHomeomorphOfLift_toCentralFamily S L
    ((A.sectionSevenAffineCentralBandProductHomeomorphOfLift S L).symm x)
  rw [Homeomorph.apply_symm_apply] at hkey
  have hcoord := congrArg A.centralFamilyCoordinate hkey
  rw [A.centralFamilyCoordinate_stripLiftPoint] at hcoord
  apply Subtype.ext
  exact (congrArg (Subtype.val : RegularCoordinateBase → ℂ) hcoord).symm

/-- The named marked trivialization and the marked trivialization attached to any other strip lift
differ by a self-homeomorphism of `strip × torus` over the strip. -/
public theorem exists_fiberwise_comparison_with_marked
    (S : A.SectionSevenAffineCentralSeparation) (L : A.SectionSevenAffineStripLift) :
    ∃ psi : sectionSevenAffineVerticalStrip ×
          AdditiveTorus A.duplicatedSectionSevenBandParameter ≃ₜ
        sectionSevenAffineVerticalStrip ×
          AdditiveTorus A.duplicatedSectionSevenBandParameter,
      (∀ p, (psi p).1 = p.1) ∧
        ∀ x, A.sectionSevenAffineCentralBandProductHomeomorph S x =
          psi ((A.sectionSevenAffineCentralBandProductHomeomorphOfLift S L).symm x) := by
  refine ⟨(A.sectionSevenAffineCentralBandProductHomeomorphOfLift S L).trans
    (A.sectionSevenAffineCentralBandProductHomeomorph S), fun p ↦ ?_, fun x ↦ ?_⟩
  · have hbase := sectionSevenAffineCentralBandProductHomeomorph_fst S
      (A.sectionSevenAffineCentralBandProductHomeomorphOfLift S L p)
    have hmark := sectionSevenAffineCentralBandProductHomeomorphOfLift_symm_fst S L
      (A.sectionSevenAffineCentralBandProductHomeomorphOfLift S L p)
    rw [Homeomorph.symm_apply_apply] at hmark
    exact hbase.trans hmark.symm
  · show _ = A.sectionSevenAffineCentralBandProductHomeomorph S
      (A.sectionSevenAffineCentralBandProductHomeomorphOfLift S L
        ((A.sectionSevenAffineCentralBandProductHomeomorphOfLift S L).symm x))
    rw [Homeomorph.apply_symm_apply]

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
