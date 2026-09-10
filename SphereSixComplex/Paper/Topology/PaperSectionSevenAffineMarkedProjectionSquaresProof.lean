module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedBandSquares
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineBandTrivialization

/-!
# Marking the affine central-band fibre coordinate

`affineCentralBandProductHomeomorph` is the marked trivialization attached to the
unique strip lift through the selected actual cusp crossing and its explicit regular-base point,
namely `affineNamedStripLift`.  Its base coordinate is the affine band projection and
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
public theorem affineCentralBandProductHomeomorph_fst
    (S : A.AffineCentralSeparation)
    (x : centralHeightBand
      (A.affineCentralHeightSplit S).height
      (A.affineCentralHeightSplit S).lower
      (A.affineCentralHeightSplit S).upper) :
    (A.affineCentralBandProductHomeomorph S x).1 =
      A.affineCentralBandProjection S x :=
  A.affineCentralBandMarkedProductHomeomorph_fst S x

/-- The unmarked trivialization statement does not determine the fibre coordinate: composing the
named marked fibre coordinate with an arbitrary self-homeomorphism of the band torus again
produces a witness of `AffineCentralBandProductTrivialization`. -/
public theorem exists_productTrivialization_fiberCoordinate_comp
    (S : A.AffineCentralSeparation)
    (M : AdditiveTorus A.duplicatedSectionSevenBandParameter ≃ₜ
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    ∃ e : centralHeightBand
        (A.affineCentralHeightSplit S).height
        (A.affineCentralHeightSplit S).lower
        (A.affineCentralHeightSplit S).upper ≃ₜ
      affineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter,
      (∀ x, (e x).1 = A.affineCentralBandProjection S x) ∧
        ∀ x, (e x).2 = M (A.affineCentralBandFiberCoordinate S x) := by
  refine ⟨(A.affineCentralBandProductHomeomorph S).trans
    ((Homeomorph.refl affineVerticalStrip).prodCongr M), fun x ↦ ?_, fun x ↦ rfl⟩
  exact affineCentralBandProductHomeomorph_fst S x

/-- The marked trivialization attached to a strip lift also has the affine band projection as its
base coordinate. -/
public theorem affineCentralBandProductHomeomorphOfLift_symm_fst
    (S : A.AffineCentralSeparation) (L : A.AffineStripLift)
    (x : centralHeightBand
      (A.affineCentralHeightSplit S).height
      (A.affineCentralHeightSplit S).lower
      (A.affineCentralHeightSplit S).upper) :
    ((A.affineCentralBandProductHomeomorphOfLift S L).symm x).1 =
      A.affineCentralBandProjection S x := by
  have hkey := A.affineCentralBandProductHomeomorphOfLift_toCentralFamily S L
    ((A.affineCentralBandProductHomeomorphOfLift S L).symm x)
  rw [Homeomorph.apply_symm_apply] at hkey
  have hcoord := congrArg A.centralFamilyCoordinate hkey
  rw [A.centralFamilyCoordinate_stripLiftPoint] at hcoord
  apply Subtype.ext
  exact (congrArg (Subtype.val : RegularCoordinateBase → ℂ) hcoord).symm

/-- The named marked trivialization and the marked trivialization attached to any other strip lift
differ by a self-homeomorphism of `strip × torus` over the strip. -/
public theorem exists_fiberwise_comparison_with_marked
    (S : A.AffineCentralSeparation) (L : A.AffineStripLift) :
    ∃ psi : affineVerticalStrip ×
          AdditiveTorus A.duplicatedSectionSevenBandParameter ≃ₜ
        affineVerticalStrip ×
          AdditiveTorus A.duplicatedSectionSevenBandParameter,
      (∀ p, (psi p).1 = p.1) ∧
        ∀ x, A.affineCentralBandProductHomeomorph S x =
          psi ((A.affineCentralBandProductHomeomorphOfLift S L).symm x) := by
  refine ⟨(A.affineCentralBandProductHomeomorphOfLift S L).trans
    (A.affineCentralBandProductHomeomorph S), fun p ↦ ?_, fun x ↦ ?_⟩
  · have hbase := affineCentralBandProductHomeomorph_fst S
      (A.affineCentralBandProductHomeomorphOfLift S L p)
    have hmark := affineCentralBandProductHomeomorphOfLift_symm_fst S L
      (A.affineCentralBandProductHomeomorphOfLift S L p)
    rw [Homeomorph.symm_apply_apply] at hmark
    exact hbase.trans hmark.symm
  · show _ = A.affineCentralBandProductHomeomorph S
      (A.affineCentralBandProductHomeomorphOfLift S L
        ((A.affineCentralBandProductHomeomorphOfLift S L).symm x))
    rw [Homeomorph.apply_symm_apply]

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
