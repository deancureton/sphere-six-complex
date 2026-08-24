module

public import SphereSixComplex.Topology.PaperCuspCentralFiberHomology
public import SphereSixComplex.Topology.PaperCuspPhaseSpreading
public import SphereSixComplex.Topology.PaperSectionSevenHomologyAssembly

/-!
# Positive-degree bases for the final Section 7 attachment

This file separates the six homology bases in the final cusp attachment from the four
geometric inclusion-map calculations.  The two cusp-filling bases are transported from the
actual toric central-fibre calculation.  The remaining four bases are exactly the homology of
the punctured cusp collar and of the elliptic interior.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable (A : PaperAnalyticData)

/-- Concatenate one and two integral coordinates. -/
public def finOneProdFinTwoAddEquiv :
    ((Fin 1 → ℤ) × (Fin 2 → ℤ)) ≃+ (Fin 3 → ℤ) where
  toFun x := ![x.1 0, x.2 0, x.2 1]
  invFun x := (fun _ ↦ x 0, ![x 1, x 2])
  left_inv x := by
    rcases x with ⟨x, y⟩
    apply Prod.ext
    · funext i
      fin_cases i
      rfl
    · funext i
      fin_cases i <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl
  map_add' x y := by
    funext i
    fin_cases i <;> rfl

/-- Concatenate two and four integral coordinates. -/
public def finTwoProdFinFourAddEquiv :
    ((Fin 2 → ℤ) × (Fin 4 → ℤ)) ≃+ (Fin 6 → ℤ) where
  toFun x := ![x.1 0, x.1 1, x.2 0, x.2 1, x.2 2, x.2 3]
  invFun x := (![x 0, x 1], ![x 2, x 3, x 4, x 5])
  left_inv x := by
    rcases x with ⟨x, y⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl
  map_add' x y := by
    funext i
    fin_cases i <;> rfl

/-- The four basis calculations not supplied by the existing cusp-filling computation.

The collar ranks are the Wang-sequence calculation for the cusp monodromy.  The interior ranks
are the Mayer--Vietoris calculation for the two elliptic discs.  Keeping these four statements
separate prevents a basis choice from silently assuming either final inclusion map. -/
public structure SectionSevenCollarInteriorHomologyBases where
  cuspCollarOne :
    IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0) ≃+
      (Fin 3 → ℤ)
  ellipticInteriorOne :
    IntegralSingularHomology 1
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ≃+
      (Fin 1 → ℤ)
  cuspCollarTwo :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) ≃+
      (Fin 6 → ℤ)
  ellipticInteriorTwo :
    IntegralSingularHomology 2
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ≃+
      (Fin 2 → ℤ)

/-- The six separate source/side bases used by the final positive-degree calculation. -/
public structure SectionSevenFinalSixHomologyBases where
  overlapOne :
    IntegralSingularHomology 1
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
          (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3 :
            Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) ≃+
      (Fin 3 → ℤ)
  interiorOne :
    IntegralSingularHomology 1
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ≃+
      (Fin 1 → ℤ)
  cuspPieceOne :
    IntegralSingularHomology 1
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3) ≃+
      (Fin 2 → ℤ)
  overlapTwo :
    IntegralSingularHomology 2
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
          (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3 :
            Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) ≃+
      (Fin 6 → ℤ)
  interiorTwo :
    IntegralSingularHomology 2
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ≃+
      (Fin 2 → ℤ)
  cuspPieceTwo :
    IntegralSingularHomology 2
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3) ≃+
      (Fin 4 → ℤ)

namespace SectionSevenFinalSixHomologyBases

variable {A : PaperAnalyticData}

/-- Combine the two degree-one side bases in the order interior, cusp filling. -/
public def finalOneTarget (B : A.SectionSevenFinalSixHomologyBases) :
    (IntegralSingularHomology 1
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ×
        IntegralSingularHomology 1
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) ≃+
      (Fin 3 → ℤ) :=
  (B.interiorOne.prodCongr B.cuspPieceOne).trans finOneProdFinTwoAddEquiv

/-- Combine the two degree-two side bases in the order interior, cusp filling. -/
public def finalTwoTarget (B : A.SectionSevenFinalSixHomologyBases) :
    (IntegralSingularHomology 2
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ×
        IntegralSingularHomology 2
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) ≃+
      (Fin 6 → ℤ) :=
  (B.interiorTwo.prodCongr B.cuspPieceTwo).trans finTwoProdFinFourAddEquiv

end SectionSevenFinalSixHomologyBases

/-- Transport the actual cusp-filling homology calculations and the four remaining local bases
to all six spaces in the final Mayer--Vietoris attachment. -/
public noncomputable def sectionSevenFinalSixHomologyBases
    (R : CuspPuncturedCollarBridge.ActualLocalCuspCentralFiberRetractionData
      A.starCuspWitness)
    (B : A.SectionSevenCollarInteriorHomologyBases) :
    A.SectionSevenFinalSixHomologyBases where
  overlapOne :=
    (integralSingularHomologyEquiv 1
      A.cuspCollarToSectionSevenFinalOverlapHomeomorph).symm.trans B.cuspCollarOne
  interiorOne := B.ellipticInteriorOne
  cuspPieceOne :=
    (integralSingularHomologyEquiv 1
      (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)).symm.trans
        (A.cuspFillingHomologyOneEquiv R)
  overlapTwo :=
    (integralSingularHomologyEquiv 2
      A.cuspCollarToSectionSevenFinalOverlapHomeomorph).symm.trans B.cuspCollarTwo
  interiorTwo := B.ellipticInteriorTwo
  cuspPieceTwo :=
    (integralSingularHomologyEquiv 2
      (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)).symm.trans
        (A.cuspFillingHomologyTwoEquiv R)

/-- Use the established phase-spreading retraction to discharge the cusp-filling input. -/
public noncomputable def sectionSevenFinalSixHomologyBasesOfLocalBases
    (B : A.SectionSevenCollarInteriorHomologyBases) :
    A.SectionSevenFinalSixHomologyBases :=
  A.sectionSevenFinalSixHomologyBases A.cuspCentralFiberRetractionData B

/-- The four geometric map identifications left after the six bases have been fixed.  Each field
identifies one actual inclusion, rather than assuming the signed Mayer--Vietoris map or the final
homology conclusion. -/
public structure SectionSevenFinalInclusionCoordinates
    (B : A.SectionSevenFinalSixHomologyBases) where
  interiorOne : ∀ x,
    B.interiorOne
        (integralSingularHomologyMap 1
          (IntegralMayerVietoris.interToLeft
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ sectionSevenFirstBoundaryHom (B.overlapOne x) (Fin.castAdd 2 i)
  cuspOne : ∀ x,
    B.cuspPieceOne
        (integralSingularHomologyMap 1
          (IntegralMayerVietoris.interToRight
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ -sectionSevenFirstBoundaryHom (B.overlapOne x) (Fin.natAdd 1 i)
  interiorTwo : ∀ x,
    B.interiorTwo
        (integralSingularHomologyMap 2
          (IntegralMayerVietoris.interToLeft
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ sectionSevenMayerVietorisFinalTwoHom (B.overlapTwo x) (Fin.castAdd 4 i)
  cuspTwo : ∀ x,
    B.cuspPieceTwo
        (integralSingularHomologyMap 2
          (IntegralMayerVietoris.interToRight
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ -sectionSevenMayerVietorisFinalTwoHom (B.overlapTwo x) (Fin.natAdd 2 i)

namespace SectionSevenFinalInclusionCoordinates

variable {A : PaperAnalyticData} {B : A.SectionSevenFinalSixHomologyBases}

/-- The four unsigned inclusion computations imply the signed degree-one square. -/
public theorem finalOne_comm (C : A.SectionSevenFinalInclusionCoordinates B) (x) :
    B.finalOneTarget
        (IntegralMayerVietoris.differenceMap
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3) 1 x) =
      sectionSevenFirstBoundaryHom (B.overlapOne x) := by
  funext i
  fin_cases i
  · change B.interiorOne
        (integralSingularHomologyMap 1
          (IntegralMayerVietoris.interToLeft
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) 0 = _
    exact congrFun (C.interiorOne x) 0
  · change B.cuspPieceOne
        (-(integralSingularHomologyMap 1
          (IntegralMayerVietoris.interToRight
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x)) 0 = _
    rw [map_neg, C.cuspOne]
    simp
  · change B.cuspPieceOne
        (-(integralSingularHomologyMap 1
          (IntegralMayerVietoris.interToRight
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x)) 1 = _
    rw [map_neg, C.cuspOne]
    simp

/-- The four unsigned inclusion computations imply the signed degree-two square. -/
public theorem finalTwo_comm (C : A.SectionSevenFinalInclusionCoordinates B) (x) :
    B.finalTwoTarget
        (IntegralMayerVietoris.differenceMap
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3) 2 x) =
      sectionSevenMayerVietorisFinalTwoHom (B.overlapTwo x) := by
  funext i
  fin_cases i
  · change B.interiorTwo
        (integralSingularHomologyMap 2
          (IntegralMayerVietoris.interToLeft
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) 0 = _
    exact congrFun (C.interiorTwo x) 0
  · change B.interiorTwo
        (integralSingularHomologyMap 2
          (IntegralMayerVietoris.interToLeft
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) 1 = _
    exact congrFun (C.interiorTwo x) 1
  · change B.cuspPieceTwo
        (-(integralSingularHomologyMap 2
          (IntegralMayerVietoris.interToRight
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x)) 0 = _
    rw [map_neg, C.cuspTwo]
    simp
  · change B.cuspPieceTwo
        (-(integralSingularHomologyMap 2
          (IntegralMayerVietoris.interToRight
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x)) 1 = _
    rw [map_neg, C.cuspTwo]
    simp
  · change B.cuspPieceTwo
        (-(integralSingularHomologyMap 2
          (IntegralMayerVietoris.interToRight
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x)) 2 = _
    rw [map_neg, C.cuspTwo]
    simp
  · change B.cuspPieceTwo
        (-(integralSingularHomologyMap 2
          (IntegralMayerVietoris.interToRight
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x)) 3 = _
    rw [map_neg, C.cuspTwo]
    simp

/-- Assemble the exact production interface from six bases and four inclusion computations. -/
public noncomputable def toPositiveDegreeHomologyAssembly
    (C : A.SectionSevenFinalInclusionCoordinates B) :
    A.SectionSevenPositiveDegreeHomologyAssembly where
  finalOneSource := B.overlapOne
  finalOneTarget := B.finalOneTarget
  finalOne_comm := C.finalOne_comm
  finalTwoSource := B.overlapTwo
  finalTwoTarget := B.finalTwoTarget
  finalTwo_comm := C.finalTwo_comm

end SectionSevenFinalInclusionCoordinates

/-- For the actual paper cusp retraction, the four local bases and four inclusion formulas are
the complete remaining input to the production positive-degree assembly. -/
public noncomputable def sectionSevenPositiveDegreeHomologyAssemblyOfLocalBases
    (B : A.SectionSevenCollarInteriorHomologyBases)
    (C : A.SectionSevenFinalInclusionCoordinates
      (A.sectionSevenFinalSixHomologyBasesOfLocalBases B)) :
    A.SectionSevenPositiveDegreeHomologyAssembly :=
  C.toPositiveDegreeHomologyAssembly

end SphereSixComplex.Geometry.PaperAnalyticData
