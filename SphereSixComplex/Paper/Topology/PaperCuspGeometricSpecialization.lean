module
public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecializationTypes
public import SphereSixComplex.Paper.Topology.CuspFiniteFiberCoordinateCircles
public import SphereSixComplex.Paper.Topology.CuspFiberSpecializationBijective

@[expose] public section
noncomputable section
open AlgebraicTopology Matrix
open scoped ContinuousMap
namespace SphereSixComplex
open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
namespace Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization
open Geometry.PaperAnalyticData

public theorem actualFiberSpecializationTwo_bijective (A : PaperAnalyticData) :
    let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
    let _ := G.fiberTopology
    Function.Bijective (G.specializationHomologyTwoMap.comp
      (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal) := by
  have h := A.cuspFiberSpecializationTwoBijective CellularHomology.integralComparison
  unfold CuspFiberSpecializationTwoBijective at h
  rwa [A.actualCuspRadialClutchingData_eq] at h

public noncomputable def cuspFillingTwoCoordinateChange (A : PaperAnalyticData) :
    (Fin 4 → ℤ) ≃+ (Fin 4 → ℤ) := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
  let _ := G.fiberTopology
  exact ((LinearEquiv.ofBijective (G.specializationHomologyTwoMap.comp
    (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal)
      (actualFiberSpecializationTwo_bijective A)).symm.trans
        G.degreeTwoCoinvariantsEquiv).toAddEquiv

public noncomputable def cuspFillingTwoReadout (A : PaperAnalyticData) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.filling 0) ≃+ (Fin 4 → ℤ) :=
  (A.cuspFillingHomologyTwoEquiv A.cuspCentralFiberRetractionData).trans
    (cuspFillingTwoCoordinateChange A)

public structure FiniteFiberDegreeTwoSpecializationMatrix (A : PaperAnalyticData)
    (K : (Fin 4 → ℤ) ≃+ (Fin 4 → ℤ) := AddEquiv.refl _) : Prop where
  degreeTwo (j i : Fin 4) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    K (G.specializationHomologyTwoMap
        ((circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal
          (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1)))) i =
      (Pi.single j 1 : Fin 4 → ℤ) i

public theorem establishedFiniteFiberDegreeTwoSpecializationMatrix
    (A : PaperAnalyticData) :
    FiniteFiberDegreeTwoSpecializationMatrix A (cuspFillingTwoCoordinateChange A) where
  degreeTwo j i := by
    let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
    let _ := G.fiberTopology
    let e := LinearEquiv.ofBijective (G.specializationHomologyTwoMap.comp
      (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal)
        (actualFiberSpecializationTwo_bijective A)
    change G.degreeTwoCoinvariantsEquiv
      (e.symm (e (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1)))) i = _
    rw [e.symm_apply_apply, G.degreeTwoCoinvariantsEquiv.apply_symm_apply]

public theorem establishedFiniteFiberDegreeOneSpecializationMatrix
    (A : PaperAnalyticData) (j i : Fin 2) :
    let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
    let _ := G.fiberTopology
    G.specializationHomologyOneMap
      ((circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal
        (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))) i =
      (Pi.single j 1 : Fin 2 → ℤ) i := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  change G.specializationHomologyOneMap
      ((circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal
        (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))) i = _
  rw [G.degreeOneCoinvariantsEquiv_symm_single]
  change G.specializationHomologyOneMap
      (integralSingularHomologyMap 1
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
        (G.degreeOneFiberGenerator j)) i = _
  rw [G.specializationHomologyOneMap_fiberInclusion]
  exact congrFun (A.cuspFiniteFiberGenerator_deckCoordinates j) i

public theorem establishedFiniteFiberGeneratorSpecializationMatrix
    (A : PaperAnalyticData) : FiniteFiberGeneratorSpecializationMatrix A (cuspFillingTwoCoordinateChange A) where
  degreeOne := establishedFiniteFiberDegreeOneSpecializationMatrix A
  degreeTwo := (establishedFiniteFiberDegreeTwoSpecializationMatrix A).degreeTwo

private theorem addMonoidHom_ext_of_equiv_pi_single_one
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] {n : ℕ}
    (e : G ≃+ (Fin n → ℤ)) (f g : G →+ H)
    (h : ∀ i, f (e.symm (Pi.single i 1)) = g (e.symm (Pi.single i 1))) :
    f = g := by
  apply AddMonoidHom.ext
  intro x
  let y := e x
  have hx : x = e.symm y := by simp [y]
  rw [hx]
  apply Pi.single_induction (M := fun _ : Fin n ↦ ℤ)
    (p := fun z ↦ f (e.symm z) = g (e.symm z)) y
  · simp
  · intro a b ha hb
    simpa using congrArg₂ (· + ·) ha hb
  · intro i z
    have hz : (Pi.single i z : Fin n → ℤ) =
        z • (Pi.single i 1 : Fin n → ℤ) := by
      ext j
      classical
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    calc
      f (e.symm (Pi.single i z)) =
          f (e.symm (z • (Pi.single i 1 : Fin n → ℤ))) := by rw [hz]
      _ = z • f (e.symm (Pi.single i 1)) := by rw [map_zsmul, map_zsmul]
      _ = z • g (e.symm (Pi.single i 1)) := congrArg (z • ·) (h i)
      _ = g (e.symm (z • (Pi.single i 1 : Fin n → ℤ))) := by rw [map_zsmul, map_zsmul]
      _ = g (e.symm (Pi.single i z)) := by rw [hz]

private theorem specializationHomologyOneMap_comp_coinvariants (A : PaperAnalyticData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    G.specializationHomologyOneMap.comp
        (circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal =
      G.degreeOneCoinvariantsEquiv.toLinearMap := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  let c := G.degreeOneCoinvariantsEquiv
  have hhom : (G.specializationHomologyOneMap.comp P.coinvariantsToTotal).toAddMonoidHom =
      c.toLinearMap.toAddMonoidHom := by
    apply addMonoidHom_ext_of_equiv_pi_single_one c.toAddEquiv
    intro j
    funext i
    change G.specializationHomologyOneMap
        (P.coinvariantsToTotal (c.symm (Pi.single j 1))) i = _
    simpa using establishedFiniteFiberDegreeOneSpecializationMatrix A j i
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun hhom x

private theorem specializationHomologyOneMap_eq_projection (A : PaperAnalyticData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    G.specializationHomologyOneMap.toAddMonoidHom =
      degreeOneFiberProjection.comp
        G.geometricWangSections.circleMappingTorusHOneAddEquiv.toAddMonoidHom := by
  have hc := specializationHomologyOneMap_comp_coinvariants A
  generalize hG : CuspRadialClutchingConstruction.actualCuspRadialClutchingData
    A.starCuspWitness = G at hc ⊢
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  let S :=
    _root_.SphereSixComplex.CircleMappingTorusHomologyBases.EstablishedCircleMappingTorusGeometricSections.sections
      G.monodromyCoordinates
  let c := G.degreeOneCoinvariantsEquiv
  let f := G.specializationHomologyOneMap
  apply AddMonoidHom.ext
  intro x
  have hx :=
    P.map_eq_correctedSection_coinvariant
      S.degreeOne c f
    hc x
  change f x = _
  rw [hx]
  unfold ActualCuspRadialClutchingData.geometricWangSections
  change c _ = degreeOneFiberProjection
    (CircleMappingTorusHomologyBases.finTwoProdIntLinearEquiv (c _, _))
  have hproj (a : Fin 2 → ℤ) (b : ℤ) :
      degreeOneFiberProjection (finTwoProdIntLinearEquiv (a, b)) = a := by
    funext i
    fin_cases i <;> rfl
  rw [hproj]
  dsimp only [c, f, P, S]
  rfl

private theorem specializationHomologyTwoMap_eq_projection (A : PaperAnalyticData) :
    let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
    let _ := G.fiberTopology
    (cuspFillingTwoCoordinateChange A).toAddMonoidHom.comp
        G.specializationHomologyTwoMap.toAddMonoidHom =
      degreeTwoFiberProjection.comp
        G.geometricWangSections.circleMappingTorusHTwoAddEquiv.toAddMonoidHom := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
  let _ := G.fiberTopology
  apply AddMonoidHom.ext
  intro x
  funext i
  exact (G.geometricWangSections_degreeTwo_first
    (actualFiberSpecializationTwo_bijective A) x i).symm

/-- Cellular-to-singular naturality for the explicit periodic `A₂` cellular basis. -/
public theorem finiteBasisNaturality (A : PaperAnalyticData) :
    FiniteBasisNaturality A (cuspFillingTwoCoordinateChange A) := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  refine ⟨?_, ?_⟩
  · apply AddMonoidHom.ext
    intro x
    let _ := G.fiberTopology
    let e := integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv
    have h := DFunLike.congr_fun (specializationHomologyOneMap_eq_projection A)
      (e x)
    change actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
        (UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData A.starCuspWitness)
        (integralSingularHomologyMap 1
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ (e.symm (e x))) =
      degreeOneFiberProjection (G.geometricWangSections.circleMappingTorusHOneAddEquiv (e x)) at h
    rw [e.symm_apply_apply] at h
    simpa [G, e, ActualCuspRadialClutchingData.geometricHomologyOneEquiv,
      Geometry.PaperAnalyticData.cuspCentralFiberRetractionData_eq_radial] using h
  · apply AddMonoidHom.ext
    intro x
    let _ := G.fiberTopology
    let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
    have h := DFunLike.congr_fun (specializationHomologyTwoMap_eq_projection A)
      (e x)
    change cuspFillingTwoCoordinateChange A (actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
        (UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData A.starCuspWitness)
        (integralSingularHomologyMap 2
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ (e.symm (e x)))) =
      degreeTwoFiberProjection (G.geometricWangSections.circleMappingTorusHTwoAddEquiv (e x)) at h
    rw [e.symm_apply_apply] at h
    simpa [G, e, ActualCuspRadialClutchingData.geometricHomologyTwoEquiv,
      Geometry.PaperAnalyticData.cuspCentralFiberRetractionData_eq_radial] using h

/-- The former thirty-entry input, now derived from the twenty fibre entries and the
specialization-normalized Wang sections. -/
public theorem establishedFiniteGeneratorSpecializationMatrix
    (A : PaperAnalyticData) :
    FiniteGeneratorSpecializationMatrix A (cuspFillingTwoCoordinateChange A) := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  constructor
  · intro j i
    have h := DFunLike.congr_fun (finiteBasisNaturality A).degreeOne
      (G.geometricHomologyOneEquiv.symm (Pi.single j 1))
    simpa [G, degreeOneFiberProjection] using congrFun h i
  · intro j i
    have h := DFunLike.congr_fun (finiteBasisNaturality A).degreeTwo
      (G.geometricHomologyTwoEquiv.symm (Pi.single j 1))
    simpa [G, degreeTwoFiberProjection] using congrFun h i

/-- Cellular-to-singular naturality for the paper's selected periodic `A₂` cusp marking in
degree one: specialization preserves its two fibre coinvariants and kills the base circle.

The left-hand side does not mention the clutching datum, so this equation is only sound because
`ActualCuspRadialClutchingData` is *normalized*: `fiberNormalization` pins the fibre marking to
the collar's own period coordinates.  Do not weaken that field.  If the datum is replaced by the
un-normalized `UnnormalizedCuspRadialClutchingData`, this equation becomes false — the fibre
marking may be composed with the hyperelliptic `±1` involution of the torus fibre, which reverses
exactly the two coordinates pinned here.  The refutation is
`not_standardA2CuspSpecializationDegreeOneStatement`,
kept as a permanent regression test in `PaperCuspGeometricSpecializationProof`. -/
public theorem degreeOne
    (A : PaperAnalyticData)
    (x : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0)) :
    actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
        (integralSingularHomologyMap 1
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ x) =
      fun i ↦ A.actualCuspRadialClutchingData.geometricHomologyOneEquiv x (Fin.castAdd 1 i) := by
  rw [A.actualCuspRadialClutchingData_eq]
  exact DFunLike.congr_fun (finiteBasisNaturality A).degreeOne x

public theorem degreeTwo
    (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    cuspFillingTwoReadout A
        (integralSingularHomologyMap 2
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ x) =
      fun i ↦ A.actualCuspRadialClutchingData.geometricHomologyTwoEquiv x (Fin.castAdd 2 i) := by
  rw [A.actualCuspRadialClutchingData_eq]
  exact DFunLike.congr_fun (finiteBasisNaturality A).degreeTwo x

end Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization

namespace Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open SphereSixComplex.CircleMappingTorusHomologyBases

variable (A : PaperAnalyticData)

public noncomputable def actualCuspFillingHomologyTwoEquiv :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.filling 0) ≃+ (Fin 4 → ℤ) :=
  EstablishedStandardA2CuspSpecialization.cuspFillingTwoReadout A

/-- The corresponding dimensionally correct realization of the paper's cusp collar. -/
public noncomputable def actualCuspCollarRadialMappingTorusRealization :
    A.CuspCollarRadialMappingTorusRealization where
  radius := A.starCuspWitness.localWitness.radius
  radius_pos := A.starCuspWitness.localWitness.radius_pos
  Fiber := A.actualCuspRadialClutchingData.Fiber
  fiberTopology := A.actualCuspRadialClutchingData.fiberTopology
  clutching := A.actualCuspRadialClutchingData.clutching
  totalHomeomorph := A.actualCuspRadialClutchingData.totalHomeomorph
  monodromyCoordinates := A.actualCuspRadialClutchingData.monodromyCoordinates

/-- Raw geometrically split coordinates on the actual cusp collar. -/
public noncomputable def cuspRawHomologyOneEquiv :
    IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0) ≃+ (Fin 3 → ℤ) := by
  exact A.actualCuspRadialClutchingData.geometricHomologyOneEquiv

public noncomputable def cuspRawHomologyTwoEquiv :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) ≃+ (Fin 6 → ℤ) := by
  exact A.actualCuspRadialClutchingData.geometricHomologyTwoEquiv

/-- The actual cusp collar bases normalized for the final Section 7 attachment. -/
public noncomputable def actualCuspSectionSevenHomologyOneEquiv :
    IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0) ≃+ (Fin 3 → ℤ) :=
  A.cuspRawHomologyOneEquiv.trans cuspSectionSevenOneCoordinateChange

public noncomputable def actualCuspSectionSevenHomologyTwoEquiv :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) ≃+ (Fin 6 → ℤ) :=
  A.cuspRawHomologyTwoEquiv.trans cuspSectionSevenTwoCoordinateChange

/-- Replace only the cusp fields of any local basis package by the controlled geometric bases. -/
public noncomputable def withActualGeometricCuspBases
    (B : A.SectionSevenCollarInteriorHomologyBases) :
    A.SectionSevenCollarInteriorHomologyBases where
  cuspCollarOne := A.actualCuspSectionSevenHomologyOneEquiv
  ellipticInteriorOne := B.ellipticInteriorOne
  cuspCollarTwo := A.actualCuspSectionSevenHomologyTwoEquiv
  cuspFillingTwo := fun _ => A.actualCuspFillingHomologyTwoEquiv
  ellipticInteriorTwo := B.ellipticInteriorTwo

/-- Build the local basis package from the elliptic interior alone.

The cusp collar's own degree-one and degree-two bases are already available geometrically, so the
elliptic interior's are the only ones the package still has to be given.  `withActualGeometricCuspBases`
says the same thing but needs a package to start from; this one does not. -/
public noncomputable def sectionSevenCollarInteriorHomologyBasesOfEllipticInterior
    (ellipticOne : IntegralSingularHomology 1
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ≃+
      (Fin 1 → ℤ))
    (ellipticTwo : IntegralSingularHomology 2
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ≃+
      (Fin 2 → ℤ)) :
    A.SectionSevenCollarInteriorHomologyBases where
  cuspCollarOne := A.actualCuspSectionSevenHomologyOneEquiv
  ellipticInteriorOne := ellipticOne
  cuspCollarTwo := A.actualCuspSectionSevenHomologyTwoEquiv
  cuspFillingTwo := fun _ => A.actualCuspFillingHomologyTwoEquiv
  ellipticInteriorTwo := ellipticTwo

/-- The package built from the elliptic interior already carries the geometric cusp bases. -/
public theorem withActualGeometricCuspBases_ofEllipticInterior
    (ellipticOne : IntegralSingularHomology 1
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ≃+
      (Fin 1 → ℤ))
    (ellipticTwo : IntegralSingularHomology 2
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ≃+
      (Fin 2 → ℤ)) :
    A.withActualGeometricCuspBases
        (A.sectionSevenCollarInteriorHomologyBasesOfEllipticInterior ellipticOne ellipticTwo) =
      A.sectionSevenCollarInteriorHomologyBasesOfEllipticInterior ellipticOne ellipticTwo :=
  rfl

/-- The actual cusp inclusion has the degree-one and degree-two coordinates required by the
final Section 7 attachment. -/
public theorem actualCuspFillingInclusionCoordinates
    (B : A.SectionSevenCollarInteriorHomologyBases) :
    A.ActualCuspFillingInclusionCoordinates (A.withActualGeometricCuspBases B) where
  degreeOne x := by
    change actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
          (integralSingularHomologyMap 1
            ⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ x) = _
    rw [EstablishedStandardA2CuspSpecialization.degreeOne A x]
    exact cuspSectionSevenOneCoordinateChange_specialization
      (A.cuspRawHomologyOneEquiv x)
  degreeTwo x := by
    change A.actualCuspFillingHomologyTwoEquiv
          (integralSingularHomologyMap 2
            ⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ x) = _
    exact (EstablishedStandardA2CuspSpecialization.degreeTwo A x).trans
      (cuspSectionSevenTwoCoordinateChange_specialization
        (A.cuspRawHomologyTwoEquiv x))

end Geometry.PaperAnalyticData

end SphereSixComplex
