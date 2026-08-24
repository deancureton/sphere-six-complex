module

public import SphereSixComplex.Topology.SectionSevenPaperCoverIdentification
public import SphereSixComplex.Geometry.PaperGluingData

/-!
# A conditional Section 7 cover-to-homology bridge

This file records what follows from the strong chain-level comparison isolated by
`SectionSevenPaperCoverIdentification`.  Once local intersection models, the canonical
Čech-nerve identification, and a transferred finite-complex contraction have been constructed,
it packages them as the exact small-chain comparison required by `PaperGluingData` and derives
the integral homology-sphere conclusion.

That comparison is a sufficient criterion, not a claim made by Section 7 of the paper: the source
uses Mayer--Vietoris and a Leray spectral sequence.  Keeping this adapter separate makes every
additional chain-level input visible and lets the source-faithful realization proceed independently.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace SphereSixComplex

/-- The Section 7 cover and the assembly layer's canonical star cover are the same four open
images, with the same ordering of the central and filling pieces. -/
public theorem sectionSevenStarOpenCover_eq_openCover (A : FourPieceStarGluingData) :
    sectionSevenStarOpenCover A = A.openCover := by
  rfl

namespace SectionSevenPaperCoverIdentification

/-- Compose the concrete Section 7 identification with a proved Leray--Čech augmentation for
the actual four-piece cover.  The augmentation is an explicit input here: in particular, this
bridge does not use `establishedFiniteOpenCoverLerayCechComparison` behind the scenes. -/
public noncomputable def toFourPieceSmallChainComparison
    {A : FourPieceStarGluingData} (h : SectionSevenPaperCoverIdentification A)
    (e : FiniteOpenCoverLerayCechComparison (sectionSevenStarOpenCover A).piece) :
    SectionSevenFourPieceSmallChainComparison
      (GluedSpace A.glueData) (sectionSevenStarOpenCover A) := by
  let identification := h.toLerayCechIdentification.identification
  refine
    { comparison := identification.hom ≫ e.augmentation
      quasiIso := ?_ }
  let _ : QuasiIso identification.hom := by
    rw [quasiIso_iff]
    intro k
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso ((identification.toHomologyIso k).hom)
    infer_instance
  let _ : QuasiIso e.augmentation := e.quasiIso
  infer_instance

/-- Version of the comparison with the cover written exactly as it occurs in the
`PaperGluingData.homologyComparison` field. -/
public noncomputable def toPaperGluingHomologyComparison
    {A : FourPieceStarGluingData} (h : SectionSevenPaperCoverIdentification A)
    (e : FiniteOpenCoverLerayCechComparison (sectionSevenStarOpenCover A).piece) :
    SectionSevenFourPieceSmallChainComparison
      (GluedSpace A.glueData) A.openCover := by
  rw [← sectionSevenStarOpenCover_eq_openCover]
  exact h.toFourPieceSmallChainComparison e

/-- With explicit small-chain retraction data, the Section 7 comparison computes the integral
homology of the glued space in every degree.  This theorem uses no established open-cover or
standard-sphere result. -/
public theorem sectionSevenHomologyRealizationOfRetraction
    {A : FourPieceStarGluingData} (h : SectionSevenPaperCoverIdentification A)
    (e : FiniteOpenCoverLerayCechComparison (sectionSevenStarOpenCover A).piece)
    (d : CoverSmallChainRetractionData (TopCat.of (GluedSpace A.glueData))
      (sectionSevenStarOpenCover A).piece) :
    SectionSevenHomologyRealization (GluedSpace A.glueData) :=
  ((h.toFourPieceSmallChainComparison e).toCoherentRealizationOfRetraction d)
    |>.sectionSevenHomologyRealization

/-- The entirely explicit bridge to the project's homology-sphere contract.  Besides the actual
cover comparison and smallification data, it asks for the standard sphere's already separated
degreewise homology calculation. -/
public theorem hasIntegralHomologyOfSixSphereOfRetraction
    {A : FourPieceStarGluingData} (h : SectionSevenPaperCoverIdentification A)
    (e : FiniteOpenCoverLerayCechComparison (sectionSevenStarOpenCover A).piece)
    (d : CoverSmallChainRetractionData (TopCat.of (GluedSpace A.glueData))
      (sectionSevenStarOpenCover A).piece)
    (hSphere : SectionSevenHomologyRealization SixSphere) :
    HasIntegralHomologyOfSixSphere (GluedSpace A.glueData) :=
  hasIntegralHomologyOfSixSphere_of_sectionSevenRealizations
    (h.sectionSevenHomologyRealizationOfRetraction e d) hSphere

/-- Convenience form using the project's explicitly named classical open-cover subdivision and
standard-sphere homology inputs.  Unlike the preceding theorem, its name records that those two
general established results enter the proof. -/
public theorem hasIntegralHomologyOfSixSphere_established
    {A : FourPieceStarGluingData} (h : SectionSevenPaperCoverIdentification A)
    (e : FiniteOpenCoverLerayCechComparison (sectionSevenStarOpenCover A).piece) :
    HasIntegralHomologyOfSixSphere (GluedSpace A.glueData) :=
  (h.toFourPieceSmallChainComparison e).hasIntegralHomologyOfSixSphere

/-- The same identification supplies the standard four-piece Mayer--Vietoris exactness and the
integral homology-sphere conclusion, using the explicitly named established general theorems. -/
public theorem genericConsequences_established
    {A : FourPieceStarGluingData} (h : SectionSevenPaperCoverIdentification A)
    (e : FiniteOpenCoverLerayCechComparison (sectionSevenStarOpenCover A).piece) :
    FourPieceMayerVietorisExactness (sectionSevenStarOpenCover A) ∧
      HasIntegralHomologyOfSixSphere (GluedSpace A.glueData) :=
  (h.toFourPieceSmallChainComparison e).genericConsequences

end SectionSevenPaperCoverIdentification

end SphereSixComplex
