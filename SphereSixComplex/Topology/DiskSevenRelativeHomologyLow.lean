module

public import SphereSixComplex.Topology.SingularExcisionOpenCover
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Low-degree relative homology of the seven-disk

This file replaces the full singular chains of the seven-disk by chains subordinate to the
concrete two-set excision cover.  The replacement remains valid after quotienting by the boundary
chains: this follows formally from the unconditional small-chain approximation and the long
exact homology sequences of the two cokernel complexes.

The remaining geometric calculation is thereby isolated as acyclicity in degrees three and four
of one explicit cover-small relative chain complex.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

/-- The literal identification `S⁶ = ∂D⁷`, transported to integral singular chains. -/
public noncomputable def sphereSixChainsIsoDiskBoundarySevenChains :
    IntegralSingularChainComplexObj (TopCat.sphere 6) ≅
      IntegralSingularChainComplexObj (TopCat.diskBoundary 7) := by
  let F := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  exact F.mapIso (eqToIso topCatSphereSix_eq_diskBoundarySeven)

public theorem sphereSixChainsIsoDiskBoundarySevenChains_hom_comp_boundary :
    sphereSixChainsIsoDiskBoundarySevenChains.hom ≫
        integralSingularChainMapObj (TopCat.diskBoundaryInclusion 7) =
      diskBoundaryToDiskSevenCoverSmallIntegralSingularChains ≫
        diskSevenCoverSmallIntegralSingularChainInclusion := by
  rw [diskBoundaryToDiskSevenCoverSmallIntegralSingularChains_comp_inclusion]
  dsimp [sphereSixChainsIsoDiskBoundarySevenChains,
    integralSingularChainMapObj]
  rw [← Functor.map_comp]
  apply Functor.congr_map
  ext x
  rfl

public theorem sphereSixChainsIsoDiskBoundarySevenChains_hom_quasiIso :
    QuasiIso sphereSixChainsIsoDiskBoundarySevenChains.hom := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  infer_instance

/-- Cover-small disk chains modulo the boundary chains. -/
public noncomputable def DiskSevenCoverSmallRelativeIntegralSingularChainComplex :
    ChainComplex AddCommGrpCat ℕ :=
  cokernel diskBoundaryToDiskSevenCoverSmallIntegralSingularChains

/-- The quotient map from cover-small disk chains to the cover-small relative complex. -/
public noncomputable def diskSevenCoverSmallRelativeChainProjection :
    DiskSevenCoverSmallIntegralSingularChainComplex ⟶
      DiskSevenCoverSmallRelativeIntegralSingularChainComplex :=
  cokernel.π diskBoundaryToDiskSevenCoverSmallIntegralSingularChains

/-- The boundary-to-small-chain map is mono, since its composite with the small-chain inclusion
is the ordinary boundary inclusion on singular chains. -/
public instance diskBoundaryToDiskSevenCoverSmallIntegralSingularChains_mono :
    Mono diskBoundaryToDiskSevenCoverSmallIntegralSingularChains := by
  let _ : Mono (diskBoundaryToDiskSevenCoverSmallIntegralSingularChains ≫
      diskSevenCoverSmallIntegralSingularChainInclusion) := by
    rw [diskBoundaryToDiskSevenCoverSmallIntegralSingularChains_comp_inclusion]
    exact diskSevenSphereSix_relativeIntegralSingularShortComplex_shortExact.mono_f
  exact mono_of_mono diskBoundaryToDiskSevenCoverSmallIntegralSingularChains
    diskSevenCoverSmallIntegralSingularChainInclusion

/-- The short exact sequence defining cover-small relative chains. -/
public noncomputable def diskSevenCoverSmallRelativeShortComplex :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk diskBoundaryToDiskSevenCoverSmallIntegralSingularChains
    diskSevenCoverSmallRelativeChainProjection
    (cokernel.condition diskBoundaryToDiskSevenCoverSmallIntegralSingularChains)

public theorem diskSevenCoverSmallRelativeShortComplex_shortExact :
    diskSevenCoverSmallRelativeShortComplex.ShortExact := by
  dsimp [diskSevenCoverSmallRelativeShortComplex,
    diskSevenCoverSmallRelativeChainProjection]
  exact
    { exact := ShortComplex.exact_cokernel
        diskBoundaryToDiskSevenCoverSmallIntegralSingularChains
      mono_f := by
        change Mono diskBoundaryToDiskSevenCoverSmallIntegralSingularChains
        infer_instance
      epi_g := by
        change Epi (cokernel.π
          diskBoundaryToDiskSevenCoverSmallIntegralSingularChains)
        infer_instance }

/-- The inclusion of cover-small disk chains induces the canonical map from the cover-small
relative complex to the ordinary relative complex of `(D⁷,S⁶)`. -/
public noncomputable def diskSevenCoverSmallRelativeChainComparison :
    DiskSevenCoverSmallRelativeIntegralSingularChainComplex ⟶
      DiskSevenSphereSixRelativeIntegralSingularChainComplex :=
  cokernel.map diskBoundaryToDiskSevenCoverSmallIntegralSingularChains
    (integralSingularChainMapObj (TopCat.diskBoundaryInclusion 7))
    sphereSixChainsIsoDiskBoundarySevenChains.hom
      diskSevenCoverSmallIntegralSingularChainInclusion
      sphereSixChainsIsoDiskBoundarySevenChains_hom_comp_boundary.symm

@[reassoc (attr := simp)]
public theorem diskSevenCoverSmallRelativeChainProjection_comp_comparison :
    diskSevenCoverSmallRelativeChainProjection ≫
        diskSevenCoverSmallRelativeChainComparison =
      diskSevenCoverSmallIntegralSingularChainInclusion ≫
        relativeIntegralSingularChainProjection
          (TopCat.diskBoundaryInclusion 7) := by
  change cokernel.π diskBoundaryToDiskSevenCoverSmallIntegralSingularChains ≫
      cokernel.desc diskBoundaryToDiskSevenCoverSmallIntegralSingularChains
        (diskSevenCoverSmallIntegralSingularChainInclusion ≫
          cokernel.π (integralSingularChainMapObj
            (TopCat.diskBoundaryInclusion 7))) _ =
    diskSevenCoverSmallIntegralSingularChainInclusion ≫
      cokernel.π (integralSingularChainMapObj
        (TopCat.diskBoundaryInclusion 7))
  exact cokernel.π_desc _ _ _

/-- The defining short exact sequence for cover-small relative chains maps to the usual relative
singular-chain short exact sequence. -/
public noncomputable def diskSevenCoverSmallRelativeShortComplexComparison :
    diskSevenCoverSmallRelativeShortComplex ⟶
      relativeIntegralSingularShortComplex (TopCat.diskBoundaryInclusion 7) where
  τ₁ := sphereSixChainsIsoDiskBoundarySevenChains.hom
  τ₂ := diskSevenCoverSmallIntegralSingularChainInclusion
  τ₃ := diskSevenCoverSmallRelativeChainComparison
  comm₁₂ := by
    exact sphereSixChainsIsoDiskBoundarySevenChains_hom_comp_boundary
  comm₂₃ := diskSevenCoverSmallRelativeChainProjection_comp_comparison.symm

/-- The unconditional small-chain approximation makes the inclusion of cover-small disk chains
a quasi-isomorphism. -/
public theorem diskSevenCoverSmallIntegralSingularChainInclusion_quasiIso :
    QuasiIso diskSevenCoverSmallIntegralSingularChainInclusion := by
  change QuasiIso (coverSmallIntegralSingularChainInclusion
    (TopCat.disk.{0} 7) diskSevenExcisionCover)
  rw [← coverSmallChainHomotopyEquiv_hom
    (TopCat.disk.{0} 7) diskSevenExcisionCover diskSevenSmallChainApproximation]
  infer_instance

/-- Quotienting by the unchanged boundary complex preserves the small-chain quasi-isomorphism.
This is the formal excision reduction supplied by the two long exact homology sequences. -/
public theorem diskSevenCoverSmallRelativeChainComparison_quasiIso :
    QuasiIso diskSevenCoverSmallRelativeChainComparison := by
  apply HomologicalComplex.HomologySequence.quasiIso_τ₃
    diskSevenCoverSmallRelativeShortComplexComparison
    diskSevenCoverSmallRelativeShortComplex_shortExact
    diskSevenSphereSix_relativeIntegralSingularShortComplex_shortExact
  · dsimp [diskSevenCoverSmallRelativeShortComplexComparison]
    exact sphereSixChainsIsoDiskBoundarySevenChains_hom_quasiIso
  · dsimp [diskSevenCoverSmallRelativeShortComplexComparison]
    exact diskSevenCoverSmallIntegralSingularChainInclusion_quasiIso

/-- Cover-small relative homology computes the usual relative homology of `(D⁷,S⁶)`. -/
public noncomputable def diskSevenCoverSmallRelativeHomologyIso (n : ℕ) :
    DiskSevenCoverSmallRelativeIntegralSingularChainComplex.homology n ≅
      DiskSevenSphereSixRelativeIntegralSingularChainComplex.homology n := by
  let _ : QuasiIso diskSevenCoverSmallRelativeChainComparison :=
    diskSevenCoverSmallRelativeChainComparison_quasiIso
  exact isoOfQuasiIsoAt diskSevenCoverSmallRelativeChainComparison n

/-- In every positive sphere degree, cover-small relative homology in the next degree is the
integral singular homology of the standard sphere. -/
public noncomputable def diskSevenCoverSmallRelativeBoundaryIso
    (n : ℕ) (hn : n ≠ 0) :
    DiskSevenCoverSmallRelativeIntegralSingularChainComplex.homology (n + 1) ≅
      (IntegralSingularChainComplexObj (TopCat.diskBoundary 7)).homology n :=
  diskSevenCoverSmallRelativeHomologyIso (n + 1) ≪≫
    diskSevenSphereSix_relativeBoundaryIso n hn

/-- The same boundary isomorphism, with the target written as the standard categorical sphere
rather than the definitionally identified disk boundary. -/
public noncomputable def diskSevenCoverSmallRelativeStandardSphereBoundaryIso
    (n : ℕ) (hn : n ≠ 0) :
    DiskSevenCoverSmallRelativeIntegralSingularChainComplex.homology (n + 1) ≅
      (IntegralSingularChainComplexObj (TopCat.sphere 6)).homology n :=
  diskSevenCoverSmallRelativeBoundaryIso n hn ≪≫
    (HomologicalComplex.homologyMapIso
      sphereSixChainsIsoDiskBoundarySevenChains n).symm

/-- The exact remaining low-degree chain calculation. -/
public def DiskSevenCoverSmallRelativeLowAcyclic : Prop :=
  IsZero (DiskSevenCoverSmallRelativeIntegralSingularChainComplex.homology 3) ∧
    IsZero (DiskSevenCoverSmallRelativeIntegralSingularChainComplex.homology 4)

/-- Acyclicity of the explicit cover-small relative complex in degree three gives `H₂(S⁶;ℤ)=0`.
-/
public theorem topCatSphereSix_integralSingularHomology_two_isZero_of_coverSmallRelative
    (h : IsZero
      (DiskSevenCoverSmallRelativeIntegralSingularChainComplex.homology 3)) :
    IsZero ((IntegralSingularChainComplexObj
      (TopCat.diskBoundary 7)).homology 2) :=
  h.of_iso (diskSevenCoverSmallRelativeBoundaryIso 2 (by omega)).symm

/-- Acyclicity of the explicit cover-small relative complex in degree four gives `H₃(S⁶;ℤ)=0`.
-/
public theorem topCatSphereSix_integralSingularHomology_three_isZero_of_coverSmallRelative
    (h : IsZero
      (DiskSevenCoverSmallRelativeIntegralSingularChainComplex.homology 4)) :
    IsZero ((IntegralSingularChainComplexObj
      (TopCat.diskBoundary 7)).homology 3) :=
  h.of_iso (diskSevenCoverSmallRelativeBoundaryIso 3 (by omega)).symm

/-- The two concrete cover-small calculations imply both required low-degree vanishings. -/
public theorem topCatSphereSix_integralSingularHomology_low_isZero_of_coverSmallRelative
    (h : DiskSevenCoverSmallRelativeLowAcyclic) :
    IsZero ((IntegralSingularChainComplexObj (TopCat.diskBoundary 7)).homology 2) ∧
      IsZero ((IntegralSingularChainComplexObj (TopCat.diskBoundary 7)).homology 3) :=
  ⟨topCatSphereSix_integralSingularHomology_two_isZero_of_coverSmallRelative h.1,
    topCatSphereSix_integralSingularHomology_three_isZero_of_coverSmallRelative h.2⟩

/-- Degree-two vanishing, stated directly for `TopCat.sphere 6`. -/
public theorem standardSphereSix_integralSingularHomology_two_isZero_of_coverSmallRelative
    (h : IsZero
      (DiskSevenCoverSmallRelativeIntegralSingularChainComplex.homology 3)) :
    IsZero ((IntegralSingularChainComplexObj (TopCat.sphere 6)).homology 2) :=
  h.of_iso
    (diskSevenCoverSmallRelativeStandardSphereBoundaryIso 2 (by omega)).symm

/-- Degree-three vanishing, stated directly for `TopCat.sphere 6`. -/
public theorem standardSphereSix_integralSingularHomology_three_isZero_of_coverSmallRelative
    (h : IsZero
      (DiskSevenCoverSmallRelativeIntegralSingularChainComplex.homology 4)) :
    IsZero ((IntegralSingularChainComplexObj (TopCat.sphere 6)).homology 3) :=
  h.of_iso
    (diskSevenCoverSmallRelativeStandardSphereBoundaryIso 3 (by omega)).symm

/-- Thus the two remaining cover-small relative calculations are exactly equivalent to the two
desired standard-sphere vanishings; the small-chain and long-exact-sequence reductions lose no
information. -/
public theorem diskSevenCoverSmallRelativeLowAcyclic_iff_standardSphereSix_low_isZero :
    DiskSevenCoverSmallRelativeLowAcyclic ↔
      IsZero ((IntegralSingularChainComplexObj (TopCat.sphere 6)).homology 2) ∧
        IsZero ((IntegralSingularChainComplexObj (TopCat.sphere 6)).homology 3) := by
  constructor
  · intro h
    exact
      ⟨standardSphereSix_integralSingularHomology_two_isZero_of_coverSmallRelative h.1,
        standardSphereSix_integralSingularHomology_three_isZero_of_coverSmallRelative h.2⟩
  · rintro ⟨h₂, h₃⟩
    exact
      ⟨h₂.of_iso (diskSevenCoverSmallRelativeStandardSphereBoundaryIso 2 (by omega)),
        h₃.of_iso (diskSevenCoverSmallRelativeStandardSphereBoundaryIso 3 (by omega))⟩

end SphereSixComplex
