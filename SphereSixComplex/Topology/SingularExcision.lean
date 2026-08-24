module

public import SphereSixComplex.Topology.DiskBoundaryQuotient
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Small singular chains for excision

This file builds the first chain-level layer of the singular excision argument.  Given a family
of subsets of a space, the small singular subcomplex consists of the singular simplices which
factor through one member of the family.  Its chain complex maps canonically and monomorphically
to the full singular chain complex, and every cover-member chain map factors through it.

The classical subdivision theorem says that, for an open cover, this inclusion is a chain-homotopy
equivalence.  The definitions below state that next step using mathlib's actual `HomotopyEquiv`
API and prove its full homological consequence.  Mathlib's current simplicial subdivision functor
does not yet provide a last-vertex map, a subdivision chain map, or its chain homotopy to the
identity, so that theorem cannot yet be constructed from library primitives.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set

namespace SphereSixComplex

section SmallChains

variable {ι : Type} (X : TopCat) (U : ι → Set X)

/-- The categorical inclusion of a topological subspace. -/
public noncomputable def topologicalSubsetInclusion (s : Set X) :
    TopCat.of s ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Singular simplices which factor through one member of `U`. -/
public noncomputable def coverSmallSingularSubcomplex :
    (TopCat.toSSet.obj X).Subcomplex :=
  ⨆ j, SSet.Subcomplex.range
    (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))

public theorem mem_coverSmallSingularSubcomplex_iff
    {n : SimplexCategoryᵒᵖ} (x : (TopCat.toSSet.obj X).obj n) :
    x ∈ (coverSmallSingularSubcomplex X U).obj n ↔
      ∃ j, x ∈ (SSet.Subcomplex.range
        (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))).obj n := by
  simp [coverSmallSingularSubcomplex]

/-- Membership means exactly that the singular simplex is the image of a simplex in one cover
member. -/
public theorem mem_coverSmallSingularSubcomplex_iff_exists_preimage
    {n : SimplexCategoryᵒᵖ} (x : (TopCat.toSSet.obj X).obj n) :
    x ∈ (coverSmallSingularSubcomplex X U).obj n ↔
      ∃ (j : ι) (y : (TopCat.toSSet.obj (TopCat.of (U j))).obj n),
        (TopCat.toSSet.map (topologicalSubsetInclusion X (U j))).app n y = x := by
  simp [mem_coverSmallSingularSubcomplex_iff, Subfunctor.range_obj]

/-- Integral chains on the cover-small singular simplicial set. -/
public noncomputable abbrev CoverSmallIntegralSingularChainComplex :
    ChainComplex AddCommGrpCat ℕ :=
  (coverSmallSingularSubcomplex X U : SSet).chainComplex (AddCommGrpCat.of ℤ)

/-- Inclusion of cover-small integral singular chains into all integral singular chains. -/
public noncomputable def coverSmallIntegralSingularChainInclusion :
    CoverSmallIntegralSingularChainComplex X U ⟶ IntegralSingularChainComplexObj X :=
  SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι (AddCommGrpCat.of ℤ)

instance coverSmallIntegralSingularChainInclusion_mono :
    Mono (coverSmallIntegralSingularChainInclusion X U) := by
  dsimp [coverSmallIntegralSingularChainInclusion, SSet.chainComplexMap,
    SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono
  apply +allowSynthFailures Functor.map_mono
  dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
  infer_instance

/-- The singular set of each cover member factors through the small singular subcomplex. -/
public noncomputable def coverMemberToSmallSingularSet (j : ι) :
    TopCat.toSSet.obj (TopCat.of (U j)) ⟶ coverSmallSingularSubcomplex X U :=
  SSet.Subcomplex.lift
    (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))
    ((le_iSup (fun k ↦ SSet.Subcomplex.range
      (TopCat.toSSet.map (topologicalSubsetInclusion X (U k)))) j))

@[reassoc (attr := simp)]
public theorem coverMemberToSmallSingularSet_comp_inclusion (j : ι) :
    coverMemberToSmallSingularSet X U j ≫ (coverSmallSingularSubcomplex X U).ι =
      TopCat.toSSet.map (topologicalSubsetInclusion X (U j)) :=
  SSet.Subcomplex.lift_ι _ _

/-- The chain map from a cover member into the small singular chains. -/
public noncomputable def coverMemberToSmallIntegralSingularChains (j : ι) :
    IntegralSingularChainComplexObj (TopCat.of (U j)) ⟶
      CoverSmallIntegralSingularChainComplex X U :=
  SSet.chainComplexMap (coverMemberToSmallSingularSet X U j) (AddCommGrpCat.of ℤ)

/-- Chains from a cover member factor coherently through the small-chain inclusion. -/
@[reassoc]
public theorem coverMemberToSmallIntegralSingularChains_comp_inclusion (j : ι) :
    coverMemberToSmallIntegralSingularChains X U j ≫
        coverSmallIntegralSingularChainInclusion X U =
      integralSingularChainMapObj (topologicalSubsetInclusion X (U j)) := by
  change
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (coverMemberToSmallSingularSet X U j) ≫
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (coverSmallSingularSubcomplex X U).ι =
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))
  rw [← Functor.map_comp, coverMemberToSmallSingularSet_comp_inclusion]

/-- The chain-level output of the classical subdivision-and-prism argument: a map which makes
chains small, together with the two chain homotopies required for a homotopy inverse.  This is
strictly algebraic data, rather than a homology-isomorphism assumption. -/
public structure CoverSmallChainRetractionData where
  /-- A chain map sending arbitrary singular chains to cover-small chains. -/
  smallify : IntegralSingularChainComplexObj X ⟶ CoverSmallIntegralSingularChainComplex X U
  /-- Smallifying after inclusion is chain-homotopic to the identity on small chains. -/
  homotopyInclusionSmallify :
    Homotopy (coverSmallIntegralSingularChainInclusion X U ≫ smallify)
      (𝟙 (CoverSmallIntegralSingularChainComplex X U))
  /-- Including after smallifying is chain-homotopic to the identity on all singular chains. -/
  homotopySmallifyInclusion :
    Homotopy (smallify ≫ coverSmallIntegralSingularChainInclusion X U)
      (𝟙 (IntegralSingularChainComplexObj X))

/-- Retraction data packages directly into mathlib's chain-homotopy equivalence. -/
public noncomputable def CoverSmallChainRetractionData.toHomotopyEquiv
    (d : CoverSmallChainRetractionData X U) :
    HomotopyEquiv (CoverSmallIntegralSingularChainComplex X U)
      (IntegralSingularChainComplexObj X) where
  hom := coverSmallIntegralSingularChainInclusion X U
  inv := d.smallify
  homotopyHomInvId := d.homotopyInclusionSmallify
  homotopyInvHomId := d.homotopySmallifyInclusion

/-- The exact small-chain approximation assertion supplied classically by iterated barycentric
subdivision and its prism chain homotopy. -/
public def CoverSmallChainApproximation : Prop :=
  HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.down ℕ)
    (coverSmallIntegralSingularChainInclusion X U)

/-- Explicit subdivision retraction data proves the small-chain approximation theorem. -/
public theorem CoverSmallChainRetractionData.approximation
    (d : CoverSmallChainRetractionData X U) :
    CoverSmallChainApproximation X U :=
  ⟨d.toHomotopyEquiv, rfl⟩

/-- A selected chain-homotopy equivalence witnessing small-chain approximation. -/
public noncomputable def coverSmallChainHomotopyEquiv
    (h : CoverSmallChainApproximation X U) :
    HomotopyEquiv (CoverSmallIntegralSingularChainComplex X U)
      (IntegralSingularChainComplexObj X) :=
  h.choose

public theorem coverSmallChainHomotopyEquiv_hom
    (h : CoverSmallChainApproximation X U) :
    (coverSmallChainHomotopyEquiv X U h).hom =
      coverSmallIntegralSingularChainInclusion X U :=
  h.choose_spec

/-- Small-chain approximation gives the expected homology isomorphism in every degree. -/
public noncomputable def coverSmallIntegralSingularHomologyIso
    (h : CoverSmallChainApproximation X U) (n : ℕ) :
    (CoverSmallIntegralSingularChainComplex X U).homology n ≅
      (IntegralSingularChainComplexObj X).homology n :=
  (coverSmallChainHomotopyEquiv X U h).toHomologyIso n

public theorem coverSmallIntegralSingularHomologyIso_hom
    (h : CoverSmallChainApproximation X U) (n : ℕ) :
    (coverSmallIntegralSingularHomologyIso X U h n).hom =
      HomologicalComplex.homologyMap
        (coverSmallIntegralSingularChainInclusion X U) n := by
  dsimp [coverSmallIntegralSingularHomologyIso]
  change HomologicalComplex.homologyMap (coverSmallChainHomotopyEquiv X U h).hom n = _
  rw [coverSmallChainHomotopyEquiv_hom]

/-- A subspace equal to the whole space is homeomorphic to the ambient space by its inclusion. -/
public noncomputable def topologicalSubsetHomeomorphOfEqUniv
    (s : Set X) (hs : s = Set.univ) : s ≃ₜ X :=
  (Homeomorph.setCongr hs).trans (Homeomorph.Set.univ X)

/-- The subspace inclusion is an isomorphism when the subset is all of `X`. -/
public theorem topologicalSubsetInclusion_isIso_of_eq_univ
    (s : Set X) (hs : s = Set.univ) :
    IsIso (topologicalSubsetInclusion X s) := by
  change IsIso (TopCat.isoOfHomeo
    (X := TopCat.of s) (Y := X) (topologicalSubsetHomeomorphOfEqUniv X s hs)).hom
  infer_instance

/-- If one cover member is the whole space, every singular simplex is already small. -/
public theorem coverSmallSingularSubcomplex_eq_top_of_member_eq_univ
    (j : ι) (hj : U j = Set.univ) :
    coverSmallSingularSubcomplex X U = ⊤ := by
  let _ := topologicalSubsetInclusion_isIso_of_eq_univ X (U j) hj
  have hrange : SSet.Subcomplex.range
      (TopCat.toSSet.map (topologicalSubsetInclusion X (U j))) = ⊤ :=
    SSet.Subcomplex.range_eq_top _
  apply top_unique
  rw [← hrange]
  exact le_iSup (fun k ↦ SSet.Subcomplex.range
    (TopCat.toSSet.map (topologicalSubsetInclusion X (U k)))) j

/-- For a cover containing the whole space, the small-chain inclusion is an isomorphism. -/
public theorem coverSmallIntegralSingularChainInclusion_isIso_of_member_eq_univ
    (j : ι) (hj : U j = Set.univ) :
    IsIso (coverSmallIntegralSingularChainInclusion X U) := by
  let htop := coverSmallSingularSubcomplex_eq_top_of_member_eq_univ X U j hj
  let e : (coverSmallSingularSubcomplex X U : SSet) ≅ TopCat.toSSet.obj X :=
    SSet.Subcomplex.eqToIso htop ≪≫ SSet.Subcomplex.topIso _
  have he : e.hom = (coverSmallSingularSubcomplex X U).ι := by
    dsimp [e]
    exact SSet.Subcomplex.homOfLE_ι htop.le
  change IsIso (((SSet.chainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).map (coverSmallSingularSubcomplex X U).ι)
  rw [← he]
  infer_instance

/-- The small-chain approximation theorem holds directly for a cover containing the whole
space, without subdivision. -/
public theorem coverSmallChainApproximation_of_member_eq_univ
    (j : ι) (hj : U j = Set.univ) :
    CoverSmallChainApproximation X U := by
  let _ := coverSmallIntegralSingularChainInclusion_isIso_of_member_eq_univ X U j hj
  exact HomologicalComplex.homotopyEquivalences.of_isIso _

end SmallChains

section DiskSevenCover

/-- The center of the closed seven-disk. -/
public noncomputable def diskSevenCenter : TopCat.disk.{0} 7 :=
  ULift.up ⟨0, by simp [Metric.mem_closedBall]⟩

/-- A concrete two-set cover used for the disk-boundary excision argument.  One member avoids the
center and contains the boundary; the other is the disk interior. -/
public noncomputable def diskSevenExcisionCover : Bool → Set (TopCat.disk.{0} 7) :=
  fun b ↦ if b then
    {x | x ∉ Set.range (TopCat.diskBoundaryInclusion.{0} 7)}
  else {diskSevenCenter}ᶜ

/-- Both members of the concrete disk cover are open. -/
public theorem diskSevenExcisionCover_isOpen (b : Bool) :
    IsOpen (diskSevenExcisionCover b) := by
  let _ : T2Space (TopCat.disk.{0} 7 : Type) := Homeomorph.ulift.symm.t2Space
  cases b
  · exact isClosed_singleton.isOpen_compl
  · simpa [diskSevenExcisionCover] using diskSevenCollapseComplement_isOpen

/-- The center of the disk is not on its boundary. -/
public theorem diskSevenCenter_not_mem_boundary_range :
    diskSevenCenter ∉ Set.range (TopCat.diskBoundaryInclusion.{0} 7) := by
  rintro ⟨y, hy⟩
  have hxy : y.down.1 = diskSevenCenter.down.1 :=
    congrArg (fun z : TopCat.disk.{0} 7 ↦ z.down.1) hy
  have hyNorm : ‖y.down.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using y.down.2
  have : y.down.1 = 0 := by simpa [diskSevenCenter] using hxy
  simp [this] at hyNorm

/-- The concrete two-set family covers the entire disk. -/
public theorem diskSevenExcisionCover_iUnion :
    ⋃ b, diskSevenExcisionCover b = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x = diskSevenCenter
  · apply Set.mem_iUnion.2
    refine ⟨true, ?_⟩
    simp only [diskSevenExcisionCover, if_true, Set.mem_ofPred_eq]
    simpa [hx] using diskSevenCenter_not_mem_boundary_range
  · apply Set.mem_iUnion.2
    refine ⟨false, ?_⟩
    simpa [diskSevenExcisionCover]

/-- The disk boundary misses the center, hence lands in the second member of the cover. -/
public theorem diskBoundaryInclusion_mem_diskSevenExcisionCover_false
    (x : TopCat.sphere.{0} 6) :
    TopCat.diskBoundaryInclusion 7 x ∈ diskSevenExcisionCover false := by
  simp only [diskSevenExcisionCover]
  intro hcenter
  exact diskSevenCenter_not_mem_boundary_range ⟨x, hcenter⟩

/-- The boundary inclusion, regarded as a map into the disk-minus-center cover member. -/
public noncomputable def diskBoundaryToDiskSevenExcisionCoverFalse :
    TopCat.sphere.{0} 6 ⟶ TopCat.of (diskSevenExcisionCover false) :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨TopCat.diskBoundaryInclusion 7 x,
        diskBoundaryInclusion_mem_diskSevenExcisionCover_false x⟩,
      (TopCat.diskBoundaryInclusion 7).hom.continuous.subtype_mk _⟩

@[reassoc (attr := simp)]
public theorem diskBoundaryToDiskSevenExcisionCoverFalse_comp_inclusion :
    diskBoundaryToDiskSevenExcisionCoverFalse ≫
      topologicalSubsetInclusion (TopCat.disk.{0} 7) (diskSevenExcisionCover false) =
        TopCat.diskBoundaryInclusion 7 := by
  ext x
  rfl

/-- The boundary singular chain map factors through the concrete cover-small disk chains. -/
public noncomputable def diskBoundaryToDiskSevenCoverSmallIntegralSingularChains :
    IntegralSingularChainComplexObj (TopCat.sphere.{0} 6) ⟶
      CoverSmallIntegralSingularChainComplex (TopCat.disk.{0} 7) diskSevenExcisionCover :=
  integralSingularChainMapObj diskBoundaryToDiskSevenExcisionCoverFalse ≫
    coverMemberToSmallIntegralSingularChains
      (TopCat.disk.{0} 7) diskSevenExcisionCover false

@[reassoc]
public theorem diskBoundaryToDiskSevenCoverSmallIntegralSingularChains_comp_inclusion :
    diskBoundaryToDiskSevenCoverSmallIntegralSingularChains ≫
        coverSmallIntegralSingularChainInclusion
          (TopCat.disk.{0} 7) diskSevenExcisionCover =
      integralSingularChainMapObj (TopCat.diskBoundaryInclusion 7) := by
  rw [diskBoundaryToDiskSevenCoverSmallIntegralSingularChains, Category.assoc,
    coverMemberToSmallIntegralSingularChains_comp_inclusion]
  change
    ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          diskBoundaryToDiskSevenExcisionCoverFalse ≫
        ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (topologicalSubsetInclusion (TopCat.disk.{0} 7)
            (diskSevenExcisionCover false)) =
      ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.diskBoundaryInclusion 7)
  rw [← Functor.map_comp, diskBoundaryToDiskSevenExcisionCoverFalse_comp_inclusion]
  rfl

/-- Cover-small integral singular chains for the concrete disk cover. -/
public noncomputable abbrev DiskSevenCoverSmallIntegralSingularChainComplex :
    ChainComplex AddCommGrpCat ℕ :=
  CoverSmallIntegralSingularChainComplex (TopCat.disk.{0} 7) diskSevenExcisionCover

/-- Inclusion of concrete cover-small disk chains into all disk singular chains. -/
public noncomputable abbrev diskSevenCoverSmallIntegralSingularChainInclusion :
    DiskSevenCoverSmallIntegralSingularChainComplex ⟶
      IntegralSingularChainComplexObj (TopCat.disk.{0} 7) :=
  coverSmallIntegralSingularChainInclusion (TopCat.disk.{0} 7) diskSevenExcisionCover

/-- The exact next subdivision theorem for the disk: iterated barycentric subdivision should make
every singular chain small for the concrete two-open-set cover, compatibly up to chain homotopy. -/
public def DiskSevenSmallChainApproximation : Prop :=
  CoverSmallChainApproximation (TopCat.disk.{0} 7) diskSevenExcisionCover

/-- A proof of the concrete subdivision theorem would identify cover-small and full disk
homology. -/
public noncomputable def diskSevenCoverSmallHomologyIso
    (h : DiskSevenSmallChainApproximation) (n : ℕ) :
    DiskSevenCoverSmallIntegralSingularChainComplex.homology n ≅
      (IntegralSingularChainComplexObj (TopCat.disk.{0} 7)).homology n :=
  coverSmallIntegralSingularHomologyIso (TopCat.disk.{0} 7)
    diskSevenExcisionCover h n

end DiskSevenCover

end SphereSixComplex
