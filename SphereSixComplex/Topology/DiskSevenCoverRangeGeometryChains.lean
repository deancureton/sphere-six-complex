module

public import SphereSixComplex.Topology.DiskSevenCoverGeometry
public import SphereSixComplex.Topology.DiskSevenRelativeHomologyLowAcyclic
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Geometric identifications of the seven-disk cover range complexes

This file transfers the explicit topology of `diskSevenExcisionCover` to the range subcomplexes
used by the local relative Mayer--Vietoris calculation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits ContinuousMap Set

namespace SphereSixComplex

/-- Inclusion of either cover member into the disk is a monomorphism. -/
public instance diskSevenCoverSubsetInclusion_mono (b : Bool) :
    Mono (topologicalSubsetInclusion (TopCat.disk.{0} 7)
      (diskSevenExcisionCover b)) := by
  rw [TopCat.mono_iff_injective]
  exact Subtype.val_injective

/-- The induced map of singular simplicial sets is a monomorphism. -/
public instance diskSevenCoverSubsetSingularSetInclusion_mono (b : Bool) :
    Mono (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.disk.{0} 7)
      (diskSevenExcisionCover b))) := by
  apply Functor.map_mono

/-- Because subspace inclusion is injective, its singular simplicial set is isomorphic to its
range subcomplex. -/
public instance diskSevenCoverMemberToRangeSingularSet_isIso (b : Bool) :
    IsIso (diskSevenCoverMemberToRangeSingularSet b) := by
  change IsIso (SSet.Subcomplex.toRange
    (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.disk.{0} 7)
      (diskSevenExcisionCover b))))
  infer_instance

/-- The singular simplicial set of a cover member, identified with its range in the disk. -/
public noncomputable def diskSevenCoverMemberRangeSingularSetIso (b : Bool) :
    TopCat.toSSet.obj (TopCat.of (diskSevenExcisionCover b)) ≅
      (diskSevenCoverRangeSubcomplex b : SSet) :=
  asIso (diskSevenCoverMemberToRangeSingularSet b)

/-- The chain map from a cover member to its range complex. -/
public noncomputable def diskSevenCoverMemberToRangeChains (b : Bool) :
    IntegralSingularChainComplexObj (TopCat.of (diskSevenExcisionCover b)) ⟶
      DiskSevenCoverRangeChainComplex b :=
  SSet.chainComplexMap (diskSevenCoverMemberToRangeSingularSet b)
    (AddCommGrpCat.of ℤ)

/-- Integral singular chains of a cover member are isomorphic to chains on the corresponding
range subcomplex. -/
public noncomputable def diskSevenCoverMemberRangeChainsIso (b : Bool) :
    IntegralSingularChainComplexObj (TopCat.of (diskSevenExcisionCover b)) ≅
      DiskSevenCoverRangeChainComplex b :=
  ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).mapIso
    (diskSevenCoverMemberRangeSingularSetIso b)

@[simp]
public theorem diskSevenCoverMemberRangeChainsIso_hom (b : Bool) :
    (diskSevenCoverMemberRangeChainsIso b).hom =
      diskSevenCoverMemberToRangeChains b :=
  rfl

/-- The induced degreewise homology identification for a cover member and its range. -/
public noncomputable def diskSevenCoverMemberRangeHomologyIso (b : Bool) (k : ℕ) :
    (IntegralSingularChainComplexObj
        (TopCat.of (diskSevenExcisionCover b))).homology k ≅
      (DiskSevenCoverRangeChainComplex b).homology k :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat
    (ComplexShape.down ℕ) k).mapIso (diskSevenCoverMemberRangeChainsIso b)

/-- Singular homology objects are invariant under a specified topological homotopy equivalence. -/
public noncomputable def integralSingularHomologyIsoOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (k : ℕ) (e : X ≃ₕ Y) :
    (((singularHomologyFunctor AddCommGrpCat k).obj
        (AddCommGrpCat.of ℤ)).obj (TopCat.of X)) ≅
      (((singularHomologyFunctor AddCommGrpCat k).obj
        (AddCommGrpCat.of ℤ)).obj (TopCat.of Y)) := by
  let F := (singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  exact CategoryTheory.Iso.mk (F.map f) (F.map g) (by
    rw [← F.map_comp, ← F.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      e.left_inv.some (AddCommGrpCat.of ℤ) k) (by
    rw [← F.map_comp, ← F.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      e.right_inv.some (AddCommGrpCat.of ℤ) k)

/-- Every positive-degree integral homology object of the true range vanishes. -/
public theorem diskSevenCoverTrueRange_homology_isZero
    (k : ℕ) (hk : k ≠ 0) :
    IsZero ((DiskSevenCoverRangeChainComplex true).homology k) := by
  let _ : ContractibleSpace
      (diskSevenExcisionCover true : Set (TopCat.disk.{0} 7)) :=
    diskSevenCoverTrue_contractibleSpace
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit
    (diskSevenExcisionCover true : Set (TopCat.disk.{0} 7))
  have hunit :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      AddCommGrpCat k (AddCommGrpCat.of ℤ) (TopCat.of Unit) hk
  have hmember : IsZero
      ((IntegralSingularChainComplexObj
        (TopCat.of (diskSevenExcisionCover true))).homology k) :=
    by
      change IsZero (((singularHomologyFunctor AddCommGrpCat k).obj
        (AddCommGrpCat.of ℤ)).obj
          (TopCat.of (diskSevenExcisionCover true)))
      exact hunit.of_iso (integralSingularHomologyIsoOfHomotopyEquiv k e)
  exact hmember.of_iso (diskSevenCoverMemberRangeHomologyIso true k).symm

/-- The boundary inclusion into the false member is a chain-homotopy equivalence. -/
public noncomputable def diskBoundaryToDiskSevenFalseMemberChainsHomotopyEquiv :
    HomotopyEquiv
      (IntegralSingularChainComplexObj (TopCat.sphere.{0} 6))
      (IntegralSingularChainComplexObj
        (TopCat.of (diskSevenExcisionCover false))) where
  hom := integralSingularChainMapObj
    diskBoundaryToDiskSevenExcisionCoverFalse
  inv := integralSingularChainMapObj diskSevenFalseRadialRetraction
  homotopyHomInvId := by
    let F := (singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)
    let h₁ : Homotopy
        (F.map diskBoundaryToDiskSevenExcisionCoverFalse ≫
          F.map diskSevenFalseRadialRetraction)
        (F.map (𝟙 (TopCat.sphere.{0} 6))) :=
      Homotopy.ofEq (by
        rw [← F.map_comp,
          diskBoundaryToDiskSevenExcisionCoverFalse_comp_radialRetraction])
    let h₂ : Homotopy (F.map (𝟙 (TopCat.sphere.{0} 6))) (𝟙 _) :=
      Homotopy.ofEq (F.map_id _)
    simpa only [integralSingularChainMapObj] using h₁.trans h₂
  homotopyInvHomId := by
    let F := (singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)
    let h₀ : Homotopy
        (F.map diskSevenFalseRadialRetraction ≫
          F.map diskBoundaryToDiskSevenExcisionCoverFalse)
        (F.map (diskSevenFalseRadialRetraction ≫
          diskBoundaryToDiskSevenExcisionCoverFalse)) :=
      Homotopy.ofEq (F.map_comp _ _).symm
    let h₁ := diskSevenFalseRadialHomotopy.singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)
    let h₂ : Homotopy
        (F.map (𝟙 (TopCat.of (diskSevenExcisionCover false)))) (𝟙 _) :=
      Homotopy.ofEq (F.map_id _)
    simpa only [integralSingularChainMapObj] using h₀.trans (h₁.trans h₂)

/-- Composing the preceding equivalence with the member-range chain isomorphism gives the exact
boundary-to-false-range chain map used by the relative complex. -/
public noncomputable def diskBoundaryToDiskSevenFalseRangeChainsHomotopyEquiv :
    HomotopyEquiv
      (IntegralSingularChainComplexObj (TopCat.sphere.{0} 6))
      (DiskSevenCoverRangeChainComplex false) :=
  diskBoundaryToDiskSevenFalseMemberChainsHomotopyEquiv.trans
    (HomotopyEquiv.ofIso (diskSevenCoverMemberRangeChainsIso false))

@[simp]
public theorem diskBoundaryToDiskSevenFalseRangeChainsHomotopyEquiv_hom :
    diskBoundaryToDiskSevenFalseRangeChainsHomotopyEquiv.hom =
      diskBoundaryToDiskSevenFalseRangeChains :=
  rfl

/-- The boundary-to-false-range map is a quasi-isomorphism. -/
public theorem diskBoundaryToDiskSevenFalseRangeChains_quasiIso :
    QuasiIso diskBoundaryToDiskSevenFalseRangeChains := by
  rw [← diskBoundaryToDiskSevenFalseRangeChainsHomotopyEquiv_hom]
  infer_instance

/-- The boundary-to-false-member map is a monomorphism. -/
public instance diskBoundaryToDiskSevenExcisionCoverFalse_mono :
    Mono diskBoundaryToDiskSevenExcisionCoverFalse := by
  rw [TopCat.mono_iff_injective]
  intro x y h
  apply ULift.ext
  apply Subtype.ext
  exact congrArg (fun z ↦ z.1.down.1) h

/-- The boundary-to-false-range chain map is degreewise injective. -/
public instance diskBoundaryToDiskSevenFalseRangeChains_mono :
    Mono diskBoundaryToDiskSevenFalseRangeChains := by
  let _ : Mono (integralSingularChainMapObj
      diskBoundaryToDiskSevenExcisionCoverFalse) := by
    dsimp [integralSingularChainMapObj]
    apply Functor.map_mono
  let _ : Mono (diskSevenCoverMemberToRangeChains false) := by
    rw [← diskSevenCoverMemberRangeChainsIso_hom]
    infer_instance
  change Mono
    (integralSingularChainMapObj diskBoundaryToDiskSevenExcisionCoverFalse ≫
      diskSevenCoverMemberToRangeChains false)
  infer_instance

/-- The standard cokernel sequence defining the false relative range complex. -/
public noncomputable def diskSevenFalseRangeRelativeShortComplex :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk diskBoundaryToDiskSevenFalseRangeChains
    diskSevenFalseRangeRelativeProjection
    (cokernel.condition diskBoundaryToDiskSevenFalseRangeChains)

/-- That cokernel sequence is short exact. -/
public theorem diskSevenFalseRangeRelativeShortComplex_shortExact :
    diskSevenFalseRangeRelativeShortComplex.ShortExact :=
  { exact := ShortComplex.exact_cokernel
      diskBoundaryToDiskSevenFalseRangeChains
    mono_f := by
      dsimp [diskSevenFalseRangeRelativeShortComplex]
      infer_instance
    epi_g := by
      dsimp [diskSevenFalseRangeRelativeShortComplex,
        diskSevenFalseRangeRelativeProjection]
      constructor
      intro Z g h w
      exact Cofork.IsColimit.hom_ext
        (cokernelIsCokernel diskBoundaryToDiskSevenFalseRangeChains) w }

/-- The false-range relative chain complex is acyclic in every degree. -/
public theorem diskSevenFalseRangeRelativeChainComplex_acyclic :
    DiskSevenFalseRangeRelativeChainComplex.Acyclic := by
  have hq : QuasiIso diskSevenFalseRangeRelativeShortComplex.f := by
    exact diskBoundaryToDiskSevenFalseRangeChains_quasiIso
  exact diskSevenFalseRangeRelativeShortComplex_shortExact.acyclic_X₃ hq

/-- Consequently every homology object of the false-range relative complex vanishes. -/
public theorem diskSevenFalseRangeRelativeChainComplex_homology_isZero (k : ℕ) :
    IsZero (DiskSevenFalseRangeRelativeChainComplex.homology k) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact diskSevenFalseRangeRelativeChainComplex_acyclic k

/-- Homology of the local relative middle complex is the biproduct of the homologies of its two
summands. -/
public noncomputable def diskSevenCoverLocalRelativeMiddleHomologyIso (k : ℕ) :
    DiskSevenCoverLocalRelativeMiddleChainComplex.homology k ≅
      (DiskSevenCoverRangeChainComplex true).homology k ⊞
        DiskSevenFalseRangeRelativeChainComplex.homology k :=
  by
    let F := HomologicalComplex.homologyFunctor AddCommGrpCat
      (ComplexShape.down ℕ) k
    letI : F.Additive := inferInstance
    letI : PreservesFiniteBiproducts F := inferInstance
    letI : PreservesBinaryBiproducts F :=
      preservesBinaryBiproducts_of_preservesBiproducts F
    exact F.mapBiprod _ _

/-- The local relative middle homology vanishes in every positive degree. -/
public theorem diskSevenCoverLocalRelativeMiddle_homology_isZero
    (k : ℕ) (hk : k ≠ 0) :
    IsZero (DiskSevenCoverLocalRelativeMiddleChainComplex.homology k) := by
  have hsum : IsZero
      ((DiskSevenCoverRangeChainComplex true).homology k ⊞
        DiskSevenFalseRangeRelativeChainComplex.homology k) :=
    (biprod_isZero_iff _ _).2
      ⟨diskSevenCoverTrueRange_homology_isZero k hk,
        diskSevenFalseRangeRelativeChainComplex_homology_isZero k⟩
  exact hsum.of_iso (diskSevenCoverLocalRelativeMiddleHomologyIso k)

/-- The two middle homology objects needed by local relative Mayer--Vietoris vanish. -/
public theorem diskSevenCoverLocalRelativeMiddle_low_isZero :
    IsZero (DiskSevenCoverLocalRelativeMiddleChainComplex.homology 3) ∧
      IsZero (DiskSevenCoverLocalRelativeMiddleChainComplex.homology 4) :=
  ⟨diskSevenCoverLocalRelativeMiddle_homology_isZero 3 (by omega),
    diskSevenCoverLocalRelativeMiddle_homology_isZero 4 (by omega)⟩

/-! ## The range intersection -/

/-- Forgetting the false-member condition includes the punctured interior in the true member. -/
public noncomputable def diskSevenIntersectionToTrue :
    TopCat.of DiskSevenCoverIntersection ⟶
      TopCat.of (diskSevenExcisionCover true) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, x.2.1⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Direct inclusion of the punctured interior in the ambient disk. -/
public noncomputable def diskSevenCoverIntersectionToDisk :
    TopCat.of DiskSevenCoverIntersection ⟶ TopCat.disk.{0} 7 :=
  topologicalSubsetInclusion (TopCat.disk.{0} 7)
    (diskSevenExcisionCover true ∩ diskSevenExcisionCover false)

@[reassoc (attr := simp)]
public theorem diskSevenIntersectionToTrue_comp_disk :
    diskSevenIntersectionToTrue ≫
        topologicalSubsetInclusion (TopCat.disk.{0} 7)
          (diskSevenExcisionCover true) =
      diskSevenCoverIntersectionToDisk := by
  rfl

@[reassoc (attr := simp)]
public theorem diskSevenIntersectionToFalse_comp_disk :
    diskSevenIntersectionToFalse ≫
        topologicalSubsetInclusion (TopCat.disk.{0} 7)
          (diskSevenExcisionCover false) =
      diskSevenCoverIntersectionToDisk := by
  rfl

/-- Singular simplices of the punctured interior land in both member ranges. -/
public theorem diskSevenCoverIntersection_range_le_rangeIntersection :
    SSet.Subcomplex.range
        (TopCat.toSSet.map diskSevenCoverIntersectionToDisk) ≤
      diskSevenCoverRangeIntersectionSubcomplex := by
  apply le_inf
  · rw [← diskSevenIntersectionToTrue_comp_disk,
      Functor.map_comp]
    exact Subfunctor.range_comp_le _ _
  · rw [← diskSevenIntersectionToFalse_comp_disk,
      Functor.map_comp]
    exact Subfunctor.range_comp_le _ _

/-- The singular simplicial set of the punctured interior, lifted to the intersection of the two
member ranges. -/
public noncomputable def diskSevenCoverIntersectionToRangeIntersectionSingularSet :
    TopCat.toSSet.obj (TopCat.of DiskSevenCoverIntersection) ⟶
      (diskSevenCoverRangeIntersectionSubcomplex : SSet) :=
  SSet.Subcomplex.lift (TopCat.toSSet.map diskSevenCoverIntersectionToDisk)
    diskSevenCoverIntersection_range_le_rangeIntersection

/-- Direct inclusion of the punctured interior is a monomorphism. -/
public instance diskSevenCoverIntersectionToDisk_mono :
    Mono diskSevenCoverIntersectionToDisk := by
  rw [TopCat.mono_iff_injective]
  exact Subtype.val_injective

/-- Its lift to the intersection range remains a monomorphism. -/
public instance diskSevenCoverIntersectionToRangeIntersectionSingularSet_mono :
    Mono diskSevenCoverIntersectionToRangeIntersectionSingularSet := by
  apply mono_of_mono_fac
    (SSet.Subcomplex.lift_ι
      (TopCat.toSSet.map diskSevenCoverIntersectionToDisk)
      diskSevenCoverIntersection_range_le_rangeIntersection)

/-- Every simplex in both member ranges has a unique lift to the punctured interior. -/
public theorem diskSevenCoverIntersectionToRangeIntersection_app_surjective
    (n : SimplexCategoryᵒᵖ) :
    Function.Surjective
      (diskSevenCoverIntersectionToRangeIntersectionSingularSet.app n) := by
  intro z
  have hz := z.2
  change
    z.1 ∈ (diskSevenCoverRangeSubcomplex true).obj n ∧
      z.1 ∈ (diskSevenCoverRangeSubcomplex false).obj n at hz
  rcases hz with ⟨hzTrue, hzFalse⟩
  change z.1 ∈ (SSet.Subcomplex.range
    (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.disk.{0} 7)
      (diskSevenExcisionCover true)))).obj n at hzTrue
  change z.1 ∈ (SSet.Subcomplex.range
    (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.disk.{0} 7)
      (diskSevenExcisionCover false)))).obj n at hzFalse
  rw [Subfunctor.range_obj] at hzTrue hzFalse
  obtain ⟨yTrue, hyTrue⟩ := hzTrue
  obtain ⟨yFalse, hyFalse⟩ := hzFalse
  let fTrue := (TopCat.of (diskSevenExcisionCover true)).toSSetObjEquiv n yTrue
  let fFalse := (TopCat.of (diskSevenExcisionCover false)).toSSetObjEquiv n yFalse
  have hpoint (p : stdSimplex ℝ (Fin (n.unop.len + 1))) :
      (fTrue p).1 = (fFalse p).1 := by
    have h := congrArg (fun q ↦
      (TopCat.disk.{0} 7).toSSetObjEquiv n q p)
        (hyTrue.trans hyFalse.symm)
    exact h
  let f : C(stdSimplex ℝ (Fin (n.unop.len + 1)),
      DiskSevenCoverIntersection) :=
    ⟨fun p ↦ ⟨(fTrue p).1, ⟨(fTrue p).2, by
        rw [hpoint p]
        exact (fFalse p).2⟩⟩,
      (continuous_subtype_val.comp fTrue.continuous).subtype_mk _⟩
  let y := (TopCat.of DiskSevenCoverIntersection).toSSetObjEquiv n |>.symm f
  refine ⟨y, ?_⟩
  apply Subtype.ext
  change (TopCat.toSSet.map diskSevenCoverIntersectionToDisk).app n y = z.1
  rw [← hyTrue]
  apply (TopCat.disk.{0} 7).toSSetObjEquiv n |>.injective
  ext p
  rfl

/-- The lift from punctured-interior singular simplices onto the range intersection is epi. -/
public instance diskSevenCoverIntersectionToRangeIntersectionSingularSet_epi :
    Epi diskSevenCoverIntersectionToRangeIntersectionSingularSet := by
  rw [NatTrans.epi_iff_epi_app]
  intro n
  rw [CategoryTheory.epi_iff_surjective]
  exact diskSevenCoverIntersectionToRangeIntersection_app_surjective n

/-- Hence the lift is an isomorphism of simplicial sets. -/
public instance diskSevenCoverIntersectionToRangeIntersectionSingularSet_isIso :
    IsIso diskSevenCoverIntersectionToRangeIntersectionSingularSet :=
  isIso_of_mono_of_epi _

/-- The singular simplicial set of the punctured interior is exactly the infimum of the two
member ranges. -/
public noncomputable def diskSevenCoverIntersectionRangeSingularSetIso :
    TopCat.toSSet.obj (TopCat.of DiskSevenCoverIntersection) ≅
      (diskSevenCoverRangeIntersectionSubcomplex : SSet) :=
  asIso diskSevenCoverIntersectionToRangeIntersectionSingularSet

/-- The resulting integral singular-chain isomorphism. -/
public noncomputable def diskSevenCoverIntersectionRangeChainsIso :
    IntegralSingularChainComplexObj (TopCat.of DiskSevenCoverIntersection) ≅
      DiskSevenCoverRangeIntersectionChainComplex :=
  ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).mapIso
    diskSevenCoverIntersectionRangeSingularSetIso

/-- Homology of the range intersection is homology of the actual punctured interior. -/
public noncomputable def diskSevenCoverIntersectionRangeHomologyIso (k : ℕ) :
    (IntegralSingularChainComplexObj
        (TopCat.of DiskSevenCoverIntersection)).homology k ≅
      DiskSevenCoverRangeIntersectionChainComplex.homology k :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat
    (ComplexShape.down ℕ) k).mapIso diskSevenCoverIntersectionRangeChainsIso

set_option backward.isDefEq.respectTransparency false in
/-- Combining the range identification with radial normalization identifies intersection-range
homology with the integral singular homology of the standard six-sphere. -/
public noncomputable def diskSevenCoverRangeIntersectionHomologyIsoSphereSix (k : ℕ) :
    DiskSevenCoverRangeIntersectionChainComplex.homology k ≅
      (IntegralSingularChainComplexObj (TopCat.sphere.{0} 6)).homology k :=
  (diskSevenCoverIntersectionRangeHomologyIso k).symm ≪≫
    integralSingularHomologyIsoOfHomotopyEquiv k
      diskSevenCoverIntersectionHomotopyEquivSphereSix

/-- Vanishing of range-intersection homology is exactly vanishing of standard-sphere homology. -/
public theorem diskSevenCoverRangeIntersection_homology_isZero_iff_sphereSix
    (k : ℕ) :
    IsZero (DiskSevenCoverRangeIntersectionChainComplex.homology k) ↔
      IsZero ((IntegralSingularChainComplexObj
        (TopCat.sphere.{0} 6)).homology k) :=
  (diskSevenCoverRangeIntersectionHomologyIsoSphereSix k).isZero_iff

/-- The entire local acyclicity obligation now consists precisely of the two standard-sphere
homology groups in degrees two and three: the local middle terms have vanished unconditionally. -/
public theorem diskSevenCoverLocalRelativeLowAcyclic_iff_sphereSix_low_isZero :
    DiskSevenCoverLocalRelativeLowAcyclic ↔
      IsZero ((IntegralSingularChainComplexObj
        (TopCat.sphere.{0} 6)).homology 2) ∧
      IsZero ((IntegralSingularChainComplexObj
        (TopCat.sphere.{0} 6)).homology 3) := by
  constructor
  · intro h
    exact
      ⟨(diskSevenCoverRangeIntersection_homology_isZero_iff_sphereSix 2).mp
          h.2.2.1,
        (diskSevenCoverRangeIntersection_homology_isZero_iff_sphereSix 3).mp
          h.2.2.2⟩
  · rintro ⟨h₂, h₃⟩
    exact
      ⟨diskSevenCoverLocalRelativeMiddle_low_isZero.1,
        diskSevenCoverLocalRelativeMiddle_low_isZero.2,
        (diskSevenCoverRangeIntersection_homology_isZero_iff_sphereSix 2).mpr h₂,
        (diskSevenCoverRangeIntersection_homology_isZero_iff_sphereSix 3).mpr h₃⟩

end SphereSixComplex
