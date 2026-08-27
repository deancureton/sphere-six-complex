module

public import SphereSixComplex.Topology.DiskSevenRelativeHomologyLow
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# A local Mayer--Vietoris reduction for the seven-disk pair

This file decomposes the concrete cover-small relative complex into the two range subcomplexes of
the disk cover.  It proves the resulting relative Mayer--Vietoris sequence short exact from
pushout squares, leaving only acyclicity of explicit local and intersection complexes in the
low-degree calculation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set

namespace SphereSixComplex

/-- A concrete chain-contraction identity at one positive degree. -/
public structure ChainContractionAt
    (K : ChainComplex AddCommGrpCat ℕ) (n : ℕ) where
  upper : K.X n ⟶ K.X (n + 1)
  lower : K.X (n - 1) ⟶ K.X n
  identity : upper ≫ K.d (n + 1) n + K.d n (n - 1) ≫ lower = 𝟙 _

/-- A contraction identity makes every cycle in that degree an explicit boundary. -/
public theorem ChainContractionAt.exactAt
    {K : ChainComplex AddCommGrpCat ℕ} {n : ℕ} (h : ChainContractionAt K n)
    (hn : n ≠ 0) : K.ExactAt n := by
  rw [K.exactAt_iff' (i := n + 1) (j := n) (k := n - 1)
    (ChainComplex.prev ℕ n)
    ((ComplexShape.down ℕ).next_eq'
      (ComplexShape.down_mk n (n - 1) (by omega)))]
  rw [ShortComplex.ab_exact_iff_function_exact]
  change Function.Exact (K.d (n + 1) n).hom (K.d n (n - 1)).hom
  intro x
  constructor
  · intro hx
    refine ⟨h.upper x, ?_⟩
    have hid := ConcreteCategory.congr_hom h.identity x
    simp only [AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply, hx,
      map_zero, add_zero, CategoryTheory.ConcreteCategory.id_apply] at hid
    exact hid
  · rintro ⟨y, rfl⟩
    exact ConcreteCategory.congr_hom (K.d_comp_d (n + 1) n (n - 1)) y

/-- A contraction identity implies vanishing of homology in that degree. -/
public theorem ChainContractionAt.isZero_homology
    {K : ChainComplex AddCommGrpCat ℕ} {n : ℕ} (h : ChainContractionAt K n)
    (hn : n ≠ 0) : IsZero (K.homology n) :=
  (h.exactAt hn).isZero_homology

/-- The singular subcomplex consisting of simplices coming from one member of the concrete disk
cover. -/
public noncomputable def diskSevenCoverRangeSubcomplex (b : Bool) :
    (TopCat.toSSet.obj (TopCat.disk.{0} 7)).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map
    (topologicalSubsetInclusion (TopCat.disk.{0} 7) (diskSevenExcisionCover b)))

/-- The intersection of the two range subcomplexes. -/
public noncomputable def diskSevenCoverRangeIntersectionSubcomplex :
    (TopCat.toSSet.obj (TopCat.disk.{0} 7)).Subcomplex :=
  diskSevenCoverRangeSubcomplex true ⊓ diskSevenCoverRangeSubcomplex false

/-- The intersection, the two cover-member ranges, and the cover-small subcomplex form the
tautological bicartesian square in the lattice of subcomplexes. -/
public theorem diskSevenCoverRangeSubcomplex_bicartSq :
    SSet.Subcomplex.BicartSq
      diskSevenCoverRangeIntersectionSubcomplex
      (diskSevenCoverRangeSubcomplex true)
      (diskSevenCoverRangeSubcomplex false)
      (coverSmallSingularSubcomplex (TopCat.disk.{0} 7)
        diskSevenExcisionCover) := by
  constructor
  · simpa [diskSevenCoverRangeSubcomplex,
      coverSmallSingularSubcomplex] using
      (iSup_bool_eq (f := fun b ↦ SSet.Subcomplex.range (TopCat.toSSet.map
        (topologicalSubsetInclusion (TopCat.disk.{0} 7)
          (diskSevenExcisionCover b))))).symm
  · rfl

/-- Integral chains on one range subcomplex. -/
public noncomputable abbrev DiskSevenCoverRangeChainComplex (b : Bool) :
    ChainComplex AddCommGrpCat ℕ :=
  (diskSevenCoverRangeSubcomplex b : SSet).chainComplex (AddCommGrpCat.of ℤ)

/-- Integral chains on the intersection of the two range subcomplexes. -/
public noncomputable abbrev DiskSevenCoverRangeIntersectionChainComplex :
    ChainComplex AddCommGrpCat ℕ :=
  (diskSevenCoverRangeIntersectionSubcomplex : SSet).chainComplex
    (AddCommGrpCat.of ℤ)

/-- A member range is contained in the cover-small singular subcomplex. -/
public theorem diskSevenCoverRangeSubcomplex_le_coverSmall (b : Bool) :
    diskSevenCoverRangeSubcomplex b ≤
      coverSmallSingularSubcomplex (TopCat.disk.{0} 7) diskSevenExcisionCover := by
  exact le_iSup (fun c ↦ SSet.Subcomplex.range (TopCat.toSSet.map
    (topologicalSubsetInclusion (TopCat.disk.{0} 7)
      (diskSevenExcisionCover c)))) b

/-- Inclusion of one member range into cover-small simplices. -/
public noncomputable def diskSevenCoverRangeToSmallSingularSet (b : Bool) :
    (diskSevenCoverRangeSubcomplex b : SSet) ⟶
      coverSmallSingularSubcomplex (TopCat.disk.{0} 7) diskSevenExcisionCover :=
  SSet.Subcomplex.homOfLE (diskSevenCoverRangeSubcomplex_le_coverSmall b)

/-- The induced inclusion on chains. -/
public noncomputable def diskSevenCoverRangeToSmallChains (b : Bool) :
    DiskSevenCoverRangeChainComplex b ⟶
      DiskSevenCoverSmallIntegralSingularChainComplex :=
  SSet.chainComplexMap (diskSevenCoverRangeToSmallSingularSet b)
    (AddCommGrpCat.of ℤ)

/-- The intersection includes into either member range. -/
public noncomputable def diskSevenCoverRangeIntersectionToRangeSingularSet (b : Bool) :
    (diskSevenCoverRangeIntersectionSubcomplex : SSet) ⟶
      (diskSevenCoverRangeSubcomplex b : SSet) :=
  match b with
  | true => SSet.Subcomplex.homOfLE inf_le_left
  | false => SSet.Subcomplex.homOfLE inf_le_right

/-- The intersection inclusion on chains. -/
public noncomputable def diskSevenCoverRangeIntersectionToRangeChains (b : Bool) :
    DiskSevenCoverRangeIntersectionChainComplex ⟶
      DiskSevenCoverRangeChainComplex b :=
  SSet.chainComplexMap (diskSevenCoverRangeIntersectionToRangeSingularSet b)
    (AddCommGrpCat.of ℤ)

/-- The two range inclusions form a pushout square of simplicial sets. -/
public theorem diskSevenCoverRangeSingularSet_isPushout :
    IsPushout
      (diskSevenCoverRangeIntersectionToRangeSingularSet true)
      (diskSevenCoverRangeIntersectionToRangeSingularSet false)
      (diskSevenCoverRangeToSmallSingularSet true)
      (diskSevenCoverRangeToSmallSingularSet false) := by
  simpa [diskSevenCoverRangeIntersectionToRangeSingularSet,
    diskSevenCoverRangeToSmallSingularSet] using
    diskSevenCoverRangeSubcomplex_bicartSq.isPushout

/-- Both routes from the intersection to cover-small chains agree. -/
public theorem diskSevenCoverRangeIntersectionToSmallChains_eq :
    diskSevenCoverRangeIntersectionToRangeChains true ≫
        diskSevenCoverRangeToSmallChains true =
      diskSevenCoverRangeIntersectionToRangeChains false ≫
        diskSevenCoverRangeToSmallChains false := by
  change
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (diskSevenCoverRangeIntersectionToRangeSingularSet true) ≫
        ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (diskSevenCoverRangeToSmallSingularSet true) =
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (diskSevenCoverRangeIntersectionToRangeSingularSet false) ≫
        ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (diskSevenCoverRangeToSmallSingularSet false)
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply Functor.congr_map
  ext n x
  apply Subtype.ext
  rfl

/-- Integral simplicial chains preserve the preceding pushout square. -/
private theorem diskSevenPushoutCocone_condition_f
    (s : PushoutCocone
      (diskSevenCoverRangeIntersectionToRangeChains true)
      (diskSevenCoverRangeIntersectionToRangeChains false)) (n : ℕ) :
    (diskSevenCoverRangeIntersectionToRangeChains true).f n ≫ s.inl.f n =
      (diskSevenCoverRangeIntersectionToRangeChains false).f n ≫ s.inr.f n := by
  exact HomologicalComplex.congr_hom s.condition n

public theorem diskSevenCoverRangeChains_isPushout :
    IsPushout
      (diskSevenCoverRangeIntersectionToRangeChains true)
      (diskSevenCoverRangeIntersectionToRangeChains false)
      (diskSevenCoverRangeToSmallChains true)
      (diskSevenCoverRangeToSmallChains false) := by
  have hdegree (n : ℕ) : IsPushout
      ((diskSevenCoverRangeIntersectionToRangeChains true).f n)
      ((diskSevenCoverRangeIntersectionToRangeChains false).f n)
      ((diskSevenCoverRangeToSmallChains true).f n)
      ((diskSevenCoverRangeToSmallChains false).f n) := by
    have hType := diskSevenCoverRangeSingularSet_isPushout.map
      ((evaluation SimplexCategoryᵒᵖ Type).obj (Opposite.op (SimplexCategory.mk n)))
    have hAb := hType.map (sigmaConst.obj (AddCommGrpCat.of ℤ))
    simpa [diskSevenCoverRangeIntersectionToRangeChains,
      diskSevenCoverRangeToSmallChains, SSet.chainComplexMap,
      SSet.chainComplexFunctor, SimplicialObject.whiskering,
      AlgebraicTopology.alternatingFaceMapComplex,
      AlgebraicTopology.AlternatingFaceMapComplex.map] using hAb
  refine ⟨⟨diskSevenCoverRangeIntersectionToSmallChains_eq⟩,
    ⟨PushoutCocone.IsColimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact
      { f := fun n ↦ (hdegree n).desc (s.inl.f n) (s.inr.f n)
          (diskSevenPushoutCocone_condition_f s n)
        comm' := by
          intro i j _
          apply (hdegree i).hom_ext
          · simp
          · simp }
  · intro s
    apply HomologicalComplex.Hom.ext
    funext n
    exact (hdegree n).inl_desc _ _ _
  · intro s
    apply HomologicalComplex.Hom.ext
    funext n
    exact (hdegree n).inr_desc _ _ _
  · intro s m hm₁ hm₂
    apply HomologicalComplex.Hom.ext
    funext n
    apply (hdegree n).hom_ext
    · rw [(hdegree n).inl_desc]
      exact HomologicalComplex.congr_hom hm₁ n
    · rw [(hdegree n).inr_desc]
      exact HomologicalComplex.congr_hom hm₂ n

/-- The singular set of a cover member, lifted to its range subcomplex. -/
public noncomputable def diskSevenCoverMemberToRangeSingularSet (b : Bool) :
    TopCat.toSSet.obj (TopCat.of (diskSevenExcisionCover b)) ⟶
      (diskSevenCoverRangeSubcomplex b : SSet) :=
  SSet.Subcomplex.lift
    (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.disk.{0} 7)
      (diskSevenExcisionCover b))) le_rfl

/-- Lifting a cover member first to its range and then to the cover-small subcomplex is the
canonical cover-member lift. -/
public theorem diskSevenCoverMemberToRange_comp_small (b : Bool) :
    diskSevenCoverMemberToRangeSingularSet b ≫
        diskSevenCoverRangeToSmallSingularSet b =
      coverMemberToSmallSingularSet
        (TopCat.disk.{0} 7) diskSevenExcisionCover b := by
  ext n x
  apply Subtype.ext
  rfl

/-- The boundary chain map lifted specifically to the `false` member range. -/
public noncomputable def diskBoundaryToDiskSevenFalseRangeChains :
    IntegralSingularChainComplexObj (TopCat.sphere.{0} 6) ⟶
      DiskSevenCoverRangeChainComplex false :=
  SSet.chainComplexMap
      (TopCat.toSSet.map diskBoundaryToDiskSevenExcisionCoverFalse)
      (AddCommGrpCat.of ℤ) ≫
    SSet.chainComplexMap (diskSevenCoverMemberToRangeSingularSet false)
      (AddCommGrpCat.of ℤ)

private theorem diskBoundaryToDiskSevenFalseRangeChains_eq :
    diskBoundaryToDiskSevenFalseRangeChains =
      integralSingularChainMapObj diskBoundaryToDiskSevenExcisionCoverFalse ≫
        SSet.chainComplexMap (diskSevenCoverMemberToRangeSingularSet false)
          (AddCommGrpCat.of ℤ) := by
  rfl

private theorem diskSevenCoverMemberToRangeChains_comp_small :
    SSet.chainComplexMap (diskSevenCoverMemberToRangeSingularSet false)
          (AddCommGrpCat.of ℤ) ≫
        diskSevenCoverRangeToSmallChains false =
      coverMemberToSmallIntegralSingularChains
        (TopCat.disk.{0} 7) diskSevenExcisionCover false := by
  rw [diskSevenCoverRangeToSmallChains,
    coverMemberToSmallIntegralSingularChains]
  change
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (diskSevenCoverMemberToRangeSingularSet false) ≫
        ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (diskSevenCoverRangeToSmallSingularSet false) =
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (coverMemberToSmallSingularSet
          (TopCat.disk.{0} 7) diskSevenExcisionCover false)
  rw [← Functor.map_comp, diskSevenCoverMemberToRange_comp_small]

private theorem diskBoundaryToDiskSevenCoverSmallIntegralSingularChains_eq :
    diskBoundaryToDiskSevenCoverSmallIntegralSingularChains =
      integralSingularChainMapObj diskBoundaryToDiskSevenExcisionCoverFalse ≫
        coverMemberToSmallIntegralSingularChains
          (TopCat.disk.{0} 7) diskSevenExcisionCover false := by
  rfl

private theorem diskBoundaryToDiskSevenFalseRangeChains_comp_small_aux :
    diskBoundaryToDiskSevenFalseRangeChains ≫
        diskSevenCoverRangeToSmallChains false =
      diskBoundaryToDiskSevenCoverSmallIntegralSingularChains := by
  calc
    _ = (integralSingularChainMapObj diskBoundaryToDiskSevenExcisionCoverFalse ≫
          SSet.chainComplexMap (diskSevenCoverMemberToRangeSingularSet false)
            (AddCommGrpCat.of ℤ)) ≫
        diskSevenCoverRangeToSmallChains false :=
      congrArg (fun q ↦ q ≫ diskSevenCoverRangeToSmallChains false)
        diskBoundaryToDiskSevenFalseRangeChains_eq
    _ = integralSingularChainMapObj diskBoundaryToDiskSevenExcisionCoverFalse ≫
        (SSet.chainComplexMap (diskSevenCoverMemberToRangeSingularSet false)
            (AddCommGrpCat.of ℤ) ≫
          diskSevenCoverRangeToSmallChains false) := Category.assoc _ _ _
    _ = integralSingularChainMapObj diskBoundaryToDiskSevenExcisionCoverFalse ≫
        coverMemberToSmallIntegralSingularChains
          (TopCat.disk.{0} 7) diskSevenExcisionCover false :=
      congrArg
        (fun q ↦ integralSingularChainMapObj
          diskBoundaryToDiskSevenExcisionCoverFalse ≫ q)
        diskSevenCoverMemberToRangeChains_comp_small
    _ = _ := diskBoundaryToDiskSevenCoverSmallIntegralSingularChains_eq.symm

/-- The boundary-to-small map factors through the false member range. -/
public theorem diskBoundaryToDiskSevenFalseRangeChains_comp_small :
    diskBoundaryToDiskSevenFalseRangeChains ≫
        diskSevenCoverRangeToSmallChains false =
      diskBoundaryToDiskSevenCoverSmallIntegralSingularChains :=
  diskBoundaryToDiskSevenFalseRangeChains_comp_small_aux
/-- The false range modulo boundary chains. -/
public noncomputable def DiskSevenFalseRangeRelativeChainComplex :
    ChainComplex AddCommGrpCat ℕ :=
  cokernel diskBoundaryToDiskSevenFalseRangeChains

/-- Projection to the false-range relative complex. -/
public noncomputable def diskSevenFalseRangeRelativeProjection :
    DiskSevenCoverRangeChainComplex false ⟶
      DiskSevenFalseRangeRelativeChainComplex :=
  cokernel.π diskBoundaryToDiskSevenFalseRangeChains

private theorem diskSevenFalseRangeRelativeProjection_condition :
    diskBoundaryToDiskSevenFalseRangeChains ≫
      diskSevenFalseRangeRelativeProjection = 0 := by
  exact cokernel.condition _

/-- The false-range relative complex maps canonically to the cover-small relative complex. -/
public noncomputable def diskSevenFalseRangeRelativeToCoverSmallRelative :
    DiskSevenFalseRangeRelativeChainComplex ⟶
      DiskSevenCoverSmallRelativeIntegralSingularChainComplex :=
  cokernel.map diskBoundaryToDiskSevenFalseRangeChains
    diskBoundaryToDiskSevenCoverSmallIntegralSingularChains (𝟙 _)
      (diskSevenCoverRangeToSmallChains false) (by
        rw [Category.id_comp]
        exact diskBoundaryToDiskSevenFalseRangeChains_comp_small)

@[reassoc (attr := simp)]
public theorem diskSevenFalseRangeRelativeProjection_comp_toCoverSmallRelative :
    diskSevenFalseRangeRelativeProjection ≫
        diskSevenFalseRangeRelativeToCoverSmallRelative =
      diskSevenCoverRangeToSmallChains false ≫
        diskSevenCoverSmallRelativeChainProjection := by
  change cokernel.π diskBoundaryToDiskSevenFalseRangeChains ≫
      cokernel.desc diskBoundaryToDiskSevenFalseRangeChains
        (diskSevenCoverRangeToSmallChains false ≫
          cokernel.π diskBoundaryToDiskSevenCoverSmallIntegralSingularChains) _ = _
  exact cokernel.π_desc _ _ _

private theorem diskSevenFalseRangePushoutDesc_condition
    (s : PushoutCocone
      (diskSevenCoverRangeToSmallChains false)
      diskSevenFalseRangeRelativeProjection) :
    diskBoundaryToDiskSevenCoverSmallIntegralSingularChains ≫ s.inl = 0 := by
  rw [← diskBoundaryToDiskSevenFalseRangeChains_comp_small,
    Category.assoc, s.condition]
  rw [← Category.assoc,
    diskSevenFalseRangeRelativeProjection_condition, zero_comp]

private noncomputable def diskSevenFalseRangePushoutDesc
    (s : PushoutCocone
      (diskSevenCoverRangeToSmallChains false)
      diskSevenFalseRangeRelativeProjection) :
    DiskSevenCoverSmallRelativeIntegralSingularChainComplex ⟶ s.pt :=
  cokernel.desc diskBoundaryToDiskSevenCoverSmallIntegralSingularChains
    s.inl (diskSevenFalseRangePushoutDesc_condition s)

private theorem diskSevenCoverSmallRelativeProjection_comp_pushoutDesc
    (s : PushoutCocone
      (diskSevenCoverRangeToSmallChains false)
      diskSevenFalseRangeRelativeProjection) :
    diskSevenCoverSmallRelativeChainProjection ≫
      diskSevenFalseRangePushoutDesc s = s.inl := by
  exact cokernel.π_desc _ _ _

private theorem diskSevenFalseRangeRelative_comp_pushoutDesc
    (s : PushoutCocone
      (diskSevenCoverRangeToSmallChains false)
      diskSevenFalseRangeRelativeProjection) :
    diskSevenFalseRangeRelativeToCoverSmallRelative ≫
      diskSevenFalseRangePushoutDesc s = s.inr := by
  let _ : Epi diskSevenFalseRangeRelativeProjection := by
    dsimp [diskSevenFalseRangeRelativeProjection]
    exact coequalizer.π_epi
  apply (cancel_epi diskSevenFalseRangeRelativeProjection).1
  calc
    diskSevenFalseRangeRelativeProjection ≫
          (diskSevenFalseRangeRelativeToCoverSmallRelative ≫
            diskSevenFalseRangePushoutDesc s) =
        (diskSevenFalseRangeRelativeProjection ≫
            diskSevenFalseRangeRelativeToCoverSmallRelative) ≫
          diskSevenFalseRangePushoutDesc s := (Category.assoc _ _ _).symm
    _ = (diskSevenCoverRangeToSmallChains false ≫
          diskSevenCoverSmallRelativeChainProjection) ≫
        diskSevenFalseRangePushoutDesc s :=
      congrArg (fun q ↦ q ≫ diskSevenFalseRangePushoutDesc s)
        diskSevenFalseRangeRelativeProjection_comp_toCoverSmallRelative
    _ = diskSevenCoverRangeToSmallChains false ≫
        (diskSevenCoverSmallRelativeChainProjection ≫
          diskSevenFalseRangePushoutDesc s) := Category.assoc _ _ _
    _ = diskSevenCoverRangeToSmallChains false ≫ s.inl :=
      congrArg (fun q ↦ diskSevenCoverRangeToSmallChains false ≫ q)
        (diskSevenCoverSmallRelativeProjection_comp_pushoutDesc s)
    _ = diskSevenFalseRangeRelativeProjection ≫ s.inr := s.condition

/-- Quotienting the false range and the total cover-small complex by the same boundary chains
is a pushout square. -/
public theorem diskSevenFalseRangeRelativeSquare_isPushout :
    IsPushout
      (diskSevenCoverRangeToSmallChains false)
      diskSevenFalseRangeRelativeProjection
      diskSevenCoverSmallRelativeChainProjection
      diskSevenFalseRangeRelativeToCoverSmallRelative := by
  let _ : Epi diskSevenFalseRangeRelativeProjection := by
    dsimp [diskSevenFalseRangeRelativeProjection]
    exact coequalizer.π_epi
  let _ : Epi diskSevenCoverSmallRelativeChainProjection := by
    dsimp [diskSevenCoverSmallRelativeChainProjection]
    exact coequalizer.π_epi
  refine ⟨⟨diskSevenFalseRangeRelativeProjection_comp_toCoverSmallRelative.symm⟩,
    ⟨PushoutCocone.IsColimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact diskSevenFalseRangePushoutDesc s
  · intro s
    exact diskSevenCoverSmallRelativeProjection_comp_pushoutDesc s
  · intro s
    exact diskSevenFalseRangeRelative_comp_pushoutDesc s
  · intro s m hm₁ _
    apply (cancel_epi diskSevenCoverSmallRelativeChainProjection).1
    rw [hm₁]
    exact (diskSevenCoverSmallRelativeProjection_comp_pushoutDesc s).symm

/-- The local middle term: true-range chains together with false-range chains modulo boundary. -/
public noncomputable abbrev DiskSevenCoverLocalRelativeMiddleChainComplex :
    ChainComplex AddCommGrpCat ℕ :=
  DiskSevenCoverRangeChainComplex true ⊞
    DiskSevenFalseRangeRelativeChainComplex

/-- Before quotienting the false range by boundary chains, the two range complexes sum onto the
cover-small chain complex. -/
public noncomputable def diskSevenCoverRangeSum :
    (DiskSevenCoverRangeChainComplex true ⊞
      DiskSevenCoverRangeChainComplex false) ⟶
      DiskSevenCoverSmallIntegralSingularChainComplex :=
  biprod.desc (diskSevenCoverRangeToSmallChains true)
    (diskSevenCoverRangeToSmallChains false)

/-- Every cover-small simplex belongs to one of the two range subcomplexes, so the range-sum map
is an epimorphism. -/
public theorem diskSevenCoverRangeSum_epi : Epi diskSevenCoverRangeSum := by
  constructor
  intro Z g h heq
  apply HomologicalComplex.Hom.ext
  funext n
  apply (coverSmallSingularSubcomplex
    (TopCat.disk.{0} 7) diskSevenExcisionCover : SSet).chainComplex_hom_ext
  intro x
  obtain ⟨b, hb⟩ :=
    (mem_coverSmallSingularSubcomplex_iff
      (TopCat.disk.{0} 7) diskSevenExcisionCover x.1).mp x.2
  let xb : (diskSevenCoverRangeSubcomplex b : SSet).obj
      (Opposite.op (SimplexCategory.mk n)) := ⟨x.1, hb⟩
  have heqn : (diskSevenCoverRangeSum.f n) ≫ g.f n =
      (diskSevenCoverRangeSum.f n) ≫ h.f n := by
    exact congrArg (fun q ↦ q.f n) heq
  cases b with
  | false =>
      have hx := congrArg
        (fun q ↦ ((diskSevenCoverRangeSubcomplex false : SSet).ιChainComplex xb ≫
          (biprod.inr : DiskSevenCoverRangeChainComplex false ⟶
            (DiskSevenCoverRangeChainComplex true ⊞
              DiskSevenCoverRangeChainComplex false)).f n) ≫ q) heqn
      have hx' :
          ((diskSevenCoverRangeSubcomplex false : SSet).ιChainComplex xb ≫
              (diskSevenCoverRangeToSmallChains false).f n) ≫ g.f n =
            ((diskSevenCoverRangeSubcomplex false : SSet).ιChainComplex xb ≫
              (diskSevenCoverRangeToSmallChains false).f n) ≫ h.f n := by
        simpa [diskSevenCoverRangeSum, Category.assoc] using hx
      have hι :
          (diskSevenCoverRangeSubcomplex false : SSet).ιChainComplex xb ≫
              (diskSevenCoverRangeToSmallChains false).f n =
            (coverSmallSingularSubcomplex (TopCat.disk.{0} 7)
              diskSevenExcisionCover : SSet).ιChainComplex x := by
        rw [diskSevenCoverRangeToSmallChains, SSet.ι_chainComplexMap_f]
        congr 1
      rw [hι] at hx'
      exact hx'
  | true =>
      have hx := congrArg
        (fun q ↦ ((diskSevenCoverRangeSubcomplex true : SSet).ιChainComplex xb ≫
          (biprod.inl : DiskSevenCoverRangeChainComplex true ⟶
            (DiskSevenCoverRangeChainComplex true ⊞
              DiskSevenCoverRangeChainComplex false)).f n) ≫ q) heqn
      have hx' :
          ((diskSevenCoverRangeSubcomplex true : SSet).ιChainComplex xb ≫
              (diskSevenCoverRangeToSmallChains true).f n) ≫ g.f n =
            ((diskSevenCoverRangeSubcomplex true : SSet).ιChainComplex xb ≫
              (diskSevenCoverRangeToSmallChains true).f n) ≫ h.f n := by
        simpa [diskSevenCoverRangeSum, Category.assoc] using hx
      have hι :
          (diskSevenCoverRangeSubcomplex true : SSet).ιChainComplex xb ≫
              (diskSevenCoverRangeToSmallChains true).f n =
            (coverSmallSingularSubcomplex (TopCat.disk.{0} 7)
              diskSevenExcisionCover : SSet).ιChainComplex x := by
        rw [diskSevenCoverRangeToSmallChains, SSet.ι_chainComplexMap_f]
        congr 1
      rw [hι] at hx'
      exact hx'
/-- Quotienting the false summand sends the absolute two-range middle term to the relative
middle term. -/
public noncomputable def diskSevenCoverRangeSumToLocalRelativeMiddle :
    (DiskSevenCoverRangeChainComplex true ⊞
      DiskSevenCoverRangeChainComplex false) ⟶
      DiskSevenCoverLocalRelativeMiddleChainComplex :=
  biprod.map (𝟙 _) diskSevenFalseRangeRelativeProjection

/-- Difference map from intersection chains to the local relative middle term. -/
public noncomputable def diskSevenCoverLocalRelativeDifference :
    DiskSevenCoverRangeIntersectionChainComplex ⟶
      DiskSevenCoverLocalRelativeMiddleChainComplex :=
  biprod.lift
    (diskSevenCoverRangeIntersectionToRangeChains true)
    (-(diskSevenCoverRangeIntersectionToRangeChains false ≫
      diskSevenFalseRangeRelativeProjection))

/-- The local difference map is mono: its true-range component is the inclusion of the
intersection subcomplex. -/
public theorem diskSevenCoverLocalRelativeDifference_mono :
    Mono diskSevenCoverLocalRelativeDifference := by
  have hinter : Mono (diskSevenCoverRangeIntersectionToRangeChains true) := by
    let _ : Mono (diskSevenCoverRangeIntersectionToRangeSingularSet true) := by
      dsimp [diskSevenCoverRangeIntersectionToRangeSingularSet]
      exact SSet.Subcomplex.mono_homOfLE inf_le_left
    dsimp [diskSevenCoverRangeIntersectionToRangeChains, SSet.chainComplexMap,
      SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  let _ : Mono (diskSevenCoverLocalRelativeDifference ≫
      (biprod.fst : DiskSevenCoverLocalRelativeMiddleChainComplex ⟶
        DiskSevenCoverRangeChainComplex true)) := by
    rw [diskSevenCoverLocalRelativeDifference, biprod.lift_fst]
    exact hinter
  exact mono_of_mono diskSevenCoverLocalRelativeDifference biprod.fst

/-- Sum map from the local relative middle term to cover-small relative chains. -/
public noncomputable def diskSevenCoverLocalRelativeSum :
    DiskSevenCoverLocalRelativeMiddleChainComplex ⟶
      DiskSevenCoverSmallRelativeIntegralSingularChainComplex :=
  biprod.desc
    (diskSevenCoverRangeToSmallChains true ≫
      diskSevenCoverSmallRelativeChainProjection)
    diskSevenFalseRangeRelativeToCoverSmallRelative

/-- The relative local sum is the quotient of the absolute range-sum decomposition. -/
public theorem diskSevenCoverRangeSumToLocalRelativeMiddle_comp_sum :
    diskSevenCoverRangeSumToLocalRelativeMiddle ≫
        diskSevenCoverLocalRelativeSum =
      diskSevenCoverRangeSum ≫
        diskSevenCoverSmallRelativeChainProjection := by
  apply biprod.hom_ext'
  · simp [diskSevenCoverRangeSumToLocalRelativeMiddle,
      diskSevenCoverLocalRelativeSum, diskSevenCoverRangeSum]
  · simp [diskSevenCoverRangeSumToLocalRelativeMiddle,
      diskSevenCoverLocalRelativeSum, diskSevenCoverRangeSum]

/-- The local relative sum is epi.  This is already forced by the explicit absolute
range-sum decomposition, after projection to relative chains. -/
public theorem diskSevenCoverLocalRelativeSum_epi :
    Epi diskSevenCoverLocalRelativeSum := by
  let _ : Epi diskSevenCoverRangeSum :=
    diskSevenCoverRangeSum_epi
  let _ : Epi diskSevenCoverSmallRelativeChainProjection := by
    dsimp [diskSevenCoverSmallRelativeChainProjection]
    exact coequalizer.π_epi
  exact epi_of_epi_fac
    diskSevenCoverRangeSumToLocalRelativeMiddle_comp_sum

/-- Pasting the absolute two-range pushout with the false-range quotient pushout gives the
relative two-range pushout. -/
public theorem diskSevenCoverLocalRelativeSquare_isPushout :
    IsPushout
      (diskSevenCoverRangeIntersectionToRangeChains true)
      (diskSevenCoverRangeIntersectionToRangeChains false ≫
        diskSevenFalseRangeRelativeProjection)
      (diskSevenCoverRangeToSmallChains true ≫
        diskSevenCoverSmallRelativeChainProjection)
      diskSevenFalseRangeRelativeToCoverSmallRelative :=
  IsPushout.paste_vert diskSevenCoverRangeChains_isPushout
    diskSevenFalseRangeRelativeSquare_isPushout

/-- The local difference and sum maps compose to zero. -/
public theorem diskSevenCoverLocalRelativeDifference_comp_sum :
    diskSevenCoverLocalRelativeDifference ≫
      diskSevenCoverLocalRelativeSum = 0 := by
  rw [diskSevenCoverLocalRelativeDifference,
    diskSevenCoverLocalRelativeSum, biprod.lift_desc,
    Preadditive.neg_comp, Category.assoc,
    diskSevenFalseRangeRelativeProjection_comp_toCoverSmallRelative,
    ← Category.assoc, ← Category.assoc,
    diskSevenCoverRangeIntersectionToSmallChains_eq, add_neg_cancel]

/-- The explicit local Mayer--Vietoris short complex for the pair `(D⁷,S⁶)`. -/
public noncomputable def diskSevenCoverSmallRelativeMayerVietorisShortComplex :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk diskSevenCoverLocalRelativeDifference
    diskSevenCoverLocalRelativeSum
    diskSevenCoverLocalRelativeDifference_comp_sum

/-- The remaining chain-level Mayer--Vietoris assertion for the concrete two-set cover. -/
public def DiskSevenCoverSmallRelativeMayerVietoris : Prop :=
  diskSevenCoverSmallRelativeMayerVietorisShortComplex.ShortExact

/-- Exactness of the relative Mayer--Vietoris short complex follows from the concrete pasted
pushout square. -/
public theorem diskSevenCoverSmallRelativeMayerVietoris_exact :
    diskSevenCoverSmallRelativeMayerVietorisShortComplex.Exact := by
  unfold diskSevenCoverSmallRelativeMayerVietorisShortComplex
  apply ShortComplex.exact_of_g_is_cokernel
  let h := diskSevenCoverLocalRelativeSquare_isPushout
  refine Cofork.IsColimit.mk _
    (fun s ↦ h.desc (biprod.inl ≫ s.π) (biprod.inr ≫ s.π) (by
      rw [← sub_eq_zero, ← Category.assoc,
        ← Category.assoc
          (diskSevenCoverRangeIntersectionToRangeChains false ≫
            diskSevenFalseRangeRelativeProjection) biprod.inr s.π,
        ← Preadditive.sub_comp]
      rw [show
        diskSevenCoverRangeIntersectionToRangeChains true ≫ biprod.inl -
            (diskSevenCoverRangeIntersectionToRangeChains false ≫
              diskSevenFalseRangeRelativeProjection) ≫ biprod.inr =
          diskSevenCoverLocalRelativeDifference by
        apply biprod.hom_ext
        · simp [diskSevenCoverLocalRelativeDifference]
        · simp [diskSevenCoverLocalRelativeDifference]]
      change diskSevenCoverLocalRelativeDifference ≫ s.π = 0
      have hs := s.condition
      change diskSevenCoverLocalRelativeDifference ≫ s.π = 0 ≫ s.π at hs
      rw [zero_comp] at hs
      exact hs))
    (fun s ↦ by
      apply biprod.hom_ext'
      · simp [diskSevenCoverLocalRelativeSum]
      · simp [diskSevenCoverLocalRelativeSum])
    (fun s m hm ↦ by
      change diskSevenCoverLocalRelativeSum ≫ m = s.π at hm
      apply h.hom_ext
      · replace hm := biprod.inl ≫= hm
        simp only [diskSevenCoverLocalRelativeSum,
          biprod.inl_desc_assoc, Category.assoc] at hm
        rw [h.inl_desc]
        simpa only [Category.assoc] using hm
      · replace hm := biprod.inr ≫= hm
        simp only [diskSevenCoverLocalRelativeSum,
          biprod.inr_desc_assoc] at hm
        rw [h.inr_desc]
        simpa only [Category.assoc] using hm)

/-- The concrete cover-small relative Mayer--Vietoris sequence is short exact, with no extra
topological or homological hypothesis. -/
public theorem diskSevenCoverSmallRelativeMayerVietoris :
    DiskSevenCoverSmallRelativeMayerVietoris :=
  { exact := diskSevenCoverSmallRelativeMayerVietoris_exact
    mono_f := diskSevenCoverLocalRelativeDifference_mono
    epi_g := diskSevenCoverLocalRelativeSum_epi }

/-- A useful characterization of the Mayer--Vietoris structure in terms of its exactness and
surjectivity fields.  Both fields are proved unconditionally above. -/
public theorem diskSevenCoverSmallRelativeMayerVietoris_iff :
    DiskSevenCoverSmallRelativeMayerVietoris ↔
      diskSevenCoverSmallRelativeMayerVietorisShortComplex.Exact ∧
        Epi diskSevenCoverLocalRelativeSum := by
  constructor
  · intro h
    exact ⟨h.exact, h.epi_g⟩
  · rintro ⟨hexact, hepi⟩
    exact
      { exact := hexact
        mono_f := diskSevenCoverLocalRelativeDifference_mono
        epi_g := hepi }

/-- The explicit local homology groups whose vanishing suffices in degrees two through four. -/
public def DiskSevenCoverLocalRelativeLowAcyclic : Prop :=
  IsZero (DiskSevenCoverLocalRelativeMiddleChainComplex.homology 3) ∧
    IsZero (DiskSevenCoverLocalRelativeMiddleChainComplex.homology 4) ∧
    IsZero (DiskSevenCoverRangeIntersectionChainComplex.homology 2) ∧
    IsZero (DiskSevenCoverRangeIntersectionChainComplex.homology 3)

/-- Fully explicit local chain-contraction data.  These are four additive degree-raising maps,
each satisfying `hd + dh = 1` in the indicated degree. -/
public def DiskSevenCoverLocalRelativeLowContractions : Prop :=
  Nonempty (ChainContractionAt DiskSevenCoverLocalRelativeMiddleChainComplex 3) ∧
    Nonempty (ChainContractionAt DiskSevenCoverLocalRelativeMiddleChainComplex 4) ∧
    Nonempty (ChainContractionAt DiskSevenCoverRangeIntersectionChainComplex 2) ∧
    Nonempty (ChainContractionAt DiskSevenCoverRangeIntersectionChainComplex 3)

/-- The explicit contractions imply all four local homology vanishings. -/
public theorem diskSevenCoverLocalRelativeLowAcyclic_of_contractions
    (h : DiskSevenCoverLocalRelativeLowContractions) :
    DiskSevenCoverLocalRelativeLowAcyclic :=
  ⟨h.1.some.isZero_homology (by omega),
    h.2.1.some.isZero_homology (by omega),
    h.2.2.1.some.isZero_homology (by omega),
    h.2.2.2.some.isZero_homology (by omega)⟩

/-- Mayer--Vietoris exactness and the four explicit local vanishings imply the two remaining
cover-small relative vanishings. -/
public theorem diskSevenCoverSmallRelativeLowAcyclic_of_local
    (hMV : DiskSevenCoverSmallRelativeMayerVietoris)
    (hlocal : DiskSevenCoverLocalRelativeLowAcyclic) :
    DiskSevenCoverSmallRelativeLowAcyclic := by
  constructor
  · exact (hMV.homology_exact₃ 3 2
      (ComplexShape.down_mk 3 2 (by omega))).isZero_X₂
        (hlocal.1.eq_of_src _ _) (hlocal.2.2.1.eq_of_tgt _ _)
  · exact (hMV.homology_exact₃ 4 3
      (ComplexShape.down_mk 4 3 (by omega))).isZero_X₂
      (hlocal.2.1.eq_of_src _ _) (hlocal.2.2.2.eq_of_tgt _ _)

/-- Thus the four local vanishings are the only remaining input: Mayer--Vietoris exactness for
the concrete cover has already been proved above. -/
public theorem diskSevenCoverSmallRelativeLowAcyclic_of_localAcyclic
    (hlocal : DiskSevenCoverLocalRelativeLowAcyclic) :
    DiskSevenCoverSmallRelativeLowAcyclic :=
  diskSevenCoverSmallRelativeLowAcyclic_of_local
    diskSevenCoverSmallRelativeMayerVietoris hlocal

/-- Consequently, the local Mayer--Vietoris calculation gives the desired standard-sphere
vanishings. -/
public theorem standardSphereSix_integralSingularHomology_low_isZero_of_local
    (hMV : DiskSevenCoverSmallRelativeMayerVietoris)
    (hlocal : DiskSevenCoverLocalRelativeLowAcyclic) :
    IsZero ((IntegralSingularChainComplexObj (TopCat.sphere 6)).homology 2) ∧
      IsZero ((IntegralSingularChainComplexObj (TopCat.sphere 6)).homology 3) := by
  rw [← diskSevenCoverSmallRelativeLowAcyclic_iff_standardSphereSix_low_isZero]
  exact diskSevenCoverSmallRelativeLowAcyclic_of_local hMV hlocal

/-- The four explicit local homology vanishings alone imply the desired standard-sphere
vanishings. -/
public theorem standardSphereSix_integralSingularHomology_low_isZero_of_localAcyclic
    (hlocal : DiskSevenCoverLocalRelativeLowAcyclic) :
    IsZero ((IntegralSingularChainComplexObj (TopCat.sphere 6)).homology 2) ∧
      IsZero ((IntegralSingularChainComplexObj (TopCat.sphere 6)).homology 3) :=
  standardSphereSix_integralSingularHomology_low_isZero_of_local
    diskSevenCoverSmallRelativeMayerVietoris hlocal

/-- A chain-level endpoint: concrete Mayer--Vietoris exactness plus four displayed contraction
identities proves both desired low-degree sphere vanishings. -/
public theorem standardSphereSix_integralSingularHomology_low_isZero_of_localContractions
    (h : DiskSevenCoverLocalRelativeLowContractions) :
    IsZero ((IntegralSingularChainComplexObj (TopCat.sphere 6)).homology 2) ∧
      IsZero ((IntegralSingularChainComplexObj (TopCat.sphere 6)).homology 3) :=
  standardSphereSix_integralSingularHomology_low_isZero_of_localAcyclic
    (diskSevenCoverLocalRelativeLowAcyclic_of_contractions h)

end SphereSixComplex
