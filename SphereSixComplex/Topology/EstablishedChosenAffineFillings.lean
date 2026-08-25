module

public import SphereSixComplex.Topology.EstablishedUnwrappedAffineFillings

/-!
# Bundled choices of affine filling-cover models

The source and deck groups of a universal cover are generally not definitionally determined by
its base.  These bundles hide those choices while retaining the exact regular-cover model and its
induced fundamental-group calculation.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

/-! ## Based transport -/

/-- Transport a based fundamental-group homomorphism along equalities of its two base points. -/
public noncomputable def fundamentalGroupHomOfBaseEq
    {B N : Type*} [TopologicalSpace B] [TopologicalSpace N]
    {b b' : B} {n n' : N} (hb : b = b') (hn : n = n')
    (f : FundamentalGroup B b →* FundamentalGroup N n) :
    FundamentalGroup B b' →* FundamentalGroup N n' := by
  subst b'
  subst n'
  exact f

/-- Transport a based loop along an equality of base points. -/
public noncomputable def fundamentalGroupElementOfBaseEq
    {B : Type*} [TopologicalSpace B] {b b' : B} (hb : b = b')
    (g : FundamentalGroup B b) : FundamentalGroup B b' := by
  subst b'
  exact g

/-- Transport an additive family of based loops along an equality of base points. -/
public noncomputable def fundamentalGroupAddHomOfBaseEq
    {Λ B : Type*} [AddCommGroup Λ] [TopologicalSpace B]
    {b b' : B} (hb : b = b')
    (f : Λ →+ Additive (FundamentalGroup B b)) :
    Λ →+ Additive (FundamentalGroup B b') := by
  subst b'
  exact f

/-- Surjectivity is preserved by based transport. -/
public theorem fundamentalGroupHomOfBaseEq_surjective
    {B N : Type*} [TopologicalSpace B] [TopologicalSpace N]
    {b b' : B} {n n' : N} (hb : b = b') (hn : n = n')
    (f : FundamentalGroup B b →* FundamentalGroup N n)
    (hf : Function.Surjective f) :
    Function.Surjective (fundamentalGroupHomOfBaseEq hb hn f) := by
  subst b'
  subst n'
  exact hf

@[simp]
public theorem fundamentalGroupHomOfBaseEq_apply
    {B N : Type*} [TopologicalSpace B] [TopologicalSpace N]
    {b b' : B} {n n' : N} (hb : b = b') (hn : n = n')
    (f : FundamentalGroup B b →* FundamentalGroup N n)
    (g : FundamentalGroup B b) :
    fundamentalGroupHomOfBaseEq hb hn f (fundamentalGroupElementOfBaseEq hb g) =
      fundamentalGroupElementOfBaseEq hn (f g) := by
  subst b'
  subst n'
  rfl

@[simp]
public theorem fundamentalGroupElementOfBaseEq_one
    {B : Type*} [TopologicalSpace B] {b b' : B} (hb : b = b') :
    fundamentalGroupElementOfBaseEq hb (1 : FundamentalGroup B b) = 1 := by
  subst b'
  rfl

@[simp]
public theorem fundamentalGroupElementOfBaseEq_mul
    {B : Type*} [TopologicalSpace B] {b b' : B} (hb : b = b')
    (g h : FundamentalGroup B b) :
    fundamentalGroupElementOfBaseEq hb (g * h) =
      fundamentalGroupElementOfBaseEq hb g * fundamentalGroupElementOfBaseEq hb h := by
  subst b'
  rfl

@[simp]
public theorem fundamentalGroupElementOfBaseEq_inv
    {B : Type*} [TopologicalSpace B] {b b' : B} (hb : b = b')
    (g : FundamentalGroup B b) :
    fundamentalGroupElementOfBaseEq hb g⁻¹ =
      (fundamentalGroupElementOfBaseEq hb g)⁻¹ := by
  subst b'
  rfl

@[simp]
public theorem fundamentalGroupElementOfBaseEq_pow
    {B : Type*} [TopologicalSpace B] {b b' : B} (hb : b = b')
    (g : FundamentalGroup B b) (k : ℕ) :
    fundamentalGroupElementOfBaseEq hb (g ^ k) =
      fundamentalGroupElementOfBaseEq hb g ^ k := by
  subst b'
  rfl

@[simp]
public theorem fundamentalGroupAddHomOfBaseEq_apply
    {Λ B : Type*} [AddCommGroup Λ] [TopologicalSpace B]
    {b b' : B} (hb : b = b')
    (f : Λ →+ Additive (FundamentalGroup B b)) (a : Λ) :
    fundamentalGroupAddHomOfBaseEq hb f a =
      Additive.ofMul (fundamentalGroupElementOfBaseEq hb
        (Additive.toMul (f a))) := by
  subst b'
  rfl

/-- A chosen regular-cover model for a cyclic affine filling. -/
public structure ChosenCyclicAffineFillingCoverModel
    (m : ℕ) (Λ B N : Type*)
    [NeZero m] [AddCommGroup Λ] [TopologicalSpace B] [TopologicalSpace N] where
  BoundaryDeck : Type
  FillingDeck : Type
  BoundaryCover : Type
  FillingCover : Type
  boundaryDeckGroup : Group BoundaryDeck
  fillingDeckGroup : Group FillingDeck
  boundaryCoverTopology : TopologicalSpace BoundaryCover
  fillingCoverTopology : TopologicalSpace FillingCover
  boundaryAction : MulAction BoundaryDeck BoundaryCover
  fillingAction : MulAction FillingDeck FillingCover
  model : @CyclicAffineFillingCoverModel m Λ BoundaryDeck FillingDeck
    BoundaryCover FillingCover B N _ _ boundaryDeckGroup fillingDeckGroup
    boundaryCoverTopology fillingCoverTopology _ _ boundaryAction fillingAction

namespace ChosenCyclicAffineFillingCoverModel

variable {m : ℕ} {Λ B N : Type*}
variable [NeZero m] [AddCommGroup Λ] [TopologicalSpace B] [TopologicalSpace N]

/-- The selected boundary base point. -/
public noncomputable def boundaryBase
    (D : ChosenCyclicAffineFillingCoverModel m Λ B N) : B := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.model.boundaryProjection D.model.base

/-- The selected filling base point. -/
public noncomputable def fillingBase
    (D : ChosenCyclicAffineFillingCoverModel m Λ B N) : N := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.model.coverMap.baseMap (D.model.boundaryProjection D.model.base)

/-- The map on fundamental groups induced by the cyclic filling inclusion. -/
public noncomputable def fundamentalGroupMap
    (D : ChosenCyclicAffineFillingCoverModel m Λ B N) :
    FundamentalGroup B D.boundaryBase →* FundamentalGroup N D.fillingBase := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact FundamentalGroup.map D.model.coverMap.baseMap
    (D.model.boundaryProjection D.model.base)

/-- The exact induced fundamental-group calculation of the chosen cyclic filling model. -/
public noncomputable def fundamentalGroupData
    (D : ChosenCyclicAffineFillingCoverModel m Λ B N) :
    letI := D.boundaryDeckGroup
    letI := D.fillingDeckGroup
    letI := D.boundaryCoverTopology
    letI := D.fillingCoverTopology
    letI := D.boundaryAction
    letI := D.fillingAction
    CyclicAffineFillingPiOneData D.model := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact establishedCyclicAffineFillingPiOne D.model

/-- The lattice generators in the chosen cyclic boundary fundamental group. -/
public noncomputable def translation
    (D : ChosenCyclicAffineFillingCoverModel m Λ B N) :
    Λ →+ Additive (FundamentalGroup B D.boundaryBase) := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.fundamentalGroupData.translation

/-- The unwrapped angular meridian in the chosen cyclic boundary fundamental group. -/
public noncomputable def meridian
    (D : ChosenCyclicAffineFillingCoverModel m Λ B N) :
    FundamentalGroup B D.boundaryBase := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.fundamentalGroupData.meridian

/-- The lattice twist made by one full cyclic iterate. -/
public noncomputable def twist
    (D : ChosenCyclicAffineFillingCoverModel m Λ B N) : Λ := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.model.twist

/-- The cyclic filling inclusion is onto on fundamental groups. -/
public theorem fundamentalGroupMap_surjective
    (D : ChosenCyclicAffineFillingCoverModel m Λ B N) :
    Function.Surjective D.fundamentalGroupMap := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.fundamentalGroupData.map_surjective

/-- The exact kernel of the cyclic filling inclusion. -/
public theorem fundamentalGroupMap_kernel
    (D : ChosenCyclicAffineFillingCoverModel m Λ B N) :
    D.fundamentalGroupMap.ker = Subgroup.normalClosure
      {D.meridian ^ m * (Additive.toMul (D.translation D.twist))⁻¹} := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.fundamentalGroupData.ker_map

/-- The canonical cyclic affine relation is killed by the filling inclusion. -/
public theorem fundamentalGroupMap_relation
    (D : ChosenCyclicAffineFillingCoverModel m Λ B N) :
    D.fundamentalGroupMap
      (D.meridian ^ m * (Additive.toMul (D.translation D.twist))⁻¹) = 1 := by
  change D.meridian ^ m *
    (Additive.toMul (D.translation D.twist))⁻¹ ∈ D.fundamentalGroupMap.ker
  rw [D.fundamentalGroupMap_kernel]
  exact Subgroup.subset_normalClosure (Set.mem_singleton _)

end ChosenCyclicAffineFillingCoverModel

/-- A chosen regular-cover model for a toric filling. -/
public structure ChosenToricFillingCoverModel
    (Λ K B N : Type*)
    [AddCommGroup Λ] [AddCommGroup K] [TopologicalSpace B] [TopologicalSpace N] where
  BoundaryDeck : Type
  FillingDeck : Type
  BoundaryCover : Type
  FillingCover : Type
  boundaryDeckGroup : Group BoundaryDeck
  fillingDeckGroup : Group FillingDeck
  boundaryCoverTopology : TopologicalSpace BoundaryCover
  fillingCoverTopology : TopologicalSpace FillingCover
  boundaryAction : MulAction BoundaryDeck BoundaryCover
  fillingAction : MulAction FillingDeck FillingCover
  model : @ToricFillingCoverModel Λ K BoundaryDeck FillingDeck BoundaryCover FillingCover B N
    _ _ boundaryDeckGroup fillingDeckGroup boundaryCoverTopology fillingCoverTopology _ _
    boundaryAction fillingAction

namespace ChosenToricFillingCoverModel

variable {Λ K B N : Type*}
variable [AddCommGroup Λ] [AddCommGroup K]
variable [TopologicalSpace B] [TopologicalSpace N]

/-- The selected boundary base point. -/
public noncomputable def boundaryBase
    (D : ChosenToricFillingCoverModel Λ K B N) : B := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.model.boundaryProjection D.model.base

/-- The selected filling base point. -/
public noncomputable def fillingBase
    (D : ChosenToricFillingCoverModel Λ K B N) : N := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.model.coverMap.baseMap (D.model.boundaryProjection D.model.base)

/-- The map on fundamental groups induced by the toric filling inclusion. -/
public noncomputable def fundamentalGroupMap
    (D : ChosenToricFillingCoverModel Λ K B N) :
    FundamentalGroup B D.boundaryBase →* FundamentalGroup N D.fillingBase := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact FundamentalGroup.map D.model.coverMap.baseMap
    (D.model.boundaryProjection D.model.base)

/-- The exact induced fundamental-group calculation of the chosen toric filling model. -/
public noncomputable def fundamentalGroupData
    (D : ChosenToricFillingCoverModel Λ K B N) :
    letI := D.boundaryDeckGroup
    letI := D.fillingDeckGroup
    letI := D.boundaryCoverTopology
    letI := D.fillingCoverTopology
    letI := D.boundaryAction
    letI := D.fillingAction
    ToricFillingPiOneData D.model := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact establishedToricFillingPiOne D.model

/-- The lattice generators in the chosen toric boundary fundamental group. -/
public noncomputable def translation
    (D : ChosenToricFillingCoverModel Λ K B N) :
    Λ →+ Additive (FundamentalGroup B D.boundaryBase) := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.fundamentalGroupData.translation

/-- The angular meridian in the chosen toric boundary fundamental group. -/
public noncomputable def meridian
    (D : ChosenToricFillingCoverModel Λ K B N) :
    FundamentalGroup B D.boundaryBase := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.fundamentalGroupData.meridian

/-- The selected toric vanishing lattice map. -/
public noncomputable def vanishing
    (D : ChosenToricFillingCoverModel Λ K B N) : K →+ Λ := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.model.vanishing

/-- The toric filling inclusion is onto on fundamental groups. -/
public theorem fundamentalGroupMap_surjective
    (D : ChosenToricFillingCoverModel Λ K B N) :
    Function.Surjective D.fundamentalGroupMap := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.fundamentalGroupData.map_surjective

/-- The exact kernel of the toric filling inclusion. -/
public theorem fundamentalGroupMap_kernel
    (D : ChosenToricFillingCoverModel Λ K B N) :
    D.fundamentalGroupMap.ker = Subgroup.normalClosure
      (Set.range (fun k ↦ Additive.toMul (D.translation (D.vanishing k))) ∪
        {D.meridian}) := by
  letI := D.boundaryDeckGroup
  letI := D.fillingDeckGroup
  letI := D.boundaryCoverTopology
  letI := D.fillingCoverTopology
  letI := D.boundaryAction
  letI := D.fillingAction
  exact D.fundamentalGroupData.ker_map

/-- Every selected toric vanishing translation is killed by the filling inclusion. -/
public theorem fundamentalGroupMap_vanishing
    (D : ChosenToricFillingCoverModel Λ K B N) (k : K) :
    D.fundamentalGroupMap
      (Additive.toMul (D.translation (D.vanishing k))) = 1 := by
  change Additive.toMul (D.translation (D.vanishing k)) ∈
    D.fundamentalGroupMap.ker
  rw [D.fundamentalGroupMap_kernel]
  exact Subgroup.subset_normalClosure (Or.inl ⟨k, rfl⟩)

/-- The angular cusp meridian is killed by the toric filling inclusion. -/
public theorem fundamentalGroupMap_meridian
    (D : ChosenToricFillingCoverModel Λ K B N) :
    D.fundamentalGroupMap D.meridian = 1 := by
  change D.meridian ∈ D.fundamentalGroupMap.ker
  rw [D.fundamentalGroupMap_kernel]
  exact Subgroup.subset_normalClosure (Or.inr (Set.mem_singleton _))

end ChosenToricFillingCoverModel

end SphereSixComplex

end
