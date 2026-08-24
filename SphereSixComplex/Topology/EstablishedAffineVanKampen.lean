module

public import SphereSixComplex.Topology.WangHomologyPresentation
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Established fundamental-group inputs for affine torus gluings

This module isolates source-independent nonabelian topology missing from Mathlib: the fundamental
group presentation of a mapping torus and the quotient-cover squares used to compute filling maps.
The interfaces retain the deck groups and their kernels, so no paper-specific presentation is
assumed here.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex

/-! ## Mapping-torus fundamental groups -/

/-- The base point of a circle mapping torus induced by a point of its fibre. -/
public def circleMappingTorusBase {F : Type} [TopologicalSpace F]
    (φ : F ≃ₜ F) (x : F) : CircleMappingTorus φ :=
  finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ φ) x

/-- The homomorphism on fundamental groups induced by the mapping-torus fibre inclusion. -/
public def circleMappingTorusFiberHom {F : Type} [TopologicalSpace F]
    (φ : F ≃ₜ F) (x : F) :
    FundamentalGroup F x →*
      FundamentalGroup (CircleMappingTorus φ) (circleMappingTorusBase φ x) :=
  FundamentalGroup.map (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ φ)) x

/-- Monodromy on the based fundamental group, including the required change of base point. -/
public def mappingTorusMonodromyHom {F : Type} [TopologicalSpace F]
    (φ : F ≃ₜ F) (x : F) (δ : Path (φ x) x) :
    FundamentalGroup F x →* FundamentalGroup F x :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath δ).toMonoidHom.comp
    (FundamentalGroup.map ⟨φ, φ.continuous⟩ x)

/-- The positively oriented cylinder edge in a circle mapping torus. -/
public def circleMappingTorusEdgePath {F : Type} [TopologicalSpace F]
    (φ : F ≃ₜ F) (x : F) :
    Path (circleMappingTorusBase φ x) (circleMappingTorusBase φ (φ x)) where
  toFun t :=
    Quotient.mk (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ φ)) ((), (t, x))
  continuous_toFun := continuous_quot_mk.comp
    (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  source' := rfl
  target' := by
    apply Quotient.sound
    apply Relation.EqvGen.rel
    exact Or.inr (Or.inr ⟨by simp, by simp, rfl⟩)

/-- The geometric mapping-torus meridian, closed by a chosen fibre connector. -/
public def circleMappingTorusMeridian {F : Type} [TopologicalSpace F]
    (φ : F ≃ₜ F) (x : F) (δ : Path (φ x) x) :
    FundamentalGroup (CircleMappingTorus φ) (circleMappingTorusBase φ x) :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk
      ((circleMappingTorusEdgePath φ x).trans
        (δ.map (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ φ)).continuous)))

/-- The universal fundamental-group presentation of a mapping torus.

The distinguished element is the positively oriented base-circle meridian, closed using `δ`.
The universal property records both generation and the absence of additional relations. -/
public structure MappingTorusFundamentalGroupUP {F : Type} [TopologicalSpace F]
    (φ : F ≃ₜ F) (x : F) (δ : Path (φ x) x) where
  conjugate : ∀ a,
    circleMappingTorusMeridian φ x δ * circleMappingTorusFiberHom φ x a *
        (circleMappingTorusMeridian φ x δ)⁻¹ =
      circleMappingTorusFiberHom φ x (mappingTorusMonodromyHom φ x δ a)
  lift : ∀ {H : Type} [Group H]
    (f : FundamentalGroup F x →* H) (t : H),
    (∀ a, t * f a * t⁻¹ = f (mappingTorusMonodromyHom φ x δ a)) →
      FundamentalGroup (CircleMappingTorus φ) (circleMappingTorusBase φ x) →* H
  lift_fiber : ∀ {H : Type} [Group H]
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a, t * f a * t⁻¹ = f (mappingTorusMonodromyHom φ x δ a)) (a),
      lift f t h (circleMappingTorusFiberHom φ x a) = f a
  lift_meridian : ∀ {H : Type} [Group H]
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a, t * f a * t⁻¹ = f (mappingTorusMonodromyHom φ x δ a)),
      lift f t h (circleMappingTorusMeridian φ x δ) = t
  hom_ext : ∀ {H : Type} [Group H]
    (f g : FundamentalGroup (CircleMappingTorus φ) (circleMappingTorusBase φ x) →* H),
    (∀ a, f (circleMappingTorusFiberHom φ x a) =
      g (circleMappingTorusFiberHom φ x a)) →
    f (circleMappingTorusMeridian φ x δ) =
      g (circleMappingTorusMeridian φ x δ) → f = g

/-- The standard HNN-extension presentation of the fundamental group of a mapping torus. -/
public axiom establishedMappingTorusFundamentalGroupUP
    {F : Type} [TopologicalSpace F] [PathConnectedSpace F]
    (φ : F ≃ₜ F) (x : F) (δ : Path (φ x) x) :
    MappingTorusFundamentalGroupUP φ x δ

/-! ## Affine torus-family quotient covers -/

/-- An equivariant map between two regular quotient covers. -/
public structure QuotientCoverMapData
    {E E' X X' G H : Type*}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X] [TopologicalSpace X']
    [Group G] [Group H] [MulAction G E] [MulAction H E']
    (p : C(E, X)) (q : C(E', X')) where
  deckMap : G →* H
  lift : C(E, E')
  baseMap : C(X, X')
  commutes : ∀ z, baseMap (p z) = q (lift z)
  equivariant : ∀ g z, lift (g • z) = deckMap g • lift z

/-- Equivariant maps of simply connected regular covers induce the corresponding deck-group
homomorphism under the standard fundamental-group equivalences. -/
public axiom establishedQuotientCoverFundamentalGroupNaturality
    {E E' X X' G H : Type*}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X] [TopologicalSpace X']
    [Group G] [Group H] [MulAction G E] [MulAction H E']
    [SimplyConnectedSpace E] [SimplyConnectedSpace E']
    {p : C(E, X)} {q : C(E', X')}
    (hp : IsQuotientCoveringMap p G) (hq : IsQuotientCoveringMap q H)
    (D : QuotientCoverMapData (G := G) (H := H) p q) (e : E)
    (γ : FundamentalGroup X (p e)) :
    (MonoidHom.op D.deckMap) (hp.fundamentalGroupEquiv ⟨e, rfl⟩ γ) =
      hq.fundamentalGroupEquiv ⟨D.lift e, rfl⟩
        (FundamentalGroup.mapOfEq D.baseMap (D.commutes e) γ)

/-! ## Algebraic output of an affine torus core -/

/-- The based fundamental-group presentation of an affine torus bundle over a bouquet of two
circles. The final field is the exact generation statement supplied by the bouquet presentation. -/
public structure AffineTorusCorePiOneData
    (G Λ : Type*) [Group G] [AddCommGroup Λ]
    (monodromyOne monodromyTwo : Λ →+ Λ) where
  translation : Λ →+ Additive G
  rhoOne : G
  rhoTwo : G
  conjugate_one : ∀ a,
    rhoOne * Additive.toMul (translation a) * rhoOne⁻¹ =
      Additive.toMul (translation (monodromyOne a))
  conjugate_two : ∀ a,
    rhoTwo * Additive.toMul (translation a) * rhoTwo⁻¹ =
      Additive.toMul (translation (monodromyTwo a))
  generators_generate : Subgroup.closure
    (Set.range (fun a ↦ Additive.toMul (translation a)) ∪ {rhoOne, rhoTwo}) = ⊤

/-- Filling relations imposed on an affine torus core, stated independently of any particular
lattice, monodromy matrices, or filling orders. -/
public structure AffineTorusStarFillingRelations
    {G Λ : Type*} [Group G] [AddCommGroup Λ]
    {monodromyOne monodromyTwo : Λ →+ Λ}
    (C : AffineTorusCorePiOneData G Λ monodromyOne monodromyTwo)
    (orderOne orderTwo : ℕ) (twistOne twistTwo cuspTwist : Λ)
    (toricSubgroup : AddSubgroup Λ) : Prop where
  elliptic_one : C.rhoOne ^ orderOne = Additive.toMul (C.translation twistOne)
  elliptic_two : C.rhoTwo ^ orderTwo = Additive.toMul (C.translation twistTwo)
  cusp : C.rhoOne * C.rhoTwo = Additive.toMul (C.translation cuspTwist)
  toric_vanishes : ∀ a ∈ toricSubgroup, Additive.toMul (C.translation a) = 1

/-- A simply connected affine deck cover of a torus family.

The deck group is an extension of `Γ` by the translation lattice `Λ`. The chosen lifts and
cocycle retain the exact monodromy and twist information needed for finite-order relations. -/
public structure AffineTorusFamilyQuotientCover
    (Λ Γ Deck E X : Type*)
    [AddCommGroup Λ] [Group Γ] [Group Deck]
    [TopologicalSpace E] [TopologicalSpace X] [MulAction Deck E] where
  projection : C(E, X)
  quotientCovering : IsQuotientCoveringMap projection Deck
  simplyConnected : SimplyConnectedSpace E
  translation : Λ →+ Additive Deck
  translation_injective : Function.Injective translation
  baseProjection : Deck →* Γ
  baseProjection_surjective : Function.Surjective baseProjection
  baseProjection_ker : ∀ d,
    baseProjection d = 1 ↔ ∃ a, Additive.toMul (translation a) = d
  lift : Γ → Deck
  lift_projects : ∀ g, baseProjection (lift g) = g
  monodromy : Γ →* Multiplicative (AddAut Λ)
  conjugate : ∀ g a,
    lift g * Additive.toMul (translation a) * (lift g)⁻¹ =
      Additive.toMul (translation ((monodromy g).toAdd a))
  cocycle : Γ → Γ → Λ
  lift_mul : ∀ g h,
    lift g * lift h =
      Additive.toMul (translation (cocycle g h)) * lift (g * h)

namespace AffineTorusFamilyQuotientCover

variable {Λ Γ Deck E X : Type*}
variable [AddCommGroup Λ] [Group Γ] [Group Deck]
variable [TopologicalSpace E] [TopologicalSpace X] [MulAction Deck E]

/-- The deck-group description of the fundamental group of an affine torus-family quotient. -/
public def fundamentalGroupEquiv
    (D : AffineTorusFamilyQuotientCover Λ Γ Deck E X) (e : E) :
    FundamentalGroup X (D.projection e) ≃* Deckᵐᵒᵖ := by
  let _ : SimplyConnectedSpace E := D.simplyConnected
  exact D.quotientCovering.fundamentalGroupEquiv ⟨e, rfl⟩

end AffineTorusFamilyQuotientCover

/-! ## Filling maps from quotient-cover squares -/

/-- A regular-cover model for a toric filling and its boundary inclusion. -/
public structure ToricFillingCoverModel
    (Λ K G H E E' B N : Type*)
    [AddCommGroup Λ] [AddCommGroup K] [Group G] [Group H]
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] [TopologicalSpace N]
    [MulAction G E] [MulAction H E'] where
  boundaryProjection : C(E, B)
  fillingProjection : C(E', N)
  boundaryQuotient : IsQuotientCoveringMap boundaryProjection G
  fillingQuotient : IsQuotientCoveringMap fillingProjection H
  boundarySimplyConnected : SimplyConnectedSpace E
  fillingSimplyConnected : SimplyConnectedSpace E'
  coverMap : QuotientCoverMapData (G := G) (H := H)
    boundaryProjection fillingProjection
  base : E
  deckTranslation : Λ →+ Additive G
  deckMeridian : G
  vanishing : K →+ Λ
  deckMap_surjective : Function.Surjective coverMap.deckMap
  deckMap_kernel : coverMap.deckMap.ker = Subgroup.normalClosure
    (Set.range (fun k ↦ Additive.toMul (deckTranslation (vanishing k))) ∪ {deckMeridian})

namespace ToricFillingCoverModel

variable {Λ K G H E E' B N : Type*}
variable [AddCommGroup Λ] [AddCommGroup K] [Group G] [Group H]
variable [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
variable [TopologicalSpace N] [MulAction G E] [MulAction H E']

/-- Identify the boundary fundamental group with the opposite boundary deck group. -/
public def boundaryFundamentalGroupEquiv
    (D : ToricFillingCoverModel Λ K G H E E' B N) :
    FundamentalGroup B (D.boundaryProjection D.base) ≃* Gᵐᵒᵖ := by
  let _ : SimplyConnectedSpace E := D.boundarySimplyConnected
  exact D.boundaryQuotient.fundamentalGroupEquiv ⟨D.base, rfl⟩

end ToricFillingCoverModel

/-- Exact induced-`π₁` data for a toric filling. -/
public structure ToricFillingPiOneData
    {Λ K G H E E' B N : Type*}
    [AddCommGroup Λ] [AddCommGroup K] [Group G] [Group H]
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] [TopologicalSpace N]
    [MulAction G E] [MulAction H E']
    (D : ToricFillingCoverModel Λ K G H E E' B N) where
  translation : Λ →+ Additive (FundamentalGroup B (D.boundaryProjection D.base))
  meridian : FundamentalGroup B (D.boundaryProjection D.base)
  translation_deck : ∀ a,
    D.boundaryFundamentalGroupEquiv (Additive.toMul (translation a)) =
      MulOpposite.op (Additive.toMul (D.deckTranslation a))
  meridian_deck : D.boundaryFundamentalGroupEquiv meridian =
    MulOpposite.op D.deckMeridian
  map_surjective : Function.Surjective
    (FundamentalGroup.map D.coverMap.baseMap (D.boundaryProjection D.base))
  ker_map :
    (FundamentalGroup.map D.coverMap.baseMap (D.boundaryProjection D.base)).ker =
      Subgroup.normalClosure
        (Set.range (fun k ↦ Additive.toMul (translation (D.vanishing k))) ∪ {meridian})

/-- The standard toric-filling computation obtained from an equivariant regular-cover square. -/
public axiom establishedToricFillingPiOne
    {Λ K G H E E' B N : Type*}
    [AddCommGroup Λ] [AddCommGroup K] [Group G] [Group H]
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] [TopologicalSpace N]
    [MulAction G E] [MulAction H E']
    (D : ToricFillingCoverModel Λ K G H E E' B N) :
    ToricFillingPiOneData D

/-- A regular-cover model for a cyclic affine filling and its boundary inclusion. -/
public structure CyclicAffineFillingCoverModel
    (m : ℕ) (Λ G H E E' B N : Type*)
    [NeZero m] [AddCommGroup Λ] [Group G] [Group H]
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] [TopologicalSpace N]
    [MulAction G E] [MulAction H E'] where
  boundaryProjection : C(E, B)
  fillingProjection : C(E', N)
  boundaryQuotient : IsQuotientCoveringMap boundaryProjection G
  fillingQuotient : IsQuotientCoveringMap fillingProjection H
  boundarySimplyConnected : SimplyConnectedSpace E
  fillingSimplyConnected : SimplyConnectedSpace E'
  coverMap : QuotientCoverMapData (G := G) (H := H)
    boundaryProjection fillingProjection
  base : E
  deckTranslation : Λ →+ Additive G
  deckMeridian : G
  monodromy : Multiplicative (AddAut Λ)
  twist : Λ
  monodromy_pow : monodromy ^ m = 1
  twist_fixed : monodromy.toAdd twist = twist
  deckMap_surjective : Function.Surjective coverMap.deckMap
  deckMap_kernel : coverMap.deckMap.ker = Subgroup.normalClosure
    {deckMeridian ^ m * (Additive.toMul (deckTranslation twist))⁻¹}

namespace CyclicAffineFillingCoverModel

variable {m : ℕ} {Λ G H E E' B N : Type*}
variable [NeZero m] [AddCommGroup Λ] [Group G] [Group H]
variable [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
variable [TopologicalSpace N] [MulAction G E] [MulAction H E']

/-- Identify the cyclic boundary fundamental group with its opposite deck group. -/
public def boundaryFundamentalGroupEquiv
    (D : CyclicAffineFillingCoverModel m Λ G H E E' B N) :
    FundamentalGroup B (D.boundaryProjection D.base) ≃* Gᵐᵒᵖ := by
  let _ : SimplyConnectedSpace E := D.boundarySimplyConnected
  exact D.boundaryQuotient.fundamentalGroupEquiv ⟨D.base, rfl⟩

end CyclicAffineFillingCoverModel

/-- Exact induced-`π₁` data for a cyclic affine filling. -/
public structure CyclicAffineFillingPiOneData
    {m : ℕ} {Λ G H E E' B N : Type*}
    [NeZero m] [AddCommGroup Λ] [Group G] [Group H]
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] [TopologicalSpace N]
    [MulAction G E] [MulAction H E']
    (D : CyclicAffineFillingCoverModel m Λ G H E E' B N) where
  translation : Λ →+ Additive (FundamentalGroup B (D.boundaryProjection D.base))
  meridian : FundamentalGroup B (D.boundaryProjection D.base)
  translation_deck : ∀ a,
    D.boundaryFundamentalGroupEquiv (Additive.toMul (translation a)) =
      MulOpposite.op (Additive.toMul (D.deckTranslation a))
  meridian_deck : D.boundaryFundamentalGroupEquiv meridian =
    MulOpposite.op D.deckMeridian
  map_surjective : Function.Surjective
    (FundamentalGroup.map D.coverMap.baseMap (D.boundaryProjection D.base))
  ker_map :
    (FundamentalGroup.map D.coverMap.baseMap (D.boundaryProjection D.base)).ker =
      Subgroup.normalClosure
        {meridian ^ m * (Additive.toMul (translation D.twist))⁻¹}

/-- The standard cyclic-affine-filling computation from an equivariant regular-cover square. -/
public axiom establishedCyclicAffineFillingPiOne
    {m : ℕ} {Λ G H E E' B N : Type*}
    [NeZero m] [AddCommGroup Λ] [Group G] [Group H]
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] [TopologicalSpace N]
    [MulAction G E] [MulAction H E']
    (D : CyclicAffineFillingCoverModel m Λ G H E E' B N) :
    CyclicAffineFillingPiOneData D

end SphereSixComplex

end
