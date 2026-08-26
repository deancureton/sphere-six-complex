module

public import SphereSixComplex.Topology.AffineVanKampenTransport
public import SphereSixComplex.Geometry.PaperCentralFamilyTopology
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Equivariant universal covers with two free meridians

This module packages the source-independent covering-space definitions for an affine torus family
over a twice-punctured base.  The base deck group is explicitly `FreeGroup (Fin 2)`.  Its
generators are infinite-order meridians, even when their images in an orbifold deck group have
finite order.

Only definitions live here.  The remaining classification input, and the theorem deducing the
equivariant universal cover from it, are in `EstablishedEquivariantUniversalCover`, which is
downstream of the covering-space construction in `EstablishedEquivariantUniversalCoverProof`.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex

/-! ## The two-meridian deck group -/

/-- The deck group of a universal cover of a base with two free meridians. -/
public abbrev TwoMeridianDeckGroup := FreeGroup (Fin 2)

/-- The first positively oriented puncture meridian. -/
public def firstMeridian : TwoMeridianDeckGroup :=
  FreeGroup.of 0

/-- The second positively oriented puncture meridian. -/
public def secondMeridian : TwoMeridianDeckGroup :=
  FreeGroup.of 1

/-- Map the two free meridians to two specified elements of an orbifold deck group. -/
public def twoMeridianOrbifoldMap {Γ : Type*} [Group Γ]
    (gOne gTwo : Γ) : TwoMeridianDeckGroup →* Γ :=
  FreeGroup.lift (fun i ↦ if i = 0 then gOne else gTwo)

@[simp]
public theorem twoMeridianOrbifoldMap_first {Γ : Type*} [Group Γ]
    (gOne gTwo : Γ) : twoMeridianOrbifoldMap gOne gTwo firstMeridian = gOne := by
  simp [twoMeridianOrbifoldMap, firstMeridian]

@[simp]
public theorem twoMeridianOrbifoldMap_second {Γ : Type*} [Group Γ]
    (gOne gTwo : Γ) : twoMeridianOrbifoldMap gOne gTwo secondMeridian = gTwo := by
  simp [twoMeridianOrbifoldMap, secondMeridian]

/-- A finite-order relation in the orbifold group puts the corresponding power of the first free
meridian in the kernel, without imposing that relation in the free deck group itself. -/
public theorem firstMeridian_pow_mem_orbifoldKernel {Γ : Type*} [Group Γ]
    (gOne gTwo : Γ) (m : ℕ) (h : gOne ^ m = 1) :
    firstMeridian ^ m ∈ (twoMeridianOrbifoldMap gOne gTwo).ker := by
  simpa using h

/-- A finite-order relation in the orbifold group puts the corresponding power of the second free
meridian in the kernel, without imposing that relation in the free deck group itself. -/
public theorem secondMeridian_pow_mem_orbifoldKernel {Γ : Type*} [Group Γ]
    (gOne gTwo : Γ) (m : ℕ) (h : gTwo ^ m = 1) :
    secondMeridian ^ m ∈ (twoMeridianOrbifoldMap gOne gTwo).ker := by
  simpa using h

/-! ## Chosen universal covers -/

/-- A chosen regular universal cover whose deck group is free on two meridians.

This is the exact covering-space boundary needed below.  It is deliberately stated using the
cover itself: Mathlib currently has no bundled semilocally-simply-connected-space predicate or
general universal-cover existence theorem from which this data could be constructed. -/
public structure TwoMeridianUniversalCover
    (E B : Type*) [TopologicalSpace E] [TopologicalSpace B]
    [MulAction TwoMeridianDeckGroup E] where
  projection : C(E, B)
  quotientCovering : IsQuotientCoveringMap projection TwoMeridianDeckGroup
  simplyConnected : SimplyConnectedSpace E

/-! ## The affine deck extension -/

/-- Convert an additive lattice monodromy into its action on the multiplicative lattice. -/
public def multiplicativeLatticeMonodromy
    {Λ G : Type*} [AddCommGroup Λ] [Group G]
    (M : G →* Multiplicative (AddAut Λ)) : G →* MulAut (Multiplicative Λ) where
  toFun g := (M g).toAdd.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro a
    apply Multiplicative.toAdd.injective
    rw [map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro a
    apply Multiplicative.toAdd.injective
    change (M (g * h)).toAdd a.toAdd = (M g).toAdd ((M h).toAdd a.toAdd)
    rw [map_mul]
    rfl

/-- The monodromy of the free meridians, obtained by mapping them to the orbifold deck group. -/
public def freeTwoMeridianMonodromy
    {Λ Γ : Type*} [AddCommGroup Λ] [Group Γ]
    (orbifoldMap : TwoMeridianDeckGroup →* Γ)
    (orbifoldMonodromy : Γ →* Multiplicative (AddAut Λ)) :
    TwoMeridianDeckGroup →* Multiplicative (AddAut Λ) :=
  orbifoldMonodromy.comp orbifoldMap

/-- The split affine deck extension of the free base deck group by the translation lattice. -/
public abbrev FreeTwoMeridianAffineDeck
    (Λ : Type*) [AddCommGroup Λ]
    (M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ)) :=
  (Multiplicative Λ) ⋊[multiplicativeLatticeMonodromy M] TwoMeridianDeckGroup

/-- Embed the translation lattice in the affine deck group. -/
public def freeAffineTranslation
    {Λ : Type*} [AddCommGroup Λ]
    {M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ)} :
    Λ →+ Additive (FreeTwoMeridianAffineDeck Λ M) where
  toFun a := Additive.ofMul
    (SemidirectProduct.inl (φ := multiplicativeLatticeMonodromy M)
      (Multiplicative.ofAdd a))
  map_zero' := by
    apply Additive.toMul.injective
    exact map_one (SemidirectProduct.inl (φ := multiplicativeLatticeMonodromy M))
  map_add' a b := by
    apply Additive.toMul.injective
    exact map_mul (SemidirectProduct.inl (φ := multiplicativeLatticeMonodromy M))
      (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

public theorem freeAffineTranslation_injective
    {Λ : Type*} [AddCommGroup Λ]
    {M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ)} :
    Function.Injective (freeAffineTranslation (Λ := Λ) (M := M)) := by
  intro a b h
  have h' := congrArg SemidirectProduct.left (congrArg Additive.toMul h)
  change Multiplicative.ofAdd a = Multiplicative.ofAdd b at h'
  exact Multiplicative.ofAdd.injective h'

/-- Projection of the affine deck group to the free two-meridian deck group. -/
public def freeAffineBaseProjection
    {Λ : Type*} [AddCommGroup Λ]
    {M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ)} :
    FreeTwoMeridianAffineDeck Λ M →* TwoMeridianDeckGroup :=
  SemidirectProduct.rightHom

/-- The canonical lift of a free base-deck transformation. -/
public def freeAffineLift
    {Λ : Type*} [AddCommGroup Λ]
    {M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ)} :
    TwoMeridianDeckGroup →* FreeTwoMeridianAffineDeck Λ M :=
  SemidirectProduct.inr

public theorem freeAffineBaseProjection_ker
    {Λ : Type*} [AddCommGroup Λ]
    {M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ)}
    (d : FreeTwoMeridianAffineDeck Λ M) :
    freeAffineBaseProjection d = 1 ↔
      ∃ a, Additive.toMul (freeAffineTranslation a) = d := by
  constructor
  · intro h
    refine ⟨d.left.toAdd, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact h.symm
  · rintro ⟨a, rfl⟩
    rfl

public theorem freeAffine_conjugate
    {Λ : Type*} [AddCommGroup Λ]
    {M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ)}
    (g : TwoMeridianDeckGroup) (a : Λ) :
    freeAffineLift (Λ := Λ) (M := M) g *
        Additive.toMul (freeAffineTranslation (M := M) a) *
        (freeAffineLift (Λ := Λ) (M := M) g)⁻¹ =
      Additive.toMul (freeAffineTranslation (M := M) ((M g).toAdd a)) := by
  symm
  change SemidirectProduct.inl (Multiplicative.ofAdd ((M g).toAdd a)) =
    SemidirectProduct.inr g * SemidirectProduct.inl (Multiplicative.ofAdd a) *
      (SemidirectProduct.inr g)⁻¹
  convert SemidirectProduct.inl_aut
    (φ := multiplicativeLatticeMonodromy M) g (Multiplicative.ofAdd a) using 1
  · rfl
  · rw [map_inv]

/-! ## A reusable affine universal-cover boundary -/

/-- A simply connected equivariant affine cover over the free two-meridian base.

The action is an explicit lattice-by-free-group semidirect product.  `orbifoldMap` only records
how free meridians act on the intermediate orbifold cover; it does not add its finite-order
relations to the universal-cover deck group. -/
public structure EquivariantAffineUniversalCover
    (Λ Γ E X : Type*) [AddCommGroup Λ] [Group Γ]
    [TopologicalSpace E] [TopologicalSpace X]
    (orbifoldMap : TwoMeridianDeckGroup →* Γ)
    (orbifoldMonodromy : Γ →* Multiplicative (AddAut Λ))
    [MulAction (FreeTwoMeridianAffineDeck Λ
      (freeTwoMeridianMonodromy orbifoldMap orbifoldMonodromy)) E] where
  projection : C(E, X)
  quotientCovering : IsQuotientCoveringMap projection
    (FreeTwoMeridianAffineDeck Λ
      (freeTwoMeridianMonodromy orbifoldMap orbifoldMonodromy))
  simplyConnected : SimplyConnectedSpace E

/-- A bundled choice of the source, topology, affine deck action, and quotient-cover data. -/
public structure ChosenEquivariantAffineUniversalCover
    (Λ Γ X : Type*) [AddCommGroup Λ] [Group Γ] [TopologicalSpace X]
    (orbifoldMap : TwoMeridianDeckGroup →* Γ)
    (orbifoldMonodromy : Γ →* Multiplicative (AddAut Λ)) where
  Cover : Type
  topology : TopologicalSpace Cover
  action : MulAction (FreeTwoMeridianAffineDeck Λ
    (freeTwoMeridianMonodromy orbifoldMap orbifoldMonodromy)) Cover
  data : @EquivariantAffineUniversalCover Λ Γ Cover X _ _ topology _
    orbifoldMap orbifoldMonodromy action

namespace EquivariantAffineUniversalCover

variable {Λ Γ E X : Type*} [AddCommGroup Λ] [Group Γ]
variable [TopologicalSpace E] [TopologicalSpace X]
variable {orbifoldMap : TwoMeridianDeckGroup →* Γ}
variable {orbifoldMonodromy : Γ →* Multiplicative (AddAut Λ)}
variable [MulAction (FreeTwoMeridianAffineDeck Λ
  (freeTwoMeridianMonodromy orbifoldMap orbifoldMonodromy)) E]

/-- Forget the orbifold comparison and retain the exact affine universal-cover data. -/
public def toAffineTorusFamilyQuotientCover
    (D : EquivariantAffineUniversalCover Λ Γ E X orbifoldMap orbifoldMonodromy) :
    AffineTorusFamilyQuotientCover Λ TwoMeridianDeckGroup
      (FreeTwoMeridianAffineDeck Λ
        (freeTwoMeridianMonodromy orbifoldMap orbifoldMonodromy)) E X where
  projection := D.projection
  quotientCovering := D.quotientCovering
  simplyConnected := D.simplyConnected
  translation := freeAffineTranslation
  translation_injective := freeAffineTranslation_injective
  baseProjection := freeAffineBaseProjection
  baseProjection_surjective := SemidirectProduct.rightHom_surjective
  baseProjection_ker := freeAffineBaseProjection_ker
  lift := freeAffineLift
  lift_projects := SemidirectProduct.rightHom_inr
  monodromy := freeTwoMeridianMonodromy orbifoldMap orbifoldMonodromy
  conjugate := freeAffine_conjugate
  cocycle := fun _ _ ↦ 0
  lift_mul := by
    intro g h
    simp [freeAffineLift, freeAffineTranslation]

end EquivariantAffineUniversalCover

namespace ChosenEquivariantAffineUniversalCover

variable {Λ Γ X : Type*} [AddCommGroup Λ] [Group Γ] [TopologicalSpace X]
variable {orbifoldMap : TwoMeridianDeckGroup →* Γ}
variable {orbifoldMonodromy : Γ →* Multiplicative (AddAut Λ)}

/-- The chosen cover as an affine torus-family quotient cover. -/
public def toAffineTorusFamilyQuotientCover
    (D : ChosenEquivariantAffineUniversalCover Λ Γ X orbifoldMap orbifoldMonodromy) :
    letI := D.topology
    letI := D.action
    AffineTorusFamilyQuotientCover Λ TwoMeridianDeckGroup
      (FreeTwoMeridianAffineDeck Λ
        (freeTwoMeridianMonodromy orbifoldMap orbifoldMonodromy)) D.Cover X := by
  letI := D.topology
  letI := D.action
  exact D.data.toAffineTorusFamilyQuotientCover

end ChosenEquivariantAffineUniversalCover

/-! ## The semidirect-product core presentation -/

/-- Monodromy on the lattice around the first free meridian. -/
public def firstFreeMonodromy
    {Λ : Type*} [AddCommGroup Λ]
    (M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ)) : Λ →+ Λ :=
  (M firstMeridian).toAdd.toAddMonoidHom

/-- Monodromy on the lattice around the second free meridian. -/
public def secondFreeMonodromy
    {Λ : Type*} [AddCommGroup Λ]
    (M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ)) : Λ →+ Λ :=
  (M secondMeridian).toAdd.toAddMonoidHom

/-- The translation lattice inside the opposite affine deck group. -/
public def oppositeFreeAffineTranslation
    {Λ : Type*} [AddCommGroup Λ]
    {M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ)} :
    Λ →+ Additive (FreeTwoMeridianAffineDeck Λ M)ᵐᵒᵖ where
  toFun a := Additive.ofMul (MulOpposite.op (Additive.toMul (freeAffineTranslation a)))
  map_zero' := by
    apply Additive.toMul.injective
    simp [freeAffineTranslation]
  map_add' a b := by
    apply Additive.toMul.injective
    apply MulOpposite.unop_injective
    change SemidirectProduct.inl (Multiplicative.ofAdd (a + b)) =
      SemidirectProduct.inl (Multiplicative.ofAdd b) *
        SemidirectProduct.inl (Multiplicative.ofAdd a)
    rw [add_comm]
    exact map_mul (SemidirectProduct.inl (φ := multiplicativeLatticeMonodromy M))
      (Multiplicative.ofAdd b) (Multiplicative.ofAdd a)

/-- The affine semidirect product, in covering-space orientation, is generated by the lattice and
the inverse lifts of the two free meridians. -/
public theorem oppositeFreeAffine_generators_generate
    {Λ : Type*} [AddCommGroup Λ]
    {M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ)} :
    Subgroup.closure
      (Set.range (fun a ↦ Additive.toMul
        (oppositeFreeAffineTranslation (M := M) a)) ∪
        {MulOpposite.op (freeAffineLift (Λ := Λ) (M := M) firstMeridian)⁻¹,
          MulOpposite.op (freeAffineLift (Λ := Λ) (M := M) secondMeridian)⁻¹}) = ⊤ := by
  let K : Subgroup (FreeTwoMeridianAffineDeck Λ M)ᵐᵒᵖ := Subgroup.closure
    (Set.range (fun a ↦ Additive.toMul
      (oppositeFreeAffineTranslation (M := M) a)) ∪
      {MulOpposite.op (freeAffineLift (Λ := Λ) (M := M) firstMeridian)⁻¹,
        MulOpposite.op (freeAffineLift (Λ := Λ) (M := M) secondMeridian)⁻¹})
  let r : TwoMeridianDeckGroup →* (FreeTwoMeridianAffineDeck Λ M)ᵐᵒᵖ :=
    (MonoidHom.op (freeAffineLift (Λ := Λ) (M := M))).comp
      (MulEquiv.inv' TwoMeridianDeckGroup).toMonoidHom
  have hrange : Set.range (FreeGroup.of : Fin 2 → TwoMeridianDeckGroup) ⊆ K.comap r := by
    rintro _ ⟨i, rfl⟩
    change r (FreeGroup.of i) ∈ K
    fin_cases i
    · apply Subgroup.subset_closure
      simp [r, firstMeridian]
    · apply Subgroup.subset_closure
      simp [r, secondMeridian]
  have hr : ∀ g, r g ∈ K := by
    intro g
    have hclosure : Subgroup.closure
        (Set.range (FreeGroup.of : Fin 2 → TwoMeridianDeckGroup)) ≤ K.comap r :=
      (Subgroup.closure_le (K.comap r)).2 hrange
    apply hclosure
    rw [FreeGroup.closure_range_of]
    trivial
  apply top_unique
  intro z _
  let d := MulOpposite.unop z
  have hright : MulOpposite.op (freeAffineLift (Λ := Λ) (M := M) d.right) ∈ K := by
    simpa [r] using hr d.right⁻¹
  have hleft : MulOpposite.op
      (Additive.toMul (freeAffineTranslation (M := M) d.left.toAdd)) ∈ K := by
    apply Subgroup.subset_closure
    exact Or.inl ⟨d.left.toAdd, rfl⟩
  rw [← show MulOpposite.op d = z by rfl]
  rw [← SemidirectProduct.inl_left_mul_inr_right d, MulOpposite.op_mul]
  exact K.mul_mem hright hleft

/-- The source-independent affine core presentation carried by the opposite deck group. -/
public def oppositeFreeAffineCorePiOneData
    {Λ : Type*} [AddCommGroup Λ]
    (M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ)) :
    AffineTorusCorePiOneData (FreeTwoMeridianAffineDeck Λ M)ᵐᵒᵖ Λ
      (firstFreeMonodromy M) (secondFreeMonodromy M) where
  translation := oppositeFreeAffineTranslation
  rhoOne := MulOpposite.op (freeAffineLift firstMeridian)⁻¹
  rhoTwo := MulOpposite.op (freeAffineLift secondMeridian)⁻¹
  conjugate_one a := by
    apply MulOpposite.unop_injective
    simpa [oppositeFreeAffineTranslation, firstFreeMonodromy, mul_assoc] using
      freeAffine_conjugate (Λ := Λ) (M := M) firstMeridian a
  conjugate_two a := by
    apply MulOpposite.unop_injective
    simpa [oppositeFreeAffineTranslation, secondFreeMonodromy, mul_assoc] using
      freeAffine_conjugate (Λ := Λ) (M := M) secondMeridian a
  generators_generate := oppositeFreeAffine_generators_generate

namespace EquivariantAffineUniversalCover

variable {Λ Γ E X : Type*} [AddCommGroup Λ] [Group Γ]
variable [TopologicalSpace E] [TopologicalSpace X]
variable {orbifoldMap : TwoMeridianDeckGroup →* Γ}
variable {orbifoldMonodromy : Γ →* Multiplicative (AddAut Λ)}
variable [MulAction (FreeTwoMeridianAffineDeck Λ
  (freeTwoMeridianMonodromy orbifoldMap orbifoldMonodromy)) E]

/-- The based fundamental group presentation obtained from the affine universal cover. -/
public def fundamentalGroupCorePiOneData
    (D : EquivariantAffineUniversalCover Λ Γ E X orbifoldMap orbifoldMonodromy)
    (e : E) :
    AffineTorusCorePiOneData (FundamentalGroup X (D.projection e)) Λ
      (firstFreeMonodromy (freeTwoMeridianMonodromy orbifoldMap orbifoldMonodromy))
      (secondFreeMonodromy (freeTwoMeridianMonodromy orbifoldMap orbifoldMonodromy)) :=
  (oppositeFreeAffineCorePiOneData
    (freeTwoMeridianMonodromy orbifoldMap orbifoldMonodromy)).mapSurjective
      (D.toAffineTorusFamilyQuotientCover.fundamentalGroupEquiv e).symm.toMonoidHom
      (D.toAffineTorusFamilyQuotientCover.fundamentalGroupEquiv e).symm.surjective

end EquivariantAffineUniversalCover

/-! ## The Fuchsian pair-of-pants classification boundary -/

namespace Geometry.GlobalTorusFamily

open Periods TriangleGroup Geometry.ComplexTorus

/-- Integral period monodromy, tagged multiplicatively as an orbifold representation. -/
public noncomputable def integralOrbifoldPeriodMonodromy :
    Delta →* Multiplicative (AddAut IntegerPeriods) where
  toFun g := Multiplicative.ofAdd (rhoLambda g).toAddEquiv
  map_one' := by
    apply Multiplicative.toAdd.injective
    rw [map_one]
    rfl
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    rw [map_mul]
    rfl

end Geometry.GlobalTorusFamily

end SphereSixComplex

end
