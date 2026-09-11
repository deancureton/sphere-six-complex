module

public import SphereSixComplex.Paper.Topology.AffineVanKampenTransport
public import SphereSixComplex.Paper.Geometry.PaperCentralFamilyTopology
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



/-! ## Chosen universal covers -/


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



/-- The canonical lift of a free base-deck transformation. -/
public def freeAffineLift
    {Λ : Type*} [AddCommGroup Λ]
    {M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ)} :
    TwoMeridianDeckGroup →* FreeTwoMeridianAffineDeck Λ M :=
  SemidirectProduct.inr



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
