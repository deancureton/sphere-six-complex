module

public import SphereSixComplex.Topology.ActualCuspCentralFiberRetraction
public import SphereSixComplex.Topology.CollarHomotopyExtension
public import SphereSixComplex.Topology.ContractibleRegularCoverInclusionProof
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.CWComplex.Classical.Basic
import SphereSixComplex.Topology.RelativeHomotopy

/-!
# Established strong-deformation-retract principles

This file proves two standard general-topology principles that are not packaged in Mathlib, in
the interfaces (`HasHomotopyExtensionProperty`, `IsHomotopyEquivalenceInclusion`,
`StrongDeformationRetraction`, `IsQuotientCoveringMap`, `EquivariantStrongDeformationRetraction`)
through which the rest of the library consumes them.

## Main results

* `EstablishedGeneralTopology.strongDeformationRetraction_of_cofibration_homotopyEquivalence`: a
  subspace inclusion with the homotopy-extension property which is a homotopy equivalence is the
  inclusion of a strong deformation retract (Hatcher, *Algebraic Topology*, Cor. 0.20).  Hatcher's
  Prop. 0.19 is already formalised for an arbitrary map in `RelativeHomotopy.lean`
  (`HomotopyExtensionProperty.exists_strongDeformationRetractData`, built on
  `CollarHomotopyExtension.lean` and `PushoutHomotopy.lean`); the theorem reads it through the
  translations `hasHomotopyExtensionProperty_iff`, `isHomotopyEquivalenceInclusion_iff` and the
  converter `TopCat.StrongDeformationRetractData.toStrongDeformationRetraction`, via
  `HomotopyExtensionProperty.nonempty_strongDeformationRetraction` (Cor. 0.20 for a map).
* `EstablishedGeneralTopology.isHomotopyEquivalenceInclusion_of_contractible_regularCover`: if a
  regular covering and the full inverse image of a subspace are contractible then, for a relative
  CW pair, the subspace inclusion is a homotopy equivalence.  The covering-space content is proved
  in `ContractibleRegularCoverInclusionProof`; only the uniqueness of `K(G, 1)` spaces
  (`isHomotopyEquivalenceInclusion_of_isAspherical_of_bijective_fundamentalGroup`) is assumed.
* `EstablishedGeneralTopology.equivariantStrongDeformationRetraction_lift`: a strong deformation
  retraction of the base lifts through the orbit map of a covering space action to a
  deck-equivariant strong deformation retraction of the total space onto the full preimage
  (Hatcher, Prop. 1.30 with Prop. 1.40(a)), from Mathlib's `IsCoveringMap.liftPath` and
  `IsLocalHomeomorph.continuous_lift` (`liftTrack` and its API below).

`HasHomotopyExtensionProperty` quantifies its target spaces over the universe of the ambient
space, as Hatcher's proof of Cor. 0.20 applies the homotopy-extension property with the targets
`A` and `X` themselves.

The one remaining `axiom` of `EstablishedGeneralTopology` is the uniqueness of `K(G, 1)` spaces
(`isHomotopyEquivalenceInclusion_of_isAspherical_of_bijective_fundamentalGroup`), tracked as a
separate follow-up.  It is purely CW-theoretic: all covering-space and homotopy-group content of
the former `K(G, 1)` axiom is proved in `ContractibleRegularCoverInclusionProof`, and
`isHomotopyEquivalenceInclusion_of_contractible_regularCover` is a theorem deduced from it.  The
homotopy-extension property of a relative CW pair, formerly an axiom here, is proved in
`RelativeCWHomotopyExtensionProof` as
`hasHomotopyExtensionProperty_of_relativeCWComplex_proved`.

The subspace-inclusion definitions `topologicalSubsetInclusionMap` and
`IsHomotopyEquivalenceInclusion` live in `EstablishedStrongDeformationRetractsDefs`, upstream of
that proof file, and are re-exported here.
-/

@[expose] public section

noncomputable section

open Set Topology unitInterval
open scoped ContinuousMap

universe u

namespace SphereSixComplex

/-- The homotopy-extension property for the inclusion `A ⊆ X`. -/
public def HasHomotopyExtensionProperty {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (Y : Type u) (_ : TopologicalSpace Y) (f : C(X, Y)) (g : C(A, Y))
    (h : ContinuousMap.Homotopy (f.comp (topologicalSubsetInclusionMap A)) g),
    ∃ (f₁ : C(X, Y)) (H : ContinuousMap.Homotopy f f₁),
      ∀ s (a : A), H (s, (a : X)) = h (s, a)

/-- Extract the homotopy equivalence recorded by a homotopy-equivalent subspace inclusion. -/
public noncomputable def IsHomotopyEquivalenceInclusion.toHomotopyEquiv
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsHomotopyEquivalenceInclusion A) : X ≃ₕ A :=
  Classical.choose h

public theorem IsHomotopyEquivalenceInclusion.toHomotopyEquiv_invFun
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsHomotopyEquivalenceInclusion A) :
    h.toHomotopyEquiv.invFun = topologicalSubsetInclusionMap A :=
  Classical.choose_spec h

/-- A non-equivariant strong deformation retraction onto a subspace. -/
public structure StrongDeformationRetraction (X : Type*) [TopologicalSpace X] (A : Set X) where
  retract : C(X, X)
  homotopy : ContinuousMap.Homotopy (ContinuousMap.id X) retract
  retract_mem : ∀ x, retract x ∈ A
  retract_fixed : ∀ x, x ∈ A → retract x = x
  homotopy_fixed : ∀ s x, x ∈ A → homotopy (s, x) = x

/-- A strong deformation retraction gives a homotopy equivalence to the retract, whose inverse
is the literal subspace inclusion. -/
public def StrongDeformationRetraction.toHomotopyEquiv
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (R : StrongDeformationRetraction X A) : X ≃ₕ A := by
  let r : C(X, A) :=
    { toFun := fun x ↦ ⟨R.retract x, R.retract_mem x⟩
      continuous_toFun := R.retract.continuous.subtype_mk _ }
  refine
    { toFun := r
      invFun := topologicalSubsetInclusionMap A
      left_inv := ⟨R.homotopy.symm⟩
      right_inv := ?_ }
  have h : r.comp (topologicalSubsetInclusionMap A) = ContinuousMap.id A := by
    ext a
    exact R.retract_fixed a a.2
  rw [h]

/-! ## Interface translations -/

/-- The subspace form of the homotopy-extension property is the map form for the subspace
inclusion.  Source: Hatcher, *Algebraic Topology*, §0 p. 14 (definition of the homotopy extension
property). -/
public theorem hasHomotopyExtensionProperty_iff {X : Type u} [TopologicalSpace X] (A : Set X) :
    HasHomotopyExtensionProperty A ↔ HomotopyExtensionProperty (topologicalSubsetInclusionMap A) :=
  ⟨.mk, HomotopyExtensionProperty.extend⟩

public alias ⟨HasHomotopyExtensionProperty.homotopyExtensionProperty,
  HomotopyExtensionProperty.hasHomotopyExtensionProperty⟩ := hasHomotopyExtensionProperty_iff

/-- The subspace inclusion is a homotopy equivalence in the sense of `IsHomotopyEquivalence` iff it
is one in the sense of `IsHomotopyEquivalenceInclusion`.  Source: Hatcher, *Algebraic Topology*,
Cor. 0.20 p. 16 (hypothesis "the inclusion `A ↪ X` is a homotopy equivalence"). -/
public theorem isHomotopyEquivalenceInclusion_iff {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsHomotopyEquivalenceInclusion A ↔
      IsHomotopyEquivalence ⇑(topologicalSubsetInclusionMap A) :=
  ⟨fun ⟨e, he⟩ ↦ ⟨e.symm, congrArg DFunLike.coe he⟩, fun ⟨e, he⟩ ↦ ⟨e.symm, DFunLike.ext' he⟩⟩

public alias ⟨IsHomotopyEquivalenceInclusion.isHomotopyEquivalence,
  IsHomotopyEquivalence.isHomotopyEquivalenceInclusion⟩ := isHomotopyEquivalenceInclusion_iff

end SphereSixComplex

/-! ## From `TopCat` retract data -/

namespace TopCat.StrongDeformationRetractData

variable {A' X : TopCat.{u}} {i : A' ⟶ X} (D : StrongDeformationRetractData i) {S : Set X}
  (hS : Set.range i.hom = S)

/-- Strong-deformation-retract data for `i : A' ⟶ X`, whose homotopy runs from `retraction ≫ i`
to the identity, gives a `SphereSixComplex.StrongDeformationRetraction` of `X` onto the range of
`i`, with the homotopy reversed.  Source: Hatcher, *Algebraic Topology*, p. 2 (definition of a
deformation retraction). -/
public def toStrongDeformationRetraction : SphereSixComplex.StrongDeformationRetraction X S where
  retract := i.hom.comp D.retraction.hom
  homotopy := D.homotopy.symm
  retract_mem _ := hS ▸ ⟨_, rfl⟩
  retract_fixed := hS ▸ Set.forall_mem_range.2 fun a ↦
    congrArg i.hom (CategoryTheory.ConcreteCategory.congr_hom D.retract a)
  homotopy_fixed t := hS ▸ Set.forall_mem_range.2 fun a ↦ D.fixed (σ t) a

/-- The retraction of `toStrongDeformationRetraction` is `i ∘ retraction`. -/
@[simp]
public theorem toStrongDeformationRetraction_retract_apply (x : X) :
    (D.toStrongDeformationRetraction hS).retract x = i (D.retraction x) :=
  rfl

/-- The homotopy of `toStrongDeformationRetraction` is the homotopy of `D` run backwards. -/
@[simp]
public theorem toStrongDeformationRetraction_homotopy_apply (t : I) (x : X) :
    (D.toStrongDeformationRetraction hS).homotopy (t, x) = D.homotopy (σ t, x) :=
  rfl

end TopCat.StrongDeformationRetractData

namespace SphereSixComplex

/-! ## Cofibrant homotopy-equivalent maps -/

/-- A map with the homotopy-extension property which is a homotopy equivalence exhibits its range
as a strong deformation retract: Hatcher's Corollary 0.20 for an arbitrary map, read off from
`HomotopyExtensionProperty.exists_strongDeformationRetractData` (`RelativeHomotopy.lean`).
Source: Hatcher, *Algebraic Topology*, Cor. 0.20 p. 16 via Prop. 0.19 pp. 16–17. -/
public theorem HomotopyExtensionProperty.nonempty_strongDeformationRetraction
    {A' X : Type u} [TopologicalSpace A'] [TopologicalSpace X] {i : C(A', X)}
    (hep : HomotopyExtensionProperty i) (hi : IsHomotopyEquivalence ⇑i)
    {S : Set X} (hS : Set.range i = S) : Nonempty (StrongDeformationRetraction X S) :=
  (hep.exists_strongDeformationRetractData hi).map fun D ↦ D.toStrongDeformationRetraction hS

/-! ## Lifting a strong deformation retraction through a covering -/

/-- The track through `e` of a base homotopy, lifted through a covering. -/
public noncomputable def liftTrack {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (cov : IsCoveringMap p) {D : Set B}
    (R : StrongDeformationRetraction B D) (e : E) : C(I, E) :=
  cov.liftPath ⟨fun s => R.homotopy (s, p e), by fun_prop⟩ e (by simp)

public theorem liftTrack_lifts {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (cov : IsCoveringMap p) {D : Set B}
    (R : StrongDeformationRetraction B D) (e : E) (s : I) :
    p (liftTrack cov R e s) = R.homotopy (s, p e) :=
  congrFun (cov.liftPath_lifts ⟨fun s => R.homotopy (s, p e), by fun_prop⟩ e (by simp)) s

public theorem liftTrack_zero {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (cov : IsCoveringMap p) {D : Set B}
    (R : StrongDeformationRetraction B D) (e : E) : liftTrack cov R e 0 = e :=
  cov.liftPath_zero _ e (by simp)

/-- The lifted homotopy is jointly continuous.  Continuity in each variable separately is what
`liftPath` provides; `IsLocalHomeomorph.continuous_lift` upgrades it. -/
public theorem continuous_liftTrack {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (cov : IsCoveringMap p) {D : Set B}
    (R : StrongDeformationRetraction B D) :
    Continuous (fun z : I × E => liftTrack cov R z.2 z.1) :=
  @IsLocalHomeomorph.continuous_lift E B E _ _ _ (⇑p) cov.isLocalHomeomorph cov.isSeparatedMap
    ⟨fun z : I × E => R.homotopy (z.1, p z.2), by fun_prop⟩
    (fun z => liftTrack cov R z.2 z.1)
    (by funext z; exact liftTrack_lifts cov R z.2 z.1)
    (by simpa only [liftTrack_zero] using continuous_id')
    (fun e => (liftTrack cov R e).continuous)

/-- A deck transformation does not change the image under the covering. -/
public theorem apply_smul_eq {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B]
    [MulAction G E] {p : C(E, B)} (hp : IsQuotientCoveringMap p G) (g : G) (e : E) :
    p (g • e) = p e :=
  hp.apply_eq_iff_mem_orbit.mpr ⟨g, rfl⟩

/-- Uniqueness of lifts: anything continuous that lifts the same track and starts at `e` is the
lifted track. -/
public theorem liftTrack_eq {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (cov : IsCoveringMap p) {D : Set B}
    (R : StrongDeformationRetraction B D) (e : E) (F : I → E)
    (hcont : Continuous F) (hlift : ∀ s, p (F s) = R.homotopy (s, p e)) (h0 : F 0 = e) :
    ∀ s, F s = liftTrack cov R e s := by
  have hg0 : (⟨fun s => R.homotopy (s, p e), by fun_prop⟩ : C(I, B)) 0 = p e := by simp
  have h := (cov.eq_liftPath_iff hg0 (Γ := F)).mpr ⟨hcont, funext hlift, h0⟩
  exact fun s => congrFun h s

/-- Over the base retract the track is constant, so its lift is too. -/
public theorem liftTrack_fixed {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (cov : IsCoveringMap p) {D : Set B}
    (R : StrongDeformationRetraction B D) {e : E} (he : p e ∈ D) (s : I) :
    liftTrack cov R e s = e :=
  (liftTrack_eq cov R e (fun _ => e) continuous_const
    (fun s => (R.homotopy_fixed s (p e) he).symm) rfl s).symm

/-- The lifted track is equivariant, again by uniqueness of lifts. -/
public theorem liftTrack_smul {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B]
    [MulAction G E] {p : C(E, B)} (hp : IsQuotientCoveringMap p G) {D : Set B}
    (R : StrongDeformationRetraction B D) (g : G) (e : E) (s : I) :
    liftTrack hp.isCoveringMap R (g • e) s = g • liftTrack hp.isCoveringMap R e s := by
  let _ := hp.toContinuousConstSMul
  refine (liftTrack_eq hp.isCoveringMap R (g • e) (fun s => g • liftTrack hp.isCoveringMap R e s)
    ((continuous_const_smul g).comp (liftTrack hp.isCoveringMap R e).continuous) ?_ ?_ s).symm
  · intro s
    rw [apply_smul_eq hp, liftTrack_lifts, apply_smul_eq hp]
  · rw [liftTrack_zero]

namespace EstablishedGeneralTopology

/-- **Uniqueness of `K(G, 1)` spaces for a relative CW pair.**  If both spaces of a relative CW
pair are aspherical and the subspace inclusion is an isomorphism on fundamental groups, then the
inclusion is a homotopy equivalence.

This is the Whitehead/compression step: the inclusion is a weak homotopy equivalence by the two
asphericity hypotheses together with the `π₁`-isomorphism, and a weak homotopy equivalence which
is the inclusion of the base of a relative CW complex is a deformation retract (Hatcher,
*Algebraic Topology*, Prop. 0.19 and Prop. 4.72 / Cor. 4.5).  Neither Mathlib nor Tau Ceti has
any homotopy theory of CW complexes, so this remains an axiom.

The `π₁` hypothesis is **not** removable, and no combination of the asphericity hypotheses
replaces it: let `B` be the solid torus `S¹ × D²` and `D` the embedded circle
`θ ↦ (e^{2iθ}, ½ e^{iθ})`.  Then `(B, D)` is a relative CW pair of two `K(ℤ, 1)` spaces, but the
inclusion is multiplication by `2` on `π₁` and is not a homotopy equivalence. -/
public axiom isHomotopyEquivalenceInclusion_of_isAspherical_of_bijective_fundamentalGroup
    {B : Type*} [TopologicalSpace B] (D : Set B) (b : B) (hb : b ∈ D)
    (hB : TauCeti.IsAspherical B b)
    (hD : TauCeti.IsAspherical D ⟨b, hb⟩)
    (hπ : Function.Bijective (FundamentalGroup.mapOfEq (topologicalSubsetInclusionMap D)
      (show (topologicalSubsetInclusionMap D) (⟨b, hb⟩ : D) = b from rfl)))
    (hCW : RelCWComplex (Set.univ : Set B) D) :
    IsHomotopyEquivalenceInclusion D

/-- If a regular covering and the full inverse image of a subspace are contractible, their
quotients are `K(G,1)` spaces. For a relative CW pair, the subspace inclusion is therefore a
homotopy equivalence.

All of the covering-space content is proved in `ContractibleRegularCoverInclusionProof`: the
higher homotopy groups of a contractible space vanish, a quotient covering map restricts to a
quotient covering map over the full preimage of a subspace with the same deck group, so `B` and
`D` are `K(G, 1)` spaces for one and the same `G`, and the two identifications of the fundamental
groups with the deck group are compatible with the inclusion, so the inclusion is a `π₁`
isomorphism.  Only the Whitehead step
`isHomotopyEquivalenceInclusion_of_isAspherical_of_bijective_fundamentalGroup` is assumed. -/
public theorem isHomotopyEquivalenceInclusion_of_contractible_regularCover
    {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B]
    [MulAction G E] (p : C(E, B)) (A : Set E) (D : Set B)
    (hp : IsQuotientCoveringMap p G) (hpreimage : p ⁻¹' D = A)
    (hE : ContractibleSpace E) (hA : ContractibleSpace A)
    (hCW : RelCWComplex (Set.univ : Set B) D) :
    IsHomotopyEquivalenceInclusion D :=
  isHomotopyEquivalenceInclusion_of_contractible_regularCover_of_whitehead p A D hp hpreimage
    hE hA hCW fun b hb hB hD hπ hCW' =>
      isHomotopyEquivalenceInclusion_of_isAspherical_of_bijective_fundamentalGroup
        D b hb hB hD hπ hCW'

/-- A cofibrant inclusion which is a homotopy equivalence is the inclusion of a strong
deformation retract. This is the standard homotopy-extension-property theorem (Hatcher,
*Algebraic Topology*, Cor. 0.20), obtained from
`HomotopyExtensionProperty.nonempty_strongDeformationRetraction` through the interface
translations `hasHomotopyExtensionProperty_iff` and `isHomotopyEquivalenceInclusion_iff`. -/
public theorem strongDeformationRetraction_of_cofibration_homotopyEquivalence
    {X : Type*} [TopologicalSpace X] (A : Set X)
    (hHEP : HasHomotopyExtensionProperty A)
    (hEquiv : IsHomotopyEquivalenceInclusion A) :
    Nonempty (StrongDeformationRetraction X A) :=
  hHEP.homotopyExtensionProperty.nonempty_strongDeformationRetraction hEquiv.isHomotopyEquivalence
    Subtype.range_coe

/-- Package the standard cofibration upgrade directly as a homotopy equivalence to the
subspace, retaining the literal inclusion as inverse. -/
public noncomputable def homotopyEquivOfCofibrationHomotopyEquivalence
    {X : Type*} [TopologicalSpace X] (A : Set X)
    (hHEP : HasHomotopyExtensionProperty A)
    (hEquiv : IsHomotopyEquivalenceInclusion A) : X ≃ₕ A :=
  (Classical.choice
    (strongDeformationRetraction_of_cofibration_homotopyEquivalence A hHEP hEquiv)).toHomotopyEquiv

/-- A strong deformation retraction lifts uniquely through a regular quotient covering. The
lift is equivariant under the deck group and retracts onto the full inverse image of the base
retract.

Proved from Mathlib's covering-space lifting API: each track is lifted by
`IsCoveringMap.liftPath`, joint continuity comes from `IsLocalHomeomorph.continuous_lift`, and both
the fixing on the preimage and the equivariance are uniqueness-of-lift arguments
(`IsCoveringMap.eq_liftPath_iff`). -/
public theorem equivariantStrongDeformationRetraction_lift
    {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B]
    [MulAction G E] (p : C(E, B)) (A : Set E) (D : Set B)
    (hp : IsQuotientCoveringMap p G) (hpreimage : p ⁻¹' D = A)
    (R : StrongDeformationRetraction B D) :
    Nonempty (EquivariantStrongDeformationRetraction G E A) := by
  let _ := hp.toContinuousConstSMul
  have hmemA : ∀ {x : E}, x ∈ A → p x ∈ D := fun {x} hx =>
    Set.mem_preimage.mp (by rw [hpreimage]; exact hx)
  exact ⟨{
    retract :=
      ⟨fun e => liftTrack hp.isCoveringMap R e 1,
        (continuous_liftTrack hp.isCoveringMap R).comp (continuous_const.prodMk continuous_id)⟩
    homotopy :=
      { toFun := fun z => liftTrack hp.isCoveringMap R z.2 z.1
        continuous_toFun := continuous_liftTrack hp.isCoveringMap R
        map_zero_left := fun e => liftTrack_zero hp.isCoveringMap R e
        map_one_left := fun _ => rfl }
    retract_mem := fun x => by
      have hD : p (liftTrack hp.isCoveringMap R x 1) ∈ D := by
        rw [liftTrack_lifts]; simpa using R.retract_mem (p x)
      rw [← hpreimage]; exact Set.mem_preimage.mpr hD
    retract_fixed := fun x hx => liftTrack_fixed hp.isCoveringMap R (hmemA hx) 1
    homotopy_fixed := fun s x hx => liftTrack_fixed hp.isCoveringMap R (hmemA hx) s
    retract_equivariant := fun g x => liftTrack_smul hp R g x 1
    homotopy_equivariant := fun g s x => liftTrack_smul hp R g x s }⟩

end EstablishedGeneralTopology

end SphereSixComplex
