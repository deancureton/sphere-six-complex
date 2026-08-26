module

public import SphereSixComplex.Topology.EstablishedStrongDeformationRetractsDefs
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.CWComplex.Classical.Basic
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Covering
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Contractible regular covers and `K(G, 1)` quotients

This file develops the covering-theoretic content of the axiom
`EstablishedGeneralTopology.isHomotopyEquivalenceInclusion_of_contractible_regularCover`:
a regular covering `p : E → B` with deck group `G` and contractible total space, together with
a subspace `D ⊆ B` whose full preimage `A = p ⁻¹' D` is contractible.

## Main results

* `subsingleton_homotopyGroup_of_contractibleSpace`: every homotopy group of a contractible
  space is trivial.  Proved by transporting a generalized loop along the contraction, using the
  Tau Ceti base-point-change machinery (`TauCeti.GenLoop.HomotopyAlong`).
* `isQuotientCoveringMap_preimageRestrict`: a quotient covering map restricts, over the full
  preimage of a subspace, to a quotient covering map with the same deck group.
* `isEilenbergMacLaneSpaceOne_of_contractibleSpace` and
  `isEilenbergMacLaneSpaceOne_preimageRestrict`: `B` and `D` are `K(G, 1)` spaces for one and
  the same group `G`, packaged in `isEilenbergMacLaneSpaceOne_of_contractible_regularCover`.
* `fundamentalGroupToMulOpposite_preimageRestrict`: the two identifications of the fundamental
  groups with the deck group are compatible with the inclusion `D ⊆ B`, because a lift inside
  `A` of a loop of `D` is a lift inside `E` of the same loop viewed in `B`.
* `bijective_fundamentalGroup_mapOfEq_of_contractible_regularCover`: **the inclusion `D ⊆ B`
  induces an isomorphism on fundamental groups.**
* `isHomotopyEquivalenceInclusion_of_contractible_regularCover_of_whitehead`: the axiom follows
  from the classical uniqueness of `K(G, 1)` spaces (a Whitehead-type principle for relative CW
  pairs), which is the only remaining input and is available neither in Mathlib nor in Tau Ceti.
-/

@[expose] public section

noncomputable section

open scoped Topology Topology.Homotopy unitInterval

namespace SphereSixComplex

/-- Every homotopy group of a contractible space is trivial. -/
public theorem subsingleton_homotopyGroup_of_contractibleSpace
    {N X : Type*} [Fintype N] [TopologicalSpace X] [ContractibleSpace X] (x : X) :
    Subsingleton (HomotopyGroup N X x) := by
  obtain ⟨x₀, hx₀⟩ := id_nullhomotopic X
  obtain ⟨H⟩ := hx₀
  let γ : Path x x₀ :=
    ⟨⟨fun t => H (t, x), by fun_prop⟩, H.apply_zero x, H.apply_one x⟩
  have key : ∀ f : Ω^ N X x,
      (⟦TauCeti.GenLoop.transport γ f⟧ : HomotopyGroup N X x₀) = ⟦GenLoop.const⟧ := by
    intro f
    refine (Quotient.sound ?_).symm
    refine TauCeti.GenLoop.HomotopyAlong.homotopic_transport
      (γ := γ) (f := f) (g := GenLoop.const) ?_
    refine
      { toFun := fun tz => H (tz.1, (f : C(I^N, X)) tz.2)
        continuous_toFun := by fun_prop
        map_zero_left := ?_
        map_one_left := ?_
        map_boundary := ?_ }
    · intro z
      simp
    · intro z
      simp
    · intro t z hz
      show H (t, (f : C(I^N, X)) z) = H (t, x)
      rw [f.2 z hz]
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b fun f f' => ?_
  refine (TauCeti.homotopyGroupEquivOfPath γ).injective ?_
  rw [TauCeti.homotopyGroupEquivOfPath_mk, TauCeti.homotopyGroupEquivOfPath_mk, key f, key f']

/-! ## Restricting a quotient covering map to the preimage of a subspace -/

/-- The restriction of a map to the full preimage of a subspace, as a map into that subspace. -/
public def preimageRestrict {E B : Type*} (p : E → B) (D : Set B) :
    (p ⁻¹' D : Set E) → D := fun a => ⟨p a, a.2⟩

section Restrict

variable {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B] [MulAction G E]
  {p : E → B}

/-- The full preimage of a subspace under a quotient covering map is invariant, so the deck
group acts on it. -/
@[instance_reducible] public def quotientCoveringPreimageMulAction
    (hp : IsQuotientCoveringMap p G) (D : Set B) :
    MulAction G (p ⁻¹' D : Set E) :=
  SubMulAction.mulAction
    ⟨p ⁻¹' D, fun g _ h => by simpa only [Set.mem_preimage, hp.map_smul g] using h⟩

/-- **A quotient covering map restricts to a quotient covering map over any subspace**, with the
same deck group, on the full preimage of that subspace. -/
public theorem isQuotientCoveringMap_preimageRestrict
    (hp : IsQuotientCoveringMap p G) (D : Set B) :
    letI := quotientCoveringPreimageMulAction hp D
    IsQuotientCoveringMap (preimageRestrict p D) G := by
  let := quotientCoveringPreimageMulAction hp D
  let := hp.toContinuousConstSMul
  have hcoe_smul : ∀ (g : G) (a : (p ⁻¹' D : Set E)),
      ((g • a : (p ⁻¹' D : Set E)) : E) = g • (a : E) := fun _ _ => rfl
  have hcont : Continuous (preimageRestrict p D) :=
    (hp.continuous.comp continuous_subtype_val).subtype_mk _
  have hsurj : Function.Surjective (preimageRestrict p D) := by
    intro b
    obtain ⟨e, he⟩ := hp.surjective (b : B)
    exact ⟨⟨e, by rw [Set.mem_preimage, he]; exact b.2⟩, Subtype.ext he⟩
  have hopen : IsOpenMap (preimageRestrict p D) := by
    intro U hU
    rw [isOpen_induced_iff] at hU
    obtain ⟨V, hV, rfl⟩ := hU
    rw [isOpen_induced_iff]
    refine ⟨p '' V, hp.isCoveringMap.isLocalHomeomorph.isOpenMap V hV, ?_⟩
    ext b
    constructor
    · rintro ⟨v, hv, hpv⟩
      exact ⟨⟨v, by rw [Set.mem_preimage, hpv]; exact b.2⟩, hv, Subtype.ext hpv⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a : E), ha, rfl⟩
  refine
    { toIsQuotientMap := hopen.isQuotientMap hcont hsurj
      continuous_const_smul := fun g =>
        (((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _)
      apply_eq_iff_mem_orbit := ?_
      disjoint := ?_ }
  · intro a₁ a₂
    constructor
    · intro h
      obtain ⟨g, hg⟩ := hp.apply_eq_iff_mem_orbit.mp (congrArg Subtype.val h)
      exact ⟨g, Subtype.ext hg⟩
    · rintro ⟨g, rfl⟩
      exact Subtype.ext (by simpa only [preimageRestrict, hcoe_smul] using hp.map_smul g)
  · intro a
    obtain ⟨U, hU, hU'⟩ := hp.disjoint (a : E)
    refine ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩
    rintro g ⟨b, ⟨c, hc, rfl⟩, hb⟩
    exact hU' g
      ⟨((g • c : (p ⁻¹' D : Set E)) : E), ⟨(c : E), hc, (hcoe_smul g c).symm⟩, hb⟩

end Restrict

/-! ## The two `K(G, 1)` quotients -/

/-- **The orbit space of a free, properly discontinuous action of `G` on a contractible space is
a `K(G, 1)`.**  This is `IsQuotientCoveringMap.isEilenbergMacLaneSpaceOne` of the Tau Ceti
library, fed with the vanishing of the higher homotopy groups of a contractible space. -/
public theorem isEilenbergMacLaneSpaceOne_of_contractibleSpace
    {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B] [MulAction G E]
    {p : E → B} (hp : IsQuotientCoveringMap p G) [ContractibleSpace E] (e : E) :
    TauCeti.IsEilenbergMacLaneSpaceOne G B (p e) :=
  hp.isEilenbergMacLaneSpaceOne rfl fun _ =>
    subsingleton_homotopyGroup_of_contractibleSpace e

/-- **A subspace whose full preimage under a contractible regular cover is contractible is a
`K(G, 1)` for the same group `G`.** -/
public theorem isEilenbergMacLaneSpaceOne_preimageRestrict
    {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B] [MulAction G E]
    {p : E → B} (hp : IsQuotientCoveringMap p G) (D : Set B)
    [ContractibleSpace (p ⁻¹' D : Set E)] (a : (p ⁻¹' D : Set E)) :
    TauCeti.IsEilenbergMacLaneSpaceOne G D (preimageRestrict p D a) :=
  let _ := quotientCoveringPreimageMulAction hp D
  isEilenbergMacLaneSpaceOne_of_contractibleSpace
    (isQuotientCoveringMap_preimageRestrict hp D) a

/-- **The `K(G, 1)` half of `isHomotopyEquivalenceInclusion_of_contractible_regularCover`**: in
the situation of that statement both the base `B` and the subspace `D` are `K(G, 1)` spaces for
one and the same group `G`, based at the image of any point of `A`. -/
public theorem isEilenbergMacLaneSpaceOne_of_contractible_regularCover
    {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B]
    [MulAction G E] (p : C(E, B)) (A : Set E) (D : Set B)
    (hp : IsQuotientCoveringMap p G) (hpreimage : p ⁻¹' D = A)
    (hE : ContractibleSpace E) (hA : ContractibleSpace A) (a : A) :
    TauCeti.IsEilenbergMacLaneSpaceOne G B (p (a : E)) ∧
      ∀ h : p (a : E) ∈ D,
        TauCeti.IsEilenbergMacLaneSpaceOne G D ⟨p (a : E), h⟩ := by
  subst hpreimage
  refine ⟨isEilenbergMacLaneSpaceOne_of_contractibleSpace hp _, fun h => ?_⟩
  exact isEilenbergMacLaneSpaceOne_preimageRestrict hp D a



/-! ## The subspace inclusion is an isomorphism on fundamental groups -/

section FundamentalGroup

variable {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B] [MulAction G E]
  {p : E → B}

/-- The two deck-group identifications of the fundamental groups of `B` and of `D` agree with
the map induced by the inclusion `D ⊆ B`: a lift of a loop of `D` inside the preimage `A` is a
lift of the same loop, viewed in `B`, inside `E`. -/
public theorem fundamentalGroupToMulOpposite_preimageRestrict
    (hp : IsQuotientCoveringMap p G) (D : Set B) (a : (p ⁻¹' D : Set E))
    (γ : FundamentalGroup D (preimageRestrict p D a)) :
    letI := quotientCoveringPreimageMulAction hp D
    hp.fundamentalGroupToMulOpposite (x := p (a : E))
        ⟨(a : E), Set.mem_preimage.mpr (Set.mem_singleton _)⟩
        (FundamentalGroup.mapOfEq (topologicalSubsetInclusionMap D)
          (show (topologicalSubsetInclusionMap D) (preimageRestrict p D a) = p (a : E) from rfl)
          γ) =
      (isQuotientCoveringMap_preimageRestrict hp D).fundamentalGroupToMulOpposite
        ⟨a, Set.mem_preimage.mpr (Set.mem_singleton _)⟩ γ := by
  let := quotientCoveringPreimageMulAction hp D
  set hpA := isQuotientCoveringMap_preimageRestrict hp D with hpA_def
  set aA : (preimageRestrict p D) ⁻¹' {preimageRestrict p D a} :=
    ⟨a, Set.mem_preimage.mpr (Set.mem_singleton _)⟩ with haA
  set eE : p ⁻¹' {p (a : E)} :=
    ⟨(a : E), Set.mem_preimage.mpr (Set.mem_singleton _)⟩ with heE
  set iD := topologicalSubsetInclusionMap D with hiD
  set iA := topologicalSubsetInclusionMap (p ⁻¹' D) with hiA
  have hiDγ : iD (preimageRestrict p D a) = p (a : E) := rfl
  refine (hp.fundamentalGroupToMulOpposite_apply_eq_Iff (e := eE)).mpr ?_
  have hcomp :
      (⟨p, hp.continuous⟩ : C(E, B)).comp iA =
        iD.comp (⟨preimageRestrict p D, hpA.isCoveringMap.continuous⟩ :
          C((p ⁻¹' D : Set E), D)) := by
    ext x
    rfl
  have hm : preimageRestrict p D
      ((hpA.isCoveringMap.monodromy γ aA : (p ⁻¹' D : Set E))) = preimageRestrict p D a :=
    Set.mem_singleton_iff.mp (Set.mem_preimage.mp (hpA.isCoveringMap.monodromy γ aA).2)
  have hmE : ((hpA.isCoveringMap.monodromy γ aA : (p ⁻¹' D : Set E)) : E) ∈
      p ⁻¹' {p (a : E)} :=
    Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (congrArg Subtype.val hm))
  have hx : (eE : E) = iA (aA : (p ⁻¹' D : Set E)) := rfl
  have hy : ((hpA.isCoveringMap.monodromy γ aA : (p ⁻¹' D : Set E)) : E) =
      iA (hpA.isCoveringMap.monodromy γ aA : (p ⁻¹' D : Set E)) := rfl
  have hmono : hp.isCoveringMap.monodromy
      (FundamentalGroup.mapOfEq iD hiDγ γ) eE =
      ⟨((hpA.isCoveringMap.monodromy γ aA : (p ⁻¹' D : Set E)) : E), hmE⟩ := by
    refine hp.isCoveringMap.monodromy_eq_of_map_eq
      (((hpA.isCoveringMap.liftPathQuotient γ aA).map iA).cast hx hy) ?_
    have hstep : (hpA.isCoveringMap.liftPathQuotient γ aA).map
          ((⟨p, hp.continuous⟩ : C(E, B)).comp iA) =
        (hpA.isCoveringMap.liftPathQuotient γ aA).map
          (iD.comp (⟨preimageRestrict p D, hpA.isCoveringMap.continuous⟩ :
            C((p ⁻¹' D : Set E), D))) := rfl
    rw [Path.Homotopic.Quotient.map_cast, ← Path.Homotopic.Quotient.map_comp, hstep,
      Path.Homotopic.Quotient.map_comp, hpA.isCoveringMap.map_liftPathQuotient]
    simp only [FundamentalGroup.mapOfEq_apply]
    induction (γ : Path.Homotopic.Quotient (preimageRestrict p D a) (preimageRestrict p D a))
      using Quotient.ind with
    | _ P => rfl
  rw [hmono]
  exact congrArg Subtype.val hpA.unop_fundamentalGroupToMulOpposite_smul

/-- **The inclusion of the subspace induces an isomorphism on fundamental groups.**  Both
fundamental groups are identified with the deck group `G`, compatibly with the inclusion by
`fundamentalGroupToMulOpposite_preimageRestrict`, so the inclusion is a bijection on `π₁`. -/
public theorem bijective_fundamentalGroup_mapOfEq_of_contractible_regularCover
    (hp : IsQuotientCoveringMap p G) (D : Set B)
    [ContractibleSpace E] [ContractibleSpace (p ⁻¹' D : Set E)]
    (a : (p ⁻¹' D : Set E)) :
    Function.Bijective (FundamentalGroup.mapOfEq (topologicalSubsetInclusionMap D)
      (show (topologicalSubsetInclusionMap D) (preimageRestrict p D a) = p (a : E) from rfl)) := by
  let := quotientCoveringPreimageMulAction hp D
  set hpA := isQuotientCoveringMap_preimageRestrict hp D with hpA_def
  have key := fundamentalGroupToMulOpposite_preimageRestrict hp D a
  have hBinj := hp.fundamentalGroupToMulOpposite_injective
    (⟨(a : E), Set.mem_preimage.mpr (Set.mem_singleton _)⟩ : p ⁻¹' {p (a : E)})
  have hAinj := hpA.fundamentalGroupToMulOpposite_injective
    (⟨a, Set.mem_preimage.mpr (Set.mem_singleton _)⟩ :
      preimageRestrict p D ⁻¹' {preimageRestrict p D a})
  have hAsurj := hpA.fundamentalGroupToMulOpposite_surjective
    (⟨a, Set.mem_preimage.mpr (Set.mem_singleton _)⟩ :
      preimageRestrict p D ⁻¹' {preimageRestrict p D a})
  refine ⟨fun γ γ' h => hAinj ?_, fun δ => ?_⟩
  · rw [← key γ, ← key γ', h]
  · obtain ⟨γ, hγ⟩ := hAsurj (hp.fundamentalGroupToMulOpposite
      (⟨(a : E), Set.mem_preimage.mpr (Set.mem_singleton _)⟩ : p ⁻¹' {p (a : E)}) δ)
    exact ⟨γ, hBinj ((key γ).trans hγ)⟩


/-! ## Reduction of the target statement to a Whitehead-type principle -/

/-- **Reduction of `isHomotopyEquivalenceInclusion_of_contractible_regularCover` to a
Whitehead-type principle.**

Everything about the covering has been discharged: for a contractible regular cover `p` with
contractible full preimage `A = p ⁻¹' D`, both `B` and `D` are aspherical and the inclusion
`D ⊆ B` induces an isomorphism on fundamental groups.  What is left is exactly the classical
uniqueness of `K(G, 1)` spaces: *a relative CW pair whose two spaces are aspherical and whose
inclusion is an isomorphism on `π₁` has a homotopy-equivalent inclusion.*

The `π₁` hypothesis cannot be dropped: `D` a circle winding twice around the core of the solid
torus `B` is a relative CW pair of two `K(ℤ, 1)`s whose inclusion is not a homotopy
equivalence. -/
public theorem isHomotopyEquivalenceInclusion_of_contractible_regularCover_of_whitehead
    {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B] [MulAction G E]
    (p : C(E, B)) (A : Set E) (D : Set B)
    (hp : IsQuotientCoveringMap p G) (hpreimage : p ⁻¹' D = A)
    (hE : ContractibleSpace E) (hA : ContractibleSpace A)
    (hCW : Topology.RelCWComplex (Set.univ : Set B) D)
    (whitehead : ∀ (b : B) (hb : b ∈ D), TauCeti.IsAspherical B b →
      TauCeti.IsAspherical D ⟨b, hb⟩ →
      Function.Bijective (FundamentalGroup.mapOfEq (topologicalSubsetInclusionMap D)
        (show (topologicalSubsetInclusionMap D) (⟨b, hb⟩ : D) = b from rfl)) →
      Topology.RelCWComplex (Set.univ : Set B) D → IsHomotopyEquivalenceInclusion D) :
    IsHomotopyEquivalenceInclusion D := by
  subst hpreimage
  obtain ⟨a⟩ : Nonempty (p ⁻¹' D : Set E) := inferInstance
  exact whitehead (p (a : E)) a.2
    (isEilenbergMacLaneSpaceOne_of_contractibleSpace hp (a : E)).isAspherical
    (isEilenbergMacLaneSpaceOne_preimageRestrict hp D a).isAspherical
    (bijective_fundamentalGroup_mapOfEq_of_contractible_regularCover hp D a) hCW


end FundamentalGroup


end SphereSixComplex

end

end
