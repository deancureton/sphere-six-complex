module

public import SphereSixComplex.Prerequisites.Topology.WangHomologyPresentation
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Algebra.Group.Subgroup.MulOppositeLemmas

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

/-- Pointwise equal continuous maps induce the same map on path homotopy classes, up to the
endpoint cast. -/
public theorem quotient_map_congr {A D : Type*} [TopologicalSpace A] [TopologicalSpace D]
    {a b : A} (Γ : Path.Homotopic.Quotient a b) (u v : C(A, D)) (h : ∀ z, u z = v z) :
    Γ.map u = (Γ.map v).cast (h a) (h b) := by
  induction Γ using Quotient.ind with
  | _ Γ =>
    apply Path.Homotopic.Quotient.eq.mpr
    refine ⟨?_⟩
    exact (Path.Homotopy.refl _).cast (by ext t; exact (h (Γ t)).symm) rfl

/-- Monodromy is natural along a map of covering spaces: transporting a lifted path by an
equivariant map gives the lift of the transported path. -/
public theorem monodromy_naturality
    {E E' X X' : Type*}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X] [TopologicalSpace X']
    {p : C(E, X)} {q : C(E', X')}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (lift : C(E, E')) (baseMap : C(X, X'))
    (commutes : ∀ z, baseMap (p z) = q (lift z))
    (e : E) (γ : FundamentalGroup X (p e)) :
    (hq.monodromy (FundamentalGroup.mapOfEq baseMap (commutes e) γ) ⟨lift e, rfl⟩ : E') =
      lift (hp.monodromy γ ⟨e, rfl⟩ : E) := by
  have hfib : q (lift ((hp.monodromy γ ⟨e, rfl⟩ : E))) = q (lift e) := by
    rw [← commutes, ← commutes]
    exact congrArg baseMap (hp.monodromy γ ⟨e, rfl⟩).2
  set ey : q ⁻¹' {q (lift e)} := ⟨lift ((hp.monodromy γ ⟨e, rfl⟩ : E)), hfib⟩ with hey
  have hmain :
      hq.monodromy (FundamentalGroup.mapOfEq baseMap (commutes e) γ) ⟨lift e, rfl⟩ = ey := by
    refine hq.monodromy_eq_of_map_eq ((hp.liftPathQuotient γ ⟨e, rfl⟩).map lift) ?_
    rw [← Path.Homotopic.Quotient.map_comp]
    rw [quotient_map_congr _ ((⟨q, hq.continuous⟩ : C(E', X')).comp lift)
      ((⟨baseMap, baseMap.continuous⟩ : C(X, X')).comp ⟨p, hp.continuous⟩)
      (fun z => (commutes z).symm)]
    rw [Path.Homotopic.Quotient.map_comp, hp.map_liftPathQuotient]
    simp only [FundamentalGroup.mapOfEq_apply]
    induction γ using Quotient.ind with
    | _ g => rfl
  rw [hmain]

/-- Equivariant maps of simply connected regular covers induce the corresponding deck-group
homomorphism under the standard fundamental-group equivalences.

Both sides are pinned down by their action on the chosen basepoint lift: Mathlib's
`fundamentalGroupToMulOpposite_apply_eq_Iff` says the equivalence sends `γ` to the unique group
element moving the lift along the monodromy of `γ`, and `monodromy_naturality` says the equivariant
map carries one monodromy to the other. -/
public theorem QuotientCoverMapData.fundamentalGroupEquiv_natural
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
        (FundamentalGroup.mapOfEq D.baseMap (D.commutes e) γ) := by
  symm
  refine (hq.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr ?_
  show D.deckMap ((hp.fundamentalGroupEquiv ⟨e, rfl⟩ γ).unop) • D.lift e = _
  rw [← D.equivariant]
  rw [show (hp.fundamentalGroupEquiv ⟨e, rfl⟩ γ).unop • e
      = (hp.isCoveringMap.monodromy γ ⟨e, rfl⟩ : E) from
    hp.unop_fundamentalGroupToMulOpposite_smul]
  exact (monodromy_naturality hp.isCoveringMap hq.isCoveringMap D.lift D.baseMap D.commutes
    e γ).symm

/-- Naturality with the target cover basepoint replaced by an equal selected lift. -/
public theorem QuotientCoverMapData.fundamentalGroupEquiv_natural_of_lift_eq
    {E E' X X' G H : Type*}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X] [TopologicalSpace X']
    [Group G] [Group H] [MulAction G E] [MulAction H E']
    [SimplyConnectedSpace E] [SimplyConnectedSpace E']
    {p : C(E, X)} {q : C(E', X')}
    (hp : IsQuotientCoveringMap p G) (hq : IsQuotientCoveringMap q H)
    (D : QuotientCoverMapData (G := G) (H := H) p q) (e : E) (e' : E')
    (he' : D.lift e = e') (γ : FundamentalGroup X (p e)) :
    (MonoidHom.op D.deckMap) (hp.fundamentalGroupEquiv ⟨e, rfl⟩ γ) =
      hq.fundamentalGroupEquiv ⟨e', rfl⟩
        (FundamentalGroup.mapOfEq D.baseMap
          ((D.commutes e).trans (congrArg q he')) γ) := by
  subst e'
  exact QuotientCoverMapData.fundamentalGroupEquiv_natural hp hq D e γ





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

section GroupTransport

open Subgroup MulOpposite

variable {A B₀ : Type*} [Group A] [Group B₀]

/-- The kernel of the opposite of a homomorphism is the opposite of its kernel. -/
public theorem ker_monoidHom_op (f : A →* B₀) : (MonoidHom.op f).ker = f.ker.op := by
  ext x
  simp [MonoidHom.mem_ker, Subgroup.mem_op]

/-- Normal closure commutes with passage to the opposite group. -/
public theorem op_normalClosure (S : Set A) :
    (normalClosure S).op = normalClosure (MulOpposite.op '' S) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : x.unop ∈ normalClosure S := hx
    have hle : normalClosure S ≤ (normalClosure (MulOpposite.op '' S)).unop := by
      refine normalClosure_le_normal ?_
      intro s hs
      exact subset_normalClosure ⟨s, hs, rfl⟩
    exact hle hx'
  · refine normalClosure_le_normal ?_
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_op).2 (subset_normalClosure hs)


end GroupTransport

/-! ## Transport of the induced map along the deck identifications -/

section CoverSquare

open Subgroup MulOpposite CategoryTheory

variable {E E' X X' G H : Type*}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X] [TopologicalSpace X']
  [Group G] [Group H] [MulAction G E] [MulAction H E']
  [SimplyConnectedSpace E] [SimplyConnectedSpace E']
  {p : C(E, X)} {q : C(E', X')}
  (hp : IsQuotientCoveringMap p G) (hq : IsQuotientCoveringMap q H)
  (cm : QuotientCoverMapData (G := G) (H := H) p q) (base : E)

/-- The `π₁` element attached to a deck transformation of the source cover. -/
public noncomputable def ofDeck (g : G) : FundamentalGroup X (p base) :=
  (hp.fundamentalGroupEquiv ⟨base, rfl⟩).symm (MulOpposite.op g)

@[simp]
public theorem fundamentalGroupEquiv_ofDeck (g : G) :
    hp.fundamentalGroupEquiv ⟨base, rfl⟩ (ofDeck hp base g) = MulOpposite.op g :=
  (hp.fundamentalGroupEquiv ⟨base, rfl⟩).apply_symm_apply _

public theorem ofDeck_mul_comm {g h : G} (hgh : g * h = h * g) :
    ofDeck hp base g * ofDeck hp base h = ofDeck hp base h * ofDeck hp base g := by
  apply (hp.fundamentalGroupEquiv ⟨base, rfl⟩).injective
  simp only [map_mul, fundamentalGroupEquiv_ofDeck, ← MulOpposite.op_mul, hgh]

/-- The basepoint-corrected induced map differs from the plain one by an isomorphism. -/
public noncomputable def basepointIso :
    FundamentalGroup X' (cm.baseMap (p base)) ≃* FundamentalGroup X' (q (cm.lift base)) :=
  (eqToIso (congr_arg FundamentalGroupoid.mk (cm.commutes base))).conj

public theorem mapOfEq_eq (γ : FundamentalGroup X (p base)) :
    FundamentalGroup.mapOfEq cm.baseMap (cm.commutes base) γ =
      basepointIso cm base (FundamentalGroup.map cm.baseMap (p base) γ) :=
  rfl

include hp hq in
/-- A surjective deck homomorphism induces a surjection on fundamental groups. -/
public theorem map_surjective_of_deckMap_surjective (hsurj : Function.Surjective cm.deckMap) :
    Function.Surjective (FundamentalGroup.map cm.baseMap (p base)) := by
  have hsurj' : Function.Surjective
      (FundamentalGroup.mapOfEq cm.baseMap (cm.commutes base)) := by
    intro y
    obtain ⟨g, hg⟩ := hsurj (hq.fundamentalGroupEquiv ⟨cm.lift base, rfl⟩ y).unop
    refine ⟨ofDeck hp base g, ?_⟩
    apply (hq.fundamentalGroupEquiv ⟨cm.lift base, rfl⟩).injective
    rw [← QuotientCoverMapData.fundamentalGroupEquiv_natural hp hq cm base]
    simp only [fundamentalGroupEquiv_ofDeck]
    exact MulOpposite.unop_injective (by simpa using hg)
  intro y
  obtain ⟨x, hx⟩ := hsurj' (basepointIso cm base y)
  refine ⟨x, ?_⟩
  apply (basepointIso cm base).injective
  rw [← mapOfEq_eq, hx]

include hq in
/-- The kernel of the induced map is the deck kernel, read through the identification. -/
public theorem ker_map_of_deckMap_ker (S : Set G) (hker : cm.deckMap.ker = normalClosure S) :
    (FundamentalGroup.map cm.baseMap (p base)).ker = normalClosure (ofDeck hp base '' S) := by
  have hkerEq : (FundamentalGroup.map cm.baseMap (p base)).ker =
      (FundamentalGroup.mapOfEq cm.baseMap (cm.commutes base)).ker := by
    ext x
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h
      rw [mapOfEq_eq, h, map_one]
    · intro h
      refine (basepointIso cm base).injective ?_
      rw [map_one, ← mapOfEq_eq]
      exact h
  rw [hkerEq]
  have hcomap : (FundamentalGroup.mapOfEq cm.baseMap (cm.commutes base)).ker =
      Subgroup.comap ((hp.fundamentalGroupEquiv ⟨base, rfl⟩ : _ →* Gᵐᵒᵖ))
        ((MonoidHom.op cm.deckMap).ker) := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap]
    constructor
    · intro h
      show (MonoidHom.op cm.deckMap) (hp.fundamentalGroupEquiv ⟨base, rfl⟩ x) = 1
      rw [QuotientCoverMapData.fundamentalGroupEquiv_natural hp hq cm base, h, map_one]
    · intro h
      have h' : (MonoidHom.op cm.deckMap) (hp.fundamentalGroupEquiv ⟨base, rfl⟩ x) = 1 := h
      rw [QuotientCoverMapData.fundamentalGroupEquiv_natural hp hq cm base] at h'
      refine (hq.fundamentalGroupEquiv ⟨cm.lift base, rfl⟩).injective ?_
      rw [map_one]
      exact h'
  rw [hcomap, ker_monoidHom_op, hker, op_normalClosure,
    ← Subgroup.comap_normalClosure _ (hp.fundamentalGroupEquiv ⟨base, rfl⟩)]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    refine (hp.fundamentalGroupEquiv ⟨base, rfl⟩).injective ?_
    rw [fundamentalGroupEquiv_ofDeck, hx]
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, by rw [fundamentalGroupEquiv_ofDeck]⟩

public theorem ofDeck_mul (g h : G) :
    ofDeck hp base (g * h) = ofDeck hp base h * ofDeck hp base g := by
  apply (hp.fundamentalGroupEquiv ⟨base, rfl⟩).injective
  rw [map_mul, fundamentalGroupEquiv_ofDeck, fundamentalGroupEquiv_ofDeck,
    fundamentalGroupEquiv_ofDeck, ← MulOpposite.op_mul]

@[simp]
public theorem ofDeck_one : ofDeck hp base (1 : G) = 1 := by
  apply (hp.fundamentalGroupEquiv ⟨base, rfl⟩).injective
  rw [fundamentalGroupEquiv_ofDeck, map_one, MulOpposite.op_one]

public theorem ofDeck_inv (g : G) : ofDeck hp base g⁻¹ = (ofDeck hp base g)⁻¹ := by
  apply (hp.fundamentalGroupEquiv ⟨base, rfl⟩).injective
  rw [fundamentalGroupEquiv_ofDeck, map_inv, fundamentalGroupEquiv_ofDeck, ← MulOpposite.op_inv]

public theorem ofDeck_pow (g : G) (n : ℕ) : ofDeck hp base (g ^ n) = (ofDeck hp base g) ^ n := by
  apply (hp.fundamentalGroupEquiv ⟨base, rfl⟩).injective
  rw [fundamentalGroupEquiv_ofDeck, map_pow, fundamentalGroupEquiv_ofDeck, ← MulOpposite.op_pow]

end CoverSquare

open Subgroup in
/-- Normal closures of `a * b` and `b * a` agree. -/
public theorem normalClosure_singleton_mul_comm {A : Type*} [Group A] (a b : A) :
    normalClosure ({a * b} : Set A) = normalClosure ({b * a} : Set A) := by
  refine le_antisymm (normalClosure_le_normal ?_) (normalClosure_le_normal ?_)
  · rintro x rfl
    have hmem : b * a ∈ normalClosure ({b * a} : Set A) := subset_normalClosure rfl
    have hconj := (normalClosure_normal (s := ({b * a} : Set A))).conj_mem _ hmem a
    have heq : a * (b * a) * a⁻¹ = a * b := by group
    rwa [heq] at hconj
  · rintro x rfl
    have hmem : a * b ∈ normalClosure ({a * b} : Set A) := subset_normalClosure rfl
    have hconj := (normalClosure_normal (s := ({a * b} : Set A))).conj_mem _ hmem b
    have heq : b * (a * b) * b⁻¹ = b * a := by group
    rwa [heq] at hconj

/-! ## The toric filling -/

namespace ToricFillingCoverModel

open Subgroup MulOpposite

variable {Λ K : Type*} [AddCommGroup Λ] [AddCommGroup K]
variable {G H E E' B N : Type*} [Group G] [Group H]
variable [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] [TopologicalSpace N]
variable [MulAction G E] [MulAction H E']
variable (D : ToricFillingCoverModel Λ K G H E E' B N)

/-- The lattice of boundary translations, as fundamental-group elements. -/
public noncomputable def piOneTranslation :
    Λ →+ Additive (FundamentalGroup B (D.boundaryProjection D.base)) := by
  let _ : SimplyConnectedSpace E := D.boundarySimplyConnected
  exact
    { toFun := fun a ↦
        Additive.ofMul (ofDeck D.boundaryQuotient D.base (Additive.toMul (D.deckTranslation a)))
      map_zero' := by simp
      map_add' := fun a b ↦ by
        have hab : D.deckTranslation (a + b) = D.deckTranslation a + D.deckTranslation b :=
          map_add _ _ _
        have hmul : Additive.toMul (D.deckTranslation (a + b))
            = Additive.toMul (D.deckTranslation a) * Additive.toMul (D.deckTranslation b) := by
          rw [hab]
          rfl
        have hmul' : Additive.toMul (D.deckTranslation (b + a))
            = Additive.toMul (D.deckTranslation b) * Additive.toMul (D.deckTranslation a) := by
          rw [map_add]
          rfl
        have hcomm : Additive.toMul (D.deckTranslation b) * Additive.toMul (D.deckTranslation a)
            = Additive.toMul (D.deckTranslation a) * Additive.toMul (D.deckTranslation b) := by
          rw [← hmul', ← hmul, add_comm b a]
        show Additive.ofMul (ofDeck D.boundaryQuotient D.base
            (Additive.toMul (D.deckTranslation (a + b)))) = _
        rw [hmul, ofDeck_mul]
        exact congrArg Additive.ofMul
          (ofDeck_mul_comm D.boundaryQuotient D.base hcomm) }

/-- The toric filling `π₁` package, derived from the deck-group presentation. -/
public noncomputable def toPiOneData : ToricFillingPiOneData D := by
  let _ : SimplyConnectedSpace E := D.boundarySimplyConnected
  let _ : SimplyConnectedSpace E' := D.fillingSimplyConnected
  refine
    { translation := D.piOneTranslation
      meridian := ofDeck D.boundaryQuotient D.base D.deckMeridian
      translation_deck := fun a ↦ ?_
      meridian_deck := ?_
      map_surjective := ?_
      ker_map := ?_ }
  · exact fundamentalGroupEquiv_ofDeck D.boundaryQuotient D.base _
  · exact fundamentalGroupEquiv_ofDeck D.boundaryQuotient D.base _
  · exact map_surjective_of_deckMap_surjective D.boundaryQuotient D.fillingQuotient
      D.coverMap D.base D.deckMap_surjective
  · rw [ker_map_of_deckMap_ker D.boundaryQuotient D.fillingQuotient D.coverMap D.base
      (Set.range (fun k ↦ Additive.toMul (D.deckTranslation (D.vanishing k))) ∪ {D.deckMeridian})
      D.deckMap_kernel]
    congr 1
    rw [Set.image_union, Set.image_singleton, ← Set.range_comp]
    rfl

end ToricFillingCoverModel

/-- The standard toric-filling computation obtained from an equivariant regular-cover square. -/
public noncomputable def toricFillingPiOneData
    {Λ K G H E E' B N : Type*}
    [AddCommGroup Λ] [AddCommGroup K] [Group G] [Group H]
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] [TopologicalSpace N]
    [MulAction G E] [MulAction H E']
    (D : ToricFillingCoverModel Λ K G H E E' B N) :
    ToricFillingPiOneData D :=
  D.toPiOneData

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
  deck_conjugate : ∀ a,
    deckMeridian * Additive.toMul (deckTranslation a) * deckMeridian⁻¹ =
      Additive.toMul (deckTranslation (monodromy.toAdd a))
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

/-! ## The cyclic affine filling -/

namespace CyclicAffineFillingCoverModel

open Subgroup MulOpposite

variable {m : ℕ} {Λ : Type*} [NeZero m] [AddCommGroup Λ]
variable {G H E E' B N : Type*} [Group G] [Group H]
variable [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] [TopologicalSpace N]
variable [MulAction G E] [MulAction H E']
variable (D : CyclicAffineFillingCoverModel m Λ G H E E' B N)

/-- The lattice of boundary translations, as fundamental-group elements. -/
public noncomputable def piOneTranslation :
    Λ →+ Additive (FundamentalGroup B (D.boundaryProjection D.base)) := by
  let _ : SimplyConnectedSpace E := D.boundarySimplyConnected
  exact
    { toFun := fun a ↦
        Additive.ofMul (ofDeck D.boundaryQuotient D.base (Additive.toMul (D.deckTranslation a)))
      map_zero' := by simp
      map_add' := fun a b ↦ by
        have hmul : Additive.toMul (D.deckTranslation (a + b))
            = Additive.toMul (D.deckTranslation a) * Additive.toMul (D.deckTranslation b) := by
          rw [map_add]
          rfl
        have hmul' : Additive.toMul (D.deckTranslation (b + a))
            = Additive.toMul (D.deckTranslation b) * Additive.toMul (D.deckTranslation a) := by
          rw [map_add]
          rfl
        have hcomm : Additive.toMul (D.deckTranslation b) * Additive.toMul (D.deckTranslation a)
            = Additive.toMul (D.deckTranslation a) * Additive.toMul (D.deckTranslation b) := by
          rw [← hmul', ← hmul, add_comm b a]
        show Additive.ofMul (ofDeck D.boundaryQuotient D.base
            (Additive.toMul (D.deckTranslation (a + b)))) = _
        rw [hmul, ofDeck_mul]
        exact congrArg Additive.ofMul
          (ofDeck_mul_comm D.boundaryQuotient D.base hcomm) }

/-- The cyclic affine filling `π₁` package, derived from the deck-group presentation. -/
public noncomputable def toPiOneData : CyclicAffineFillingPiOneData D := by
  let _ : SimplyConnectedSpace E := D.boundarySimplyConnected
  let _ : SimplyConnectedSpace E' := D.fillingSimplyConnected
  refine
    { translation := D.piOneTranslation
      meridian := ofDeck D.boundaryQuotient D.base D.deckMeridian
      translation_deck := fun a ↦ ?_
      meridian_deck := ?_
      map_surjective := ?_
      ker_map := ?_ }
  · exact fundamentalGroupEquiv_ofDeck D.boundaryQuotient D.base _
  · exact fundamentalGroupEquiv_ofDeck D.boundaryQuotient D.base _
  · exact map_surjective_of_deckMap_surjective D.boundaryQuotient D.fillingQuotient
      D.coverMap D.base D.deckMap_surjective
  · rw [ker_map_of_deckMap_ker D.boundaryQuotient D.fillingQuotient D.coverMap D.base
      {D.deckMeridian ^ m * (Additive.toMul (D.deckTranslation D.twist))⁻¹} D.deckMap_kernel,
      Set.image_singleton, ofDeck_mul, ofDeck_inv, ofDeck_pow]
    exact normalClosure_singleton_mul_comm _ _


end CyclicAffineFillingCoverModel

/-- The standard cyclic-affine-filling computation from an equivariant regular-cover square. -/
public noncomputable def cyclicAffineFillingPiOneData
    {m : ℕ} {Λ G H E E' B N : Type*}
    [NeZero m] [AddCommGroup Λ] [Group G] [Group H]
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] [TopologicalSpace N]
    [MulAction G E] [MulAction H E']
    (D : CyclicAffineFillingCoverModel m Λ G H E E' B N) :
    CyclicAffineFillingPiOneData D :=
  D.toPiOneData

end SphereSixComplex

end
