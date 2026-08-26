module

public import SphereSixComplex.Topology.EstablishedEquivariantUniversalCoverDefs
public import TauCeti.AlgebraicTopology.UniversalCover.Action
public import TauCeti.AlgebraicTopology.UniversalCover.Covering

/-!
# Reducing the equivariant universal cover to a fundamental-group identification

The equivariant universal-cover classification for the punctured global family asserts the
existence of a simply connected space with a free properly discontinuous action of the affine
deck group `Λ ⋊ FreeGroup (Fin 2)` whose quotient is the punctured global family.  A simply
connected quotient covering already forces the fundamental group of the base to be the acting
group, so the group-theoretic identification is the whole geometric content of that assertion.
This file proves the converse direction: from such an identification, together with the local
niceness the based-path universal cover needs, the classification is constructed outright,
leaving no covering-space existence step implicit.  `EstablishedEquivariantUniversalCover` then
retains only the identification as its input.

The construction is TauCeti's based-path universal cover, whose fundamental-group action is
already known to be a quotient covering map, transported along the given group isomorphism.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex

section Transport

set_option linter.style.haveILetI false in
/-- A quotient covering map for one group is a quotient covering map for any isomorphic group,
acting through the isomorphism. -/
public theorem isQuotientCoveringMap_compHom
    {E X G H : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Group G] [Group H] [MulAction H E] {f : E → X}
    (hf : IsQuotientCoveringMap f H) (e : G ≃* H) :
    letI := MulAction.compHom E (e : G →* H)
    IsQuotientCoveringMap f G := by
  letI := MulAction.compHom E (e : G →* H)
  have hsmul : ∀ (g : G) (x : E), g • x = e g • x := fun _ _ ↦ rfl
  refine ⟨hf.toIsQuotientMap, ⟨fun g ↦ ?_⟩, ?_, ?_⟩
  · simpa only [hsmul] using hf.continuous_const_smul (e g)
  · intro e₁ e₂
    rw [hf.apply_eq_iff_mem_orbit]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨e.symm h, ?_⟩
      show e.symm h • e₂ = h • e₂
      rw [hsmul, e.apply_symm_apply]
    · rintro ⟨g, rfl⟩
      exact ⟨e g, rfl⟩
  · intro x
    obtain ⟨U, hU, hU'⟩ := hf.disjoint x
    refine ⟨U, hU, fun g hg ↦ ?_⟩
    have hone : e g = 1 := hU' (e g) (by simpa only [hsmul] using hg)
    simpa using congrArg e.symm hone

end Transport

section AffineCoverOfFundamentalGroup

variable {Λ Γ : Type*} [AddCommGroup Λ] [Group Γ]
variable {X : Type} [TopologicalSpace X]
variable {orbifoldMap : TwoMeridianDeckGroup →* Γ}
variable {orbifoldMonodromy : Γ →* Multiplicative (AddAut Λ)}

/-- An identification of the fundamental group with the affine deck group constructs the
equivariant affine universal cover.  Nothing beyond that identification and the three standard
local niceness hypotheses enters. -/
public noncomputable def chosenEquivariantAffineUniversalCover_of_fundamentalGroupEquiv
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [TauCeti.SemilocallySimplyConnectedSpace X]
    (x₀ : X)
    (e : FreeTwoMeridianAffineDeck Λ
        (freeTwoMeridianMonodromy orbifoldMap orbifoldMonodromy) ≃*
      FundamentalGroup X x₀) :
    ChosenEquivariantAffineUniversalCover Λ Γ X orbifoldMap orbifoldMonodromy := by
  letI : MulAction (FreeTwoMeridianAffineDeck Λ
      (freeTwoMeridianMonodromy orbifoldMap orbifoldMonodromy))
      (TauCeti.UniversalCover x₀) :=
    MulAction.compHom (TauCeti.UniversalCover x₀) e.toMonoidHom
  exact
    { Cover := TauCeti.UniversalCover x₀
      topology := inferInstance
      action := inferInstance
      data :=
        { projection :=
            ⟨TauCeti.UniversalCover.proj, TauCeti.UniversalCover.continuous_proj x₀⟩
          quotientCovering :=
            isQuotientCoveringMap_compHom TauCeti.UniversalCover.isQuotientCoveringMap e
          simplyConnected := TauCeti.UniversalCover.simplyConnectedSpace x₀ } }

end AffineCoverOfFundamentalGroup

section PuncturedGlobalFamily

namespace Geometry.GlobalTorusFamily

open Periods TriangleGroup Geometry.ComplexTorus

/-- The classification input retained by `EstablishedEquivariantUniversalCover`: the punctured
global family is locally nice, and its fundamental group at some base point is the
affine deck group `IntegerPeriods ⋊ FreeGroup (Fin 2)` with the two free meridians acting by the
order-three and order-four integral period monodromies.  No covering space is postulated. -/
public structure PuncturedGlobalFamilyAffineFundamentalGroup
    {U : TriangleUniformization} (F : PeriodFunctions U) where
  locallyPathConnected : LocallyPathConnectedSpace (PuncturedGlobalFamily F)
  pathConnected : PathConnectedSpace (PuncturedGlobalFamily F)
  semilocallySimplyConnected :
    TauCeti.SemilocallySimplyConnectedSpace (PuncturedGlobalFamily F)
  base : PuncturedGlobalFamily F
  identification :
    FreeTwoMeridianAffineDeck IntegerPeriods
        (freeTwoMeridianMonodromy (twoMeridianOrbifoldMap g₁ g₂)
          integralOrbifoldPeriodMonodromy) ≃*
      FundamentalGroup (PuncturedGlobalFamily F) base

set_option linter.style.haveILetI false in
/-- The affine fundamental-group identification constructs the chosen equivariant affine
universal cover outright. -/
public noncomputable def puncturedGlobalFamilyEquivariantUniversalCover_of_fundamentalGroup
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (P : PuncturedGlobalFamilyAffineFundamentalGroup F) :
    ChosenEquivariantAffineUniversalCover IntegerPeriods Delta (PuncturedGlobalFamily F)
      (twoMeridianOrbifoldMap g₁ g₂) integralOrbifoldPeriodMonodromy := by
  letI := P.locallyPathConnected
  letI := P.pathConnected
  letI := P.semilocallySimplyConnected
  exact chosenEquivariantAffineUniversalCover_of_fundamentalGroupEquiv P.base P.identification

/-- Exact residual statement: the equivariant universal-cover classification for the punctured
global family follows from the affine fundamental-group identification above.  Conversely the
only thing the classification is used for downstream is that identification, through
`EquivariantAffineUniversalCover.fundamentalGroupCorePiOneData`. -/
public theorem nonempty_chosenEquivariantAffineUniversalCover_of_fundamentalGroup
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (P : PuncturedGlobalFamilyAffineFundamentalGroup F) :
    Nonempty (ChosenEquivariantAffineUniversalCover IntegerPeriods Delta
      (PuncturedGlobalFamily F) (twoMeridianOrbifoldMap g₁ g₂)
      integralOrbifoldPeriodMonodromy) :=
  ⟨puncturedGlobalFamilyEquivariantUniversalCover_of_fundamentalGroup F P⟩

end Geometry.GlobalTorusFamily

end PuncturedGlobalFamily

end SphereSixComplex
