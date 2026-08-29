module

public import SphereSixComplex.Topology.EstablishedEquivariantUniversalCoverProof
public import SphereSixComplex.Geometry.FuchsianPuncturedGlobalFamilyNiceness
public import SphereSixComplex.Periods.FuchsianUniformizationBridge
public import SphereSixComplex.Topology.PaperGeometricCentralCore

/-!
# The paper's punctured-family affine fundamental group

The definitions of the two-meridian deck group, the affine deck extension and the equivariant
affine universal cover are in `EstablishedEquivariantUniversalCoverDefs`, and are re-exported
here, so every module path using them is unchanged.

This module reduces the remaining classification input for the paper's punctured global family
to injectivity of its canonical affine presentation and derives the equivariant universal cover.

## What is assumed, and why in this form

The geometric period loops and the two marked meridians already define a canonical homomorphism
from `IntegerPeriods ⋊ FreeGroup (Fin 2)` to the fundamental group.  Their conjugation laws and
generation theorem prove that this homomorphism is surjective.  The sole retained input is that
it is injective, i.e. that the global pair-of-pants gluing introduces no additional relation.

The based-path cover also needs the base to be path connected, locally path connected and
semilocally simply connected.  None of the three is assumed: over a Fuchsian modular parameter the
family is a complex manifold and connected, so all three follow
(`Geometry.FuchsianPuncturedGlobalFamilyNiceness`).

The explicit affine mapping-torus covers prove the corresponding cyclic statements on both
elliptic collars.  They do not by themselves prove the global pair-of-pants gluing, which is
exactly the injectivity residual retained here.

The covering space is not assumed.  The resulting fundamental-group equivalence is transported
onto Tau Ceti's based-path universal cover.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex

namespace AffineTorusCorePiOneData

variable {G Λ : Type*} [Group G] [AddCommGroup Λ]
variable (M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ))
variable (C : AffineTorusCorePiOneData G Λ (firstFreeMonodromy M) (secondFreeMonodromy M))

public def freeMeridianHom : TwoMeridianDeckGroup →* G :=
  FreeGroup.lift fun i ↦ if i = 0 then C.rhoOne else C.rhoTwo

public theorem freeMeridianHom_conjugate (g : TwoMeridianDeckGroup) (a : Λ) :
    freeMeridianHom M C g * Additive.toMul (C.translation a) *
        (freeMeridianHom M C g)⁻¹ =
      Additive.toMul (C.translation ((M g).toAdd a)) := by
  induction g using FreeGroup.induction_on generalizing a with
  | C1 => simp
  | of i =>
      fin_cases i
      · simpa [freeMeridianHom, firstFreeMonodromy, firstMeridian] using C.conjugate_one a
      · simpa [freeMeridianHom, secondFreeMonodromy, secondMeridian] using C.conjugate_two a
  | inv_of i hi =>
      let g := FreeGroup.of i
      have h := hi ((M g).toAdd.symm a)
      have hM : (M g).toAdd ((M g).toAdd.symm a) = a := (M g).toAdd.apply_symm_apply a
      rw [hM] at h
      rw [map_inv, map_inv]
      calc
        (freeMeridianHom M C g)⁻¹ * Additive.toMul (C.translation a) *
              ((freeMeridianHom M C g)⁻¹)⁻¹ =
            (freeMeridianHom M C g)⁻¹ *
              (freeMeridianHom M C g *
                Additive.toMul (C.translation ((M g).toAdd.symm a)) *
                (freeMeridianHom M C g)⁻¹) *
              ((freeMeridianHom M C g)⁻¹)⁻¹ := by rw [h]
        _ = Additive.toMul (C.translation ((M g).toAdd.symm a)) := by group
  | mul g h hg hh =>
      rw [map_mul, map_mul]
      calc
        (freeMeridianHom M C g * freeMeridianHom M C h) *
              Additive.toMul (C.translation a) *
              (freeMeridianHom M C g * freeMeridianHom M C h)⁻¹ =
            freeMeridianHom M C g *
              (freeMeridianHom M C h * Additive.toMul (C.translation a) *
                (freeMeridianHom M C h)⁻¹) *
              (freeMeridianHom M C g)⁻¹ := by group
        _ = freeMeridianHom M C g *
              Additive.toMul (C.translation ((M h).toAdd a)) *
              (freeMeridianHom M C g)⁻¹ := by rw [hh]
        _ = Additive.toMul (C.translation ((M g).toAdd ((M h).toAdd a))) := hg _
        _ = Additive.toMul (C.translation (((M g) * (M h)).toAdd a)) := rfl

public def freeAffinePresentationHom : FreeTwoMeridianAffineDeck Λ M →* G :=
  SemidirectProduct.lift C.translation.toMultiplicative (freeMeridianHom M C) (by
    intro g
    apply MonoidHom.ext
    intro a
    exact (freeMeridianHom_conjugate M C g a.toAdd).symm)

@[simp]
public theorem freeAffinePresentationHom_translation (a : Λ) :
    freeAffinePresentationHom M C
        (Additive.toMul (freeAffineTranslation (M := M) a)) =
      Additive.toMul (C.translation a) := by
  change Additive.toMul (C.translation a) * 1 = _
  simp

@[simp]
public theorem freeAffinePresentationHom_first :
    freeAffinePresentationHom M C
        (freeAffineLift (Λ := Λ) (M := M) firstMeridian) = C.rhoOne := by
  simp [freeAffinePresentationHom, freeAffineLift, SemidirectProduct.lift, freeMeridianHom,
    firstMeridian]
  exact map_one C.translation.toMultiplicative

@[simp]
public theorem freeAffinePresentationHom_second :
    freeAffinePresentationHom M C
        (freeAffineLift (Λ := Λ) (M := M) secondMeridian) = C.rhoTwo := by
  simp [freeAffinePresentationHom, freeAffineLift, SemidirectProduct.lift, freeMeridianHom,
    secondMeridian]
  exact map_one C.translation.toMultiplicative

public theorem freeAffinePresentationHom_surjective :
    Function.Surjective (freeAffinePresentationHom M C) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← C.generators_generate, Subgroup.closure_le]
  intro g hg
  rcases hg with ⟨a, rfl⟩ | hg
  · exact ⟨Additive.toMul (freeAffineTranslation (M := M) a), by simp⟩
  · rcases hg with rfl | rfl
    · exact ⟨freeAffineLift firstMeridian, by simp⟩
    · exact ⟨freeAffineLift secondMeridian, by simp⟩

end AffineTorusCorePiOneData

namespace Geometry.GlobalTorusFamily

open Periods TriangleGroup Geometry.ComplexTorus
open SphereSixComplex.LatticeData SphereSixComplex.Topology

/-- The free two-meridian monodromy of the paper's punctured global family. -/
public noncomputable abbrev paperPuncturedGlobalFamilyFreeMonodromy :
    TwoMeridianDeckGroup →* Multiplicative (AddAut Lattice) :=
  freeTwoMeridianMonodromy (twoMeridianOrbifoldMap g₁ g₂)
    integralOrbifoldPeriodMonodromy

public theorem firstFreeMonodromy_paperPuncturedGlobalFamilyFreeMonodromy :
    firstFreeMonodromy paperPuncturedGlobalFamilyFreeMonodromy = paperMonodromyOne := by
  apply AddMonoidHom.ext
  intro a
  simp [firstFreeMonodromy, paperPuncturedGlobalFamilyFreeMonodromy,
    freeTwoMeridianMonodromy, integralOrbifoldPeriodMonodromy,
    paperMonodromyOne]

public theorem secondFreeMonodromy_paperPuncturedGlobalFamilyFreeMonodromy :
    secondFreeMonodromy paperPuncturedGlobalFamilyFreeMonodromy = paperMonodromyTwo := by
  apply AddMonoidHom.ext
  intro a
  simp [secondFreeMonodromy, paperPuncturedGlobalFamilyFreeMonodromy,
    freeTwoMeridianMonodromy, integralOrbifoldPeriodMonodromy,
    paperMonodromyTwo]

/-- The geometric translations and marked meridians as affine core data at the actual cusp
basepoint. -/
public noncomputable def paperPuncturedGlobalFamilyAffineCorePiOneData
    (A : PaperAnalyticData) :
    AffineTorusCorePiOneData
      (FundamentalGroup A.CentralFamily A.actualCuspCentralBase)
      Lattice (firstFreeMonodromy paperPuncturedGlobalFamilyFreeMonodromy)
        (secondFreeMonodromy paperPuncturedGlobalFamilyFreeMonodromy) := by
  rw [firstFreeMonodromy_paperPuncturedGlobalFamilyFreeMonodromy,
    secondFreeMonodromy_paperPuncturedGlobalFamilyFreeMonodromy]
  exact A.actualCuspGeometricCorePiOneData

/-- The canonical affine presentation map determined by the geometric period loops and the two
marked meridians. -/
public noncomputable def paperPuncturedGlobalFamilyAffinePresentation
    (A : PaperAnalyticData) :
    FreeTwoMeridianAffineDeck Lattice paperPuncturedGlobalFamilyFreeMonodromy →*
      FundamentalGroup A.CentralFamily A.actualCuspCentralBase :=
  AffineTorusCorePiOneData.freeAffinePresentationHom
    paperPuncturedGlobalFamilyFreeMonodromy
    (paperPuncturedGlobalFamilyAffineCorePiOneData A)

/-- Exact residual: the canonical surjective affine presentation has no additional global
pair-of-pants relation. -/
public axiom paperPuncturedGlobalFamilyAffinePresentation_injective
    (A : PaperAnalyticData) :
    Function.Injective (paperPuncturedGlobalFamilyAffinePresentation A)

/-- The paper's punctured-family affine fundamental-group classification, derived from the
canonical presentation and its injectivity residual. -/
public noncomputable def establishedPuncturedGlobalFamilyAffineFundamentalGroup
    (A : PaperAnalyticData) :
    PuncturedGlobalFamilyAffineFundamentalGroup A.periods where
  base := A.actualCuspCentralBase
  identification := MulEquiv.ofBijective (paperPuncturedGlobalFamilyAffinePresentation A)
    ⟨paperPuncturedGlobalFamilyAffinePresentation_injective A,
      AffineTorusCorePiOneData.freeAffinePresentationHom_surjective
        paperPuncturedGlobalFamilyFreeMonodromy
        (paperPuncturedGlobalFamilyAffineCorePiOneData A)⟩

/-- The equivariant universal-cover classification for a punctured Fuchsian affine torus family.

This is now a theorem: the affine fundamental-group identification above is transported onto
Tau Ceti's based-path universal cover, which is simply connected and whose fundamental-group
action is a quotient covering map.  The conclusion supplies only the universal cover and its
affine deck action. -/
public noncomputable def establishedPuncturedGlobalFamilyEquivariantUniversalCover
    (A : PaperAnalyticData) :
    ChosenEquivariantAffineUniversalCover IntegerPeriods Delta A.CentralFamily
      (twoMeridianOrbifoldMap g₁ g₂) integralOrbifoldPeriodMonodromy :=
  letI := fuchsianPuncturedGlobalFamily_locallyPathConnected A.modular.modularParameter A.periods
  letI := fuchsianPuncturedGlobalFamily_pathConnected A.modular.modularParameter A.periods
  letI := fuchsianPuncturedGlobalFamily_semilocallySimplyConnected
    A.modular.modularParameter A.periods
  puncturedGlobalFamilyEquivariantUniversalCover_of_fundamentalGroup A.periods
    (establishedPuncturedGlobalFamilyAffineFundamentalGroup A)

end Geometry.GlobalTorusFamily

end SphereSixComplex

end
