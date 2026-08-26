module

public import SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Restricted orbit quotients as open subspaces

An invariant open carrier for a continuous group action has an orbit quotient which embeds as an
open subspace of the ambient orbit quotient.  This is the point-set identification needed to keep
the full deck action visible when passing from a lifted radial domain to the corresponding region
of a quotient family.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

open Set Topology
open Geometry.EquivariantQuotientHomeomorph

universe u

variable {G X : Type u} [Group G] [TopologicalSpace X]

/-- The subtype inclusion respects the restricted and ambient orbit relations. -/
public theorem restrictedOrbitRel_subtype_val
    (A : MulAction G X) (S : InvariantOpenCarrier A) :
    ∀ a b : S.carrier, restrictedOrbitRel A S a b →
      orbitRelOf A (a : X) (b : X) := by
  intro a b hab
  change (letI := restrictedMulAction A S
    MulAction.orbitRel G S.carrier a b) at hab
  change (∃ g : G, restrictedActionMap S g b = a) at hab
  change ∃ g : G, actionMap A g (b : X) = (a : X)
  obtain ⟨g, hg⟩ := hab
  exact ⟨g, congrArg Subtype.val hg⟩

/-- The canonical map from the orbit quotient of an invariant carrier to the ambient orbit
quotient. -/
public noncomputable def restrictedOrbitQuotientInclusion
    (A : MulAction G X) (S : InvariantOpenCarrier A) :
    Quotient (restrictedOrbitRel A S) → Quotient (orbitRelOf A) :=
  Quotient.map Subtype.val (restrictedOrbitRel_subtype_val A S)

@[simp]
public theorem restrictedOrbitQuotientInclusion_mk
    (A : MulAction G X) (S : InvariantOpenCarrier A) (x : S.carrier) :
    restrictedOrbitQuotientInclusion A S (Quotient.mk _ x) =
      Quotient.mk _ (x : X) :=
  rfl

public theorem restrictedOrbitQuotientInclusion_continuous
    (A : MulAction G X) (S : InvariantOpenCarrier A) :
    Continuous (restrictedOrbitQuotientInclusion A S) := by
  exact continuous_quot_map (restrictedOrbitRel_subtype_val A S) continuous_subtype_val

public theorem restrictedOrbitQuotientInclusion_injective
    (A : MulAction G X) (S : InvariantOpenCarrier A) :
    Function.Injective (restrictedOrbitQuotientInclusion A S) := by
  intro q₁ q₂ h
  induction q₁ using Quotient.inductionOn with
  | _ x =>
    induction q₂ using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      change (letI := restrictedMulAction A S
        MulAction.orbitRel G S.carrier x y)
      change ∃ g : G, restrictedActionMap S g y = x
      have hxy : orbitRelOf A (x : X) (y : X) := Quotient.exact h
      change (∃ g : G, actionMap A g (y : X) = (x : X)) at hxy
      obtain ⟨g, hg⟩ := hxy
      exact ⟨g, Subtype.ext hg⟩

public theorem restrictedOrbitQuotientInclusion_isOpenMap
    (A : MulAction G X) (S : InvariantOpenCarrier A)
    (hcontinuous : letI := A; ContinuousConstSMul G X) :
    IsOpenMap (restrictedOrbitQuotientInclusion A S) := by
  let _ := A
  let _ : ContinuousConstSMul G X := hcontinuous
  have hpre : IsOpenMap (fun x : S.carrier ↦
      (Quotient.mk _ (x : X) : Quotient (orbitRelOf A))) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := X)).isOpenMap.comp
      S.isOpen_carrier.isOpenMap_subtype_val
  apply IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective
  convert hpre using 1
  funext x
  rfl

/-- The restricted quotient is an open subspace of the ambient orbit quotient. -/
public theorem restrictedOrbitQuotientInclusion_isOpenEmbedding
    (A : MulAction G X) (S : InvariantOpenCarrier A)
    (hcontinuous : letI := A; ContinuousConstSMul G X) :
    IsOpenEmbedding (restrictedOrbitQuotientInclusion A S) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (restrictedOrbitQuotientInclusion_continuous A S)
    (restrictedOrbitQuotientInclusion_injective A S)
    (restrictedOrbitQuotientInclusion_isOpenMap A S hcontinuous)

/-- The carrier quotient identified with its literal image in the ambient orbit quotient. -/
public noncomputable def restrictedOrbitQuotientHomeomorphRange
    (A : MulAction G X) (S : InvariantOpenCarrier A)
    (hcontinuous : letI := A; ContinuousConstSMul G X) :
    Quotient (restrictedOrbitRel A S) ≃ₜ
      Set.range (restrictedOrbitQuotientInclusion A S) :=
  (restrictedOrbitQuotientInclusion_isOpenEmbedding A S hcontinuous).isEmbedding.toHomeomorph

end SphereSixComplex
