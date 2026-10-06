module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallChains

@[expose] public section

/-! # The actual small singular chain subcomplex -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- Retain the original submodule scalar action on the small-chain subtype. -/
instance integralSingularSmallChainsModule (n : ℕ) (U : ι → Set X) :
    Module ℤ (integralSingularSmallChains n U) := (integralSingularSmallChains n U).module

/-- Restrict the same actual singular boundary to the small-chain submodules. -/
def integralSingularSmallBoundary (i j : ℕ) (U : ι → Set X) :
    integralSingularSmallChains i U →ₗ[ℤ] integralSingularSmallChains j U :=
  ((integralSingularChains X).d i j).hom.restrict
    (fun _ hc => integralSingularSmallChains_d i j U hc)

/-- The original small-chain subcomplex with its inherited boundary. -/
def integralSingularSmallComplex (U : ι → Set X) : ChainComplex (ModuleCat.{u} ℤ) ℕ where
  X n := ModuleCat.of ℤ (integralSingularSmallChains n U)
  d i j := ModuleCat.ofHom (integralSingularSmallBoundary i j U)
  shape i j h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change (integralSingularChains X).d i j c.val = 0
    rw [(integralSingularChains X).shape i j h]
    rfl
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change (integralSingularChains X).d j k ((integralSingularChains X).d i j c.val) = 0
    exact congrArg (fun f : (integralSingularChains X).X i ⟶
      (integralSingularChains X).X k => f c.val) ((integralSingularChains X).d_comp_d i j k)

/-- Inclusion is the actual subtype inclusion in every degree. -/
def integralSingularSmallInclusion (U : ι → Set X) :
    integralSingularSmallComplex U ⟶ integralSingularChains X where
  f n := ModuleCat.ofHom (integralSingularSmallChains n U).subtype
  comm' _ _ _ := rfl

/-- The original small-chain inclusion is injective on the full complex. -/
instance integralSingularSmallInclusion_mono (U : ι → Set X) :
    Mono (integralSingularSmallInclusion U) :=
  HomologicalComplex.mono_of_mono_f _ (fun _n =>
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective)

end DifferentialGeometry.Topology
