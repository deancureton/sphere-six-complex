module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallHomology

@[expose] public section

/-! # Actual subspace chains included in the original small complex -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The original inclusion of a cover member takes its chains into the
SAME original small-chain submodule. -/
theorem integralSingularChainToSmall_mem (n : ℕ) (U : ι → Set X) (i : ι)
    (c : (integralSingularChains (U i)).X n) :
    (integralSingularChainMap (singularSubspaceInclusion (U i))).f n c ∈ integralSingularSmallChains n U := by
  apply Submodule.mem_iSup_of_mem i
  rw [integralSingularChainsIn_eq_range]
  exact ⟨c, rfl⟩

/-- The SAME actual inclusion, corestricted to the original small complex. -/
def integralSingularChainToSmall (U : ι → Set X) (i : ι) :
    integralSingularChains (U i) ⟶ integralSingularSmallComplex U where
  f n := ModuleCat.ofHom (((integralSingularChainMap (singularSubspaceInclusion (U i))).f n).hom.codRestrict
    (integralSingularSmallChains n U) (integralSingularChainToSmall_mem n U i))
  comm' j k _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f : (integralSingularChains (U i)).X j ⟶ (integralSingularChains X).X k => f c)
      ((integralSingularChainMap (singularSubspaceInclusion (U i))).comm j k)

/-- Factoring through the small complex gives the SAME original subspace inclusion. -/
theorem integralSingularChainToSmall_inclusion (U : ι → Set X) (i : ι) :
    integralSingularChainToSmall U i ≫ integralSingularSmallInclusion U =
      integralSingularChainMap (singularSubspaceInclusion (U i)) := rfl

/-- This actual inclusion into the small complex is injective. -/
instance integralSingularChainToSmall_mono (U : ι → Set X) (i : ι) :
    Mono (integralSingularChainToSmall U i) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  intro a b h
  apply integralSingularChainInclusion_injective n (U i)
  exact congrArg Subtype.val h

end DifferentialGeometry.Topology
