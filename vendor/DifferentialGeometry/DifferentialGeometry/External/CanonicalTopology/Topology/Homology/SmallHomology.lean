module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallCycles
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyCriterion
public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public section

/-! # The original small-chain inclusion induces the actual homology isomorphism -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The SAME original small-chain inclusion is a quasi-isomorphism in
every positive degree, by the constructed small representatives and boundaries. -/
theorem integralSingularSmallInclusion_quasiIsoAt_succ (n : ℕ) (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    QuasiIsoAt (integralSingularSmallInclusion U) (n + 1) := by
  rw [quasiIsoAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.quasiIso_iff]
  apply isIso_moduleHomologyMap_of_cycles
  · intro c b hb
    change (integralSingularChains X).d (n + 2) (n + 1) b = c.val.val at hb
    have hc : (integralSingularChains X).d (n + 1) n c.val.val = 0 :=
      congrArg Subtype.val c.property
    obtain ⟨a, ha, hab⟩ := exists_small_boundary_of_boundary n U hU hcover c.val.val c.val.property hc b hb
    exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  · intro d
    obtain ⟨s, hs, hcycle, b, hb⟩ := exists_small_cycle_representative n U hU hcover d.val d.property
    exact ⟨⟨⟨s, hs⟩, Subtype.ext hcycle⟩, b, hb⟩

/-- The SAME original inclusion also induces an isomorphism in degree zero. -/
theorem integralSingularSmallInclusion_quasiIsoAt_zero (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    QuasiIsoAt (integralSingularSmallInclusion U) 0 := by
  rw [quasiIsoAt_iff' _ 1 0 0 (by simp) (by simp),
    ShortComplex.quasiIso_iff]
  apply isIso_moduleHomologyMap_of_cycles
  · intro c b hb
    change (integralSingularChains X).d 1 0 b = c.val.val at hb
    obtain ⟨a, ha, hab⟩ := exists_small_zero_boundary_of_boundary U hU hcover c.val.val b hb
    exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  · intro d
    refine ⟨⟨⟨d.val, integralSingularSmallChains_zero_all U hU hcover d.val⟩,
      Subtype.ext d.property⟩, 0, ?_⟩
    change (integralSingularChains X).d 1 0 0 = d.val - d.val
    rw [map_zero, sub_self]
    rfl

/-- The actual inclusion of original small chains for any open cover is
a quasi-isomorphism of the original integral singular chain complexes. -/
theorem integralSingularSmallInclusion_quasiIso (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    QuasiIso (integralSingularSmallInclusion U) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero => exact integralSingularSmallInclusion_quasiIsoAt_zero U hU hcover
  | succ n => exact integralSingularSmallInclusion_quasiIsoAt_succ n U hU hcover

/-- The resulting isomorphism is induced by the SAME original small-chain
inclusion; it does not replace either complex or its homology. -/
def integralSingularSmallHomologyIso (n : ℕ) (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    (integralSingularSmallComplex U).homology n ≅ (integralSingularChains X).homology n := by
  letI := integralSingularSmallInclusion_quasiIso U hU hcover
  exact asIso (HomologicalComplex.homologyMap (integralSingularSmallInclusion U) n)

end DifferentialGeometry.Topology
