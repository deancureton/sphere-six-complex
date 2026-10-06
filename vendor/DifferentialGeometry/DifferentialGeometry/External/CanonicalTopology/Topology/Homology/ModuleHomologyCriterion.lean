module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps

@[expose] public section

/-! # A concrete cycle-and-boundary criterion for the original homology map -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace DifferentialGeometry.Topology

variable {R : Type u} [Ring R] {S T : ShortComplex (ModuleCat.{v} R)}

/-- Proved algebraic criterion: lifting cycle classes and reflecting
actual boundaries makes the ORIGINAL categorical homology map an isomorphism. -/
theorem isIso_moduleHomologyMap_of_cycles (φ : S ⟶ T)
    (hinj : ∀ c : LinearMap.ker S.g.hom, ∀ b : T.X₁, T.f b = φ.τ₂ c.val →
      ∃ a : S.X₁, S.f a = c.val)
    (hsurj : ∀ d : LinearMap.ker T.g.hom, ∃ c : LinearMap.ker S.g.hom,
      ∃ b : T.X₁, T.f b = d.val - φ.τ₂ c.val) :
    IsIso (ShortComplex.homologyMap φ) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply (injective_iff_map_eq_zero (ShortComplex.homologyMap φ).hom).mpr
    intro a ha
    obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective S a
    change ShortComplex.homologyMap φ (moduleHomologyClass S c) = 0 at ha
    rw [moduleHomologyClass_map, moduleHomologyClass_eq_zero_iff] at ha
    obtain ⟨b, hb⟩ := ha
    exact (moduleHomologyClass_eq_zero_iff S c).mpr (hinj c b hb)
  · intro a
    obtain ⟨d, rfl⟩ := moduleHomologyClass_surjective T a
    obtain ⟨c, b, hb⟩ := hsurj d
    refine ⟨moduleHomologyClass S c, ?_⟩
    rw [moduleHomologyClass_map]
    exact ((moduleHomologyClass_eq_iff T d (moduleCycleMap φ c)).mpr ⟨b, hb⟩).symm

end DifferentialGeometry.Topology
