module

public import SphereSixComplex.Prerequisites.Topology.EstablishedAffineVanKampen

/-!
# Transport of affine van Kampen data

Affine core presentations and filling relations descend along a surjective group homomorphism.
This is the algebraic step used after the central-piece fundamental group is mapped into a star
gluing.
-/

@[expose] public section

namespace SphereSixComplex

namespace AffineTorusCorePiOneData

variable {G H Λ : Type*} [Group G] [Group H] [AddCommGroup Λ]
variable {monodromyOne monodromyTwo : Λ →+ Λ}

/-- Push an affine-core presentation through a surjective group homomorphism. -/
public def mapSurjective
    (C : AffineTorusCorePiOneData G Λ monodromyOne monodromyTwo)
    (f : G →* H) (hf : Function.Surjective f) :
    AffineTorusCorePiOneData H Λ monodromyOne monodromyTwo where
  translation := f.toAdditive.comp C.translation
  rhoOne := f C.rhoOne
  rhoTwo := f C.rhoTwo
  conjugate_one a := by
    change f C.rhoOne * f (Additive.toMul (C.translation a)) * (f C.rhoOne)⁻¹ =
      f (Additive.toMul (C.translation (monodromyOne a)))
    simpa only [map_mul, map_inv] using congrArg f (C.conjugate_one a)
  conjugate_two a := by
    change f C.rhoTwo * f (Additive.toMul (C.translation a)) * (f C.rhoTwo)⁻¹ =
      f (Additive.toMul (C.translation (monodromyTwo a)))
    simpa only [map_mul, map_inv] using congrArg f (C.conjugate_two a)
  generators_generate := by
    let S := Set.range (fun a ↦ Additive.toMul (C.translation a)) ∪
      {C.rhoOne, C.rhoTwo}
    let T := Set.range
        (fun a ↦ Additive.toMul ((f.toAdditive.comp C.translation) a)) ∪
      {f C.rhoOne, f C.rhoTwo}
    let K : Subgroup H := Subgroup.closure T
    have hle : Subgroup.closure S ≤ K.comap f := by
      rw [Subgroup.closure_le]
      intro g hg
      change f g ∈ K
      apply Subgroup.subset_closure
      rcases hg with ⟨a, rfl⟩ | hg
      · exact Or.inl ⟨a, rfl⟩
      · rcases hg with rfl | rfl
        · exact Or.inr (Set.mem_insert _ _)
        · exact Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    apply top_unique
    intro h _
    obtain ⟨g, rfl⟩ := hf h
    change f g ∈ K
    apply hle
    rw [C.generators_generate]
    trivial

end AffineTorusCorePiOneData

end SphereSixComplex

end
