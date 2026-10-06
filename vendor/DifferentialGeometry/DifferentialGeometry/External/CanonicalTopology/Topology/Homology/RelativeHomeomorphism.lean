module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeFunctoriality
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalHomology
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-! # Original relative and local homology under the same homeomorphism -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

set_option backward.isDefEq.respectTransparency false in
/-- An actual homeomorphism carrying the original subspaces in both
directions induces inverse maps on the SAME original relative complexes. -/
def integralRelativeChainHomeomorphIso (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (he : MapsTo e A B) (he' : MapsTo e.symm B A) :
    integralRelativeChains A ≅ integralRelativeChains B where
  hom := integralRelativeChainMap ⟨e, e.continuous⟩ he
  inv := integralRelativeChainMap ⟨e.symm, e.symm.continuous⟩ he'
  hom_inv_id := by
    rw [← integralRelativeChainMap_comp]
    have h : (⟨e.symm, e.symm.continuous⟩ : C(Y, X)).comp ⟨e, e.continuous⟩ = ContinuousMap.id X := by
      ext x
      exact e.symm_apply_apply x
    exact integralRelativeChainMap_eq_id _ _ _ h
  inv_hom_id := by
    rw [← integralRelativeChainMap_comp]
    have h : (⟨e, e.continuous⟩ : C(X, Y)).comp ⟨e.symm, e.symm.continuous⟩ = ContinuousMap.id Y := by
      ext y
      exact e.apply_symm_apply y
    exact integralRelativeChainMap_eq_id _ _ _ h

/-- The actual relative homology isomorphism induced by the SAME
homeomorphism of the original pair. -/
def integralRelativeHomologyHomeomorphIso (n : ℕ) (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (he : MapsTo e A B) (he' : MapsTo e.symm B A) :
    integralRelativeHomology n A ≅ integralRelativeHomology n B :=
  HomologicalComplex.homologyMapIso (integralRelativeChainHomeomorphIso e A B he he') n

/-- Its map is precisely the original induced relative homology map. -/
theorem integralRelativeHomologyHomeomorphIso_hom (n : ℕ) (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (he : MapsTo e A B) (he' : MapsTo e.symm B A) :
    (integralRelativeHomologyHomeomorphIso n e A B he he').hom.hom =
      integralRelativeHomologyMap n ⟨e, e.continuous⟩ he := rfl

/-- An actual homeomorphism identifies the original local homology at
the specified point with that at its SAME image point. -/
def integralLocalHomologyHomeomorphIso (n : ℕ) (e : X ≃ₜ Y) (x : X) :
    integralLocalHomology n x ≅ integralLocalHomology n (e x) :=
  integralRelativeHomologyHomeomorphIso n e {x}ᶜ {e x}ᶜ
    (fun _ hy => e.injective.ne hy)
    (fun y hy => by
      change e.symm y ≠ x
      intro h
      apply hy
      exact (e.apply_symm_apply y).symm.trans (congrArg e h))

variable {Z : Type u} [TopologicalSpace Z]

private theorem localHomeomorph_hom_eq_map (n : ℕ) (e : X ≃ₜ Y) (x : X)
    (he : MapsTo e ({x}ᶜ : Set X) ({e x}ᶜ : Set Y)) :
    (integralLocalHomologyHomeomorphIso n e x).hom.hom =
      integralRelativeHomologyMap n ⟨e, e.continuous⟩ he := rfl

theorem integralLocalHomologyHomeomorphIso_trans (n : ℕ) (e : X ≃ₜ Y)
    (f : Y ≃ₜ Z) (x : X) :
    (integralLocalHomologyHomeomorphIso n (e.trans f) x).hom.hom =
      (integralLocalHomologyHomeomorphIso n f (e x)).hom.hom.comp
        (integralLocalHomologyHomeomorphIso n e x).hom.hom := by
  let he : MapsTo e ({x}ᶜ : Set X) ({e x}ᶜ : Set Y) := fun _ hy => e.injective.ne hy
  let hf : MapsTo f ({e x}ᶜ : Set Y) ({f (e x)}ᶜ : Set Z) := fun _ hy => f.injective.ne hy
  let hef : MapsTo (e.trans f) ({x}ᶜ : Set X) ({(e.trans f) x}ᶜ : Set Z) :=
    fun _ hy => (e.trans f).injective.ne hy
  rw [localHomeomorph_hom_eq_map n (e.trans f) x hef,
    localHomeomorph_hom_eq_map n f (e x) hf, localHomeomorph_hom_eq_map n e x he]
  rw [← integralRelativeHomologyMap_comp]
  rfl

theorem integralLocalHomologyNeighborhoodIso_hom [T1Space X] (n : ℕ)
    (x : X) (U : Set X) (hU : IsOpen U) (hx : x ∈ U) :
    (integralLocalHomologyNeighborhoodIso n x U hU hx).hom.hom =
      integralRelativeHomologyMap n (singularSubspaceInclusion U)
        (neighborhoodPointComplement_mapsTo x U hx) := rfl

theorem integralLocalHomologyNeighborhoodIso_map [T1Space X] [T1Space Y]
    (n : ℕ) (f : ContinuousMap X Y) (x : X)
    (hf : MapsTo f ({x}ᶜ : Set X) ({f x}ᶜ : Set Y))
    (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : MapsTo f U V) (hx : x ∈ U) :
    (integralRelativeHomologyMap n f hf).comp
        (integralLocalHomologyNeighborhoodIso n x U hU hx).hom.hom =
      (integralLocalHomologyNeighborhoodIso n (f x) V hV (hUV hx)).hom.hom.comp
        (integralRelativeHomologyMap n (singularPairRestriction f hUV)
          (show MapsTo (singularPairRestriction f hUV)
            ({(⟨x, hx⟩ : U)}ᶜ : Set U) ({(⟨f x, hUV hx⟩ : V)}ᶜ : Set V) from
            fun y hy h => hf (show (y : X) ∈ ({x}ᶜ : Set X) from
              fun hxy => hy (Subtype.ext hxy)) (congrArg Subtype.val h))) := by
  change (integralRelativeHomologyMap n _ _).comp
      (integralRelativeHomologyMap n _ _) =
    (integralRelativeHomologyMap n _ _).comp (integralRelativeHomologyMap n _ _)
  rw [← integralRelativeHomologyMap_comp, ← integralRelativeHomologyMap_comp]
  rfl

theorem integralLocalHomologyNeighborhoodIso_natural [T1Space X] [T1Space Y]
    (n : ℕ) (e : X ≃ₜ Y) (U : Set X) (V : Set Y)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : ∀ x, x ∈ U ↔ e x ∈ V)
    (x : X) (hx : x ∈ U) :
    (integralLocalHomologyHomeomorphIso n e x).hom.hom.comp
        (integralLocalHomologyNeighborhoodIso n x U hU hx).hom.hom =
      (integralLocalHomologyNeighborhoodIso n (e x) V hV ((hUV x).mp hx)).hom.hom.comp
        (integralLocalHomologyHomeomorphIso n (e.subtype hUV) (⟨x, hx⟩ : U)).hom.hom := by
  let he : MapsTo e ({x}ᶜ : Set X) ({e x}ᶜ : Set Y) := fun _ hy => e.injective.ne hy
  let hmap : MapsTo e U V := fun y hy => (hUV y).mp hy
  let heU : MapsTo (singularPairRestriction ⟨e, e.continuous⟩ hmap)
      ({(⟨x, hx⟩ : U)}ᶜ : Set U) ({(⟨e x, hmap hx⟩ : V)}ᶜ : Set V) :=
    fun _ hy h => hy (Subtype.ext (e.injective (congrArg Subtype.val h)))
  have hsub : (integralLocalHomologyHomeomorphIso n (e.subtype hUV)
      (⟨x, hx⟩ : U)).hom.hom =
      integralRelativeHomologyMap n (singularPairRestriction ⟨e, e.continuous⟩ hmap)
        heU := rfl
  rw [localHomeomorph_hom_eq_map n e x he, hsub]
  exact integralLocalHomologyNeighborhoodIso_map n ⟨e, e.continuous⟩ x he
    U V hU hV hmap hx

theorem integralLocalHomologyNeighborhoodIso_comp [T1Space X] (n : ℕ)
    (x : X) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ⊆ V) (hx : x ∈ U) :
    (integralLocalHomologyNeighborhoodIso n x V hV (hUV hx)).hom.hom.comp
        (integralRelativeHomologyMap n
          (singularPairRestriction (ContinuousMap.id X) hUV)
          (show MapsTo (singularPairRestriction (ContinuousMap.id X) hUV)
            ({(⟨x, hx⟩ : U)}ᶜ : Set U) ({(⟨x, hUV hx⟩ : V)}ᶜ : Set V) from
            fun _ hy h => hy (Set.mem_singleton_iff.mpr (Subtype.ext
              (congrArg (fun z : V => (z : X)) (Set.mem_singleton_iff.mp h)))))) =
      (integralLocalHomologyNeighborhoodIso n x U hU hx).hom.hom := by
  change (integralRelativeHomologyMap n _ _).comp
      (integralRelativeHomologyMap n _ _) = integralRelativeHomologyMap n _ _
  rw [← integralRelativeHomologyMap_comp]
  rfl

theorem integralRelativeHomologyMap_eq_of_eqOn_neighborhood [T1Space X]
    (n : ℕ) (f g : ContinuousMap X Y) (x : X) (y : Y)
    (hf : MapsTo f ({x}ᶜ : Set X) ({y}ᶜ : Set Y))
    (hg : MapsTo g ({x}ᶜ : Set X) ({y}ᶜ : Set Y))
    (U : Set X) (hU : IsOpen U) (hx : x ∈ U) (hfg : EqOn f g U) :
    integralRelativeHomologyMap n f hf = integralRelativeHomologyMap n g hg := by
  let e := integralLocalHomologyNeighborhoodIso n x U hU hx
  have he : Function.Surjective e.hom.hom := by
    intro a
    refine ⟨e.inv.hom a, ?_⟩
    exact congrArg (fun k => k.hom a) e.inv_hom_id
  have hcomp : (integralRelativeHomologyMap n f hf).comp e.hom.hom =
      (integralRelativeHomologyMap n g hg).comp e.hom.hom := by
    change (integralRelativeHomologyMap n f hf).comp
        (integralRelativeHomologyMap n _ _) =
      (integralRelativeHomologyMap n g hg).comp (integralRelativeHomologyMap n _ _)
    rw [← integralRelativeHomologyMap_comp, ← integralRelativeHomologyMap_comp]
    have hmaps : f.comp (singularSubspaceInclusion U) =
        g.comp (singularSubspaceInclusion U) := by
      ext z
      exact hfg z.property
    simp only [hmaps]
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := he a
  exact LinearMap.congr_fun hcomp b

end DifferentialGeometry.Topology
