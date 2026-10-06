module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainExcision
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem cochain_pullback_eq_zero_iff (n : ℕ) (A : Set X)
    (φ : integralSingularCochain n X) :
    integralSingularCochainPullback n (singularSubspaceInclusion A) φ = 0 ↔
      ∀ σ : integralSingularSimplex n X,
        range (integralSingularSimplexEquiv n X σ) ⊆ A →
          φ (integralSimplexChain n σ) = 0 := by
  constructor
  · intro hφ σ hσ
    have h := LinearMap.congr_fun hφ
      (integralSimplexChain n (integralSingularSimplexRestriction n A σ hσ))
    change φ ((integralSingularChainMap (singularSubspaceInclusion A)).f n _) = 0 at h
    rwa [integralSimplexChain_map, integralSingularSimplexRestriction_inclusion] at h
  · intro hφ
    apply (integralSingularChainBasis n A).ext
    intro σ
    change φ ((integralSingularChainMap (singularSubspaceInclusion A)).f n
      (integralSingularChainBasis n A σ)) = 0
    rw [integralSingularChainBasis_apply, integralSimplexChain_map]
    apply hφ
    rintro _ ⟨t, rfl⟩
    rw [integralSingularSimplexMap_apply]
    exact (integralSingularSimplexEquiv n A σ t).property

private theorem exists_cochain_decomposition (n : ℕ) (A B : Set X)
    (φ : integralSingularCochain n X)
    (hφ : integralSingularCochainPullback n (singularSubspaceInclusion (A ∩ B)) φ = 0) :
    ∃ α β : integralSingularCochain n X,
      integralSingularCochainPullback n (singularSubspaceInclusion A) α = 0 ∧
      integralSingularCochainPullback n (singularSubspaceInclusion B) β = 0 ∧ α + β = φ := by
  classical
  let β : integralSingularCochain n X := (integralSingularChainBasis n X).constr ℕ
    (fun σ => if range (integralSingularSimplexEquiv n X σ) ⊆ A
      then φ (integralSimplexChain n σ) else 0)
  have hβ (σ : integralSingularSimplex n X) :
      β (integralSimplexChain n σ) =
        if range (integralSingularSimplexEquiv n X σ) ⊆ A
          then φ (integralSimplexChain n σ) else 0 := by
    change ((integralSingularChainBasis n X).constr ℕ _ : integralSingularCochain n X) _ = _
    rw [← integralSingularChainBasis_apply, Basis.constr_basis, integralSingularChainBasis_apply]
  refine ⟨φ - β, β, ?_, ?_, sub_add_cancel φ β⟩
  · apply (cochain_pullback_eq_zero_iff n A _).2
    intro σ hσ
    rw [LinearMap.sub_apply, hβ, ite_eq_left hσ, sub_self]
  · apply (cochain_pullback_eq_zero_iff n B _).2
    intro σ hσ
    rw [hβ]
    split_ifs with hA
    · exact (cochain_pullback_eq_zero_iff n (A ∩ B) φ).1 hφ σ
        (fun x hx => ⟨hA hx, hσ hx⟩)
    · rfl

private theorem relative_cochain_inclusion_injective (n : ℕ) (A : Set X) :
    Function.Injective ((integralRelativeCochainInclusion A).f n) := by
  have h := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (integralRelativeCochainSequence_shortExact A) n
  exact (ModuleCat.mono_iff_injective _).1 h.mono_f

private theorem relative_cochain_inclusion_pullback (n : ℕ) (A : Set X)
    (φ : (integralRelativeCochains A).X n) :
    integralSingularCochainPullback n (singularSubspaceInclusion A)
      ((integralRelativeCochainInclusion A).f n φ) = 0 := by
  exact congrArg (fun f : integralRelativeCochains A ⟶ integralSingularCochains A => f.f n φ)
    (integralRelativeCochainInclusion_comp A)

theorem exists_relative_cochain_inter_decomposition (n : ℕ) (A B : Set X)
    (φ : (integralRelativeCochains (A ∩ B)).X n) :
    ∃ (α : (integralRelativeCochains A).X n) (β : (integralRelativeCochains B).X n),
      (integralRelativeCochainMap (ContinuousMap.id X)
        (show A ∩ B ⊆ A from inter_subset_left)).f n α +
      (integralRelativeCochainMap (ContinuousMap.id X)
        (show A ∩ B ⊆ B from inter_subset_right)).f n β = φ := by
  obtain ⟨α, β, hα, hβ, hφ⟩ := exists_cochain_decomposition n A B
    ((integralRelativeCochainInclusion (A ∩ B)).f n φ)
    (relative_cochain_inclusion_pullback n (A ∩ B) φ)
  have ha : α ∈ LinearMap.range ((integralRelativeCochainInclusion A).f n).hom := by
    rw [integralRelativeCochainInclusion_range]
    exact hα
  have hb : β ∈ LinearMap.range ((integralRelativeCochainInclusion B).f n).hom := by
    rw [integralRelativeCochainInclusion_range]
    exact hβ
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  refine ⟨a, b, relative_cochain_inclusion_injective n (A ∩ B) ?_⟩
  rw [map_add]
  have hA := integralRelativeCochainMap_inclusion (ContinuousMap.id X)
    (show A ∩ B ⊆ A from inter_subset_left)
  have hB := integralRelativeCochainMap_inclusion (ContinuousMap.id X)
    (show A ∩ B ⊆ B from inter_subset_right)
  rw [integralSingularCochainMap_id, Category.comp_id] at hA hB
  have ha := congrArg (fun f : integralRelativeCochains A ⟶ integralSingularCochains X => f.f n a) hA
  have hb := congrArg (fun f : integralRelativeCochains B ⟶ integralSingularCochains X => f.f n b) hB
  exact (congrArg₂ (· + ·) ha hb).trans hφ

def integralRelativeCochainInterSum (A B : Set X) :
    integralRelativeCochains A ⊞ integralRelativeCochains B ⟶
      integralRelativeCochains (A ∩ B) :=
  biprod.desc
    (integralRelativeCochainMap (ContinuousMap.id X)
      (show A ∩ B ⊆ A from inter_subset_left))
    (integralRelativeCochainMap (ContinuousMap.id X)
      (show A ∩ B ⊆ B from inter_subset_right))

theorem integralRelativeCochainInterSum_surjective (n : ℕ) (A B : Set X) :
    Function.Surjective ((integralRelativeCochainInterSum A B).f n) := by
  intro φ
  obtain ⟨α, β, h⟩ := exists_relative_cochain_inter_decomposition n A B φ
  let a : integralRelativeCochains A ⟶
      integralRelativeCochains A ⊞ integralRelativeCochains B := biprod.inl
  let b : integralRelativeCochains B ⟶
      integralRelativeCochains A ⊞ integralRelativeCochains B := biprod.inr
  refine ⟨a.f n α + b.f n β, ?_⟩
  rw [map_add]
  have hA : a ≫ integralRelativeCochainInterSum A B =
      integralRelativeCochainMap (ContinuousMap.id X)
        (show A ∩ B ⊆ A from inter_subset_left) := biprod.inl_desc _ _
  have hB : b ≫ integralRelativeCochainInterSum A B =
      integralRelativeCochainMap (ContinuousMap.id X)
        (show A ∩ B ⊆ B from inter_subset_right) := biprod.inr_desc _ _
  exact (congrArg₂ (· + ·)
    (congrArg (fun f : integralRelativeCochains A ⟶ integralRelativeCochains (A ∩ B) =>
      f.f n α) hA)
    (congrArg (fun f : integralRelativeCochains B ⟶ integralRelativeCochains (A ∩ B) =>
      f.f n β) hB)).trans h

theorem integralRelativeCochainInterSum_epi (A B : Set X) :
    Epi (integralRelativeCochainInterSum A B) := by
  have h (n : ℕ) : Epi ((integralRelativeCochainInterSum A B).f n) :=
    (ModuleCat.epi_iff_surjective _).2 (integralRelativeCochainInterSum_surjective n A B)
  exact HomologicalComplex.epi_of_epi_f (integralRelativeCochainInterSum A B) h

theorem integralRelativeCochainInterSum_natural
    {Y : Type u} [TopologicalSpace Y] (f : ContinuousMap X Y)
    {A B : Set X} {C D : Set Y} (hA : MapsTo f A C) (hB : MapsTo f B D) :
    biprod.map (integralRelativeCochainMap f hA) (integralRelativeCochainMap f hB) ≫
        integralRelativeCochainInterSum A B =
      integralRelativeCochainInterSum C D ≫
        integralRelativeCochainMap f
          (show MapsTo f (A ∩ B) (C ∩ D) from fun _ hx => ⟨hA hx.1, hB hx.2⟩) := by
  unfold integralRelativeCochainInterSum
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc]
    erw [← integralRelativeCochainMap_comp, ← integralRelativeCochainMap_comp]
    rfl
  · simp only [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc]
    erw [← integralRelativeCochainMap_comp, ← integralRelativeCochainMap_comp]
    rfl

theorem exists_relative_cochain_compl_union_decomposition (n : ℕ) (K L : Set X)
    (φ : (integralRelativeCochains (K ∪ L)ᶜ).X n) :
    ∃ (α : (integralRelativeCochains Kᶜ).X n) (β : (integralRelativeCochains Lᶜ).X n),
      (integralRelativeCochainMap (ContinuousMap.id X)
        (show (K ∪ L)ᶜ ⊆ Kᶜ from compl_subset_compl.mpr subset_union_left)).f n α +
      (integralRelativeCochainMap (ContinuousMap.id X)
        (show (K ∪ L)ᶜ ⊆ Lᶜ from compl_subset_compl.mpr subset_union_right)).f n β = φ := by
  have aux (C : Set X) (hC : C = Kᶜ ∩ Lᶜ)
      (hK : MapsTo (ContinuousMap.id X) C Kᶜ)
      (hL : MapsTo (ContinuousMap.id X) C Lᶜ)
      (ψ : (integralRelativeCochains C).X n) :
      ∃ (α : (integralRelativeCochains Kᶜ).X n) (β : (integralRelativeCochains Lᶜ).X n),
        (integralRelativeCochainMap (ContinuousMap.id X) hK).f n α +
        (integralRelativeCochainMap (ContinuousMap.id X) hL).f n β = ψ := by
    subst C
    exact exists_relative_cochain_inter_decomposition n Kᶜ Lᶜ ψ
  exact aux (K ∪ L)ᶜ (compl_union K L) _ _ φ

end DifferentialGeometry.Topology

end


noncomputable section

open CategoryTheory CategoryTheory.Limits Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem exists_cochain_relative_extension (n : ℕ) (A B : Set X)
    (φ : integralSingularCochain n B)
    (hφ : integralSingularCochainPullback n
      (singularSubspaceInclusion (subspaceIntersection A B)) φ = 0) :
    ∃ ψ : integralSingularCochain n X,
      integralSingularCochainPullback n (singularSubspaceInclusion A) ψ = 0 ∧
      integralSingularCochainPullback n (singularSubspaceInclusion B) ψ = φ := by
  classical
  let ψ : integralSingularCochain n X := (integralSingularChainBasis n X).constr ℕ
    (fun σ => if hσ : range (integralSingularSimplexEquiv n X σ) ⊆ B
      then φ (integralSimplexChain n (integralSingularSimplexRestriction n B σ hσ)) else 0)
  have hψ (σ : integralSingularSimplex n X) :
      ψ (integralSimplexChain n σ) =
        if hσ : range (integralSingularSimplexEquiv n X σ) ⊆ B
          then φ (integralSimplexChain n (integralSingularSimplexRestriction n B σ hσ)) else 0 := by
    change ((integralSingularChainBasis n X).constr ℕ _ : integralSingularCochain n X) _ = _
    rw [← integralSingularChainBasis_apply, Basis.constr_basis]
  refine ⟨ψ, ?_, ?_⟩
  · apply (cochain_pullback_eq_zero_iff n A ψ).2
    intro σ hA
    rw [hψ]
    split_ifs with hB
    · apply (cochain_pullback_eq_zero_iff n (subspaceIntersection A B) φ).1 hφ
      rintro _ ⟨t, rfl⟩
      change integralSingularSimplexEquiv n X σ t ∈ A
      exact hA ⟨t, rfl⟩
    · rfl
  · apply (integralSingularChainBasis n B).ext
    intro σ
    change ψ ((integralSingularChainMap (singularSubspaceInclusion B)).f n
      (integralSingularChainBasis n B σ)) = φ (integralSingularChainBasis n B σ)
    rw [integralSingularChainBasis_apply, integralSimplexChain_map, hψ]
    have hB : range (integralSingularSimplexEquiv n X
        (integralSingularSimplexMap n (singularSubspaceInclusion B) σ)) ⊆ B := by
      rintro _ ⟨t, rfl⟩
      rw [integralSingularSimplexMap_apply]
      exact (integralSingularSimplexEquiv n B σ t).property
    rw [dite_eq_left hB]
    congr 1

theorem integralRelativeCochainMap_subspace_surjective (n : ℕ) (A B : Set X) :
    Function.Surjective ((integralRelativeCochainMap (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B)).f n) := by
  intro φ
  have hφ : integralSingularCochainPullback n
      (singularSubspaceInclusion (subspaceIntersection A B))
      ((integralRelativeCochainInclusion (subspaceIntersection A B)).f n φ) = 0 := by
    exact congrArg (fun f : integralRelativeCochains (subspaceIntersection A B) ⟶
      integralSingularCochains (subspaceIntersection A B) => f.f n φ)
      (integralRelativeCochainInclusion_comp (subspaceIntersection A B))
  obtain ⟨ψ, hA, hB⟩ := exists_cochain_relative_extension n A B
    ((integralRelativeCochainInclusion (subspaceIntersection A B)).f n φ) hφ
  have hψ : ψ ∈ LinearMap.range ((integralRelativeCochainInclusion A).f n).hom := by
    rw [integralRelativeCochainInclusion_range]
    exact hA
  obtain ⟨α, rfl⟩ := hψ
  refine ⟨α, ?_⟩
  have hexact := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (integralRelativeCochainSequence_shortExact (subspaceIntersection A B)) n
  apply (ModuleCat.mono_iff_injective _).1 hexact.mono_f
  have hmap := integralRelativeCochainMap_inclusion (singularSubspaceInclusion B)
    (subspaceIntersection_mapsTo A B)
  exact (congrArg (fun f : integralRelativeCochains A ⟶ integralSingularCochains B => f.f n α)
    hmap).trans hB

end DifferentialGeometry.Topology

end


noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

theorem integralRelativeCochainMap_union_excision
    {X : Type u} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) :
    let i : C(B, ↥(A ∪ B)) :=
      ⟨fun x => ⟨x.val, Or.inr x.property⟩, continuous_subtype_val.subtype_mk _⟩
    let hf : MapsTo i (subspaceIntersection A B) (subspaceIntersection A (A ∪ B)) :=
      fun _ hx => hx
    QuasiIso (integralRelativeCochainMap i hf) := by
  intro i hf
  have hi : _root_.Topology.IsOpenEmbedding i :=
    .inclusion subset_union_right (hB.preimage continuous_subtype_val)
  have himage : i '' (subspaceIntersection A B)ᶜ =
      (subspaceIntersection A (A ∪ B))ᶜ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hxB : x.val ∈ B := x.property.resolve_left hx
      exact ⟨⟨x.val, hxB⟩, hx, Subtype.ext rfl⟩
  have hclosed : IsClosed (i '' (subspaceIntersection A B)ᶜ) := by
    rw [himage]
    exact (hA.preimage continuous_subtype_val).isClosed_compl
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have h := integralRelativeCohomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image
    n i hi (subspaceIntersection A B)ᶜ hclosed
  have H : ∀ hf' : MapsTo i ((subspaceIntersection A B)ᶜ)ᶜ
      (i '' (subspaceIntersection A B)ᶜ)ᶜ,
      Function.Bijective (integralRelativeCohomologyMap n i hf') := fun _ => h
  rw [himage, compl_compl, compl_compl] at H
  exact H hf

end DifferentialGeometry.Topology

end


noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

def integralTwoSetRelativeCochains (A B : Set X) : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  pullback (integralRelativeCochainInclusion A) (integralRelativeCochainInclusion B)

def integralTwoSetRelativeCochainDifference (A B : Set X) :
    integralTwoSetRelativeCochains A B ⟶
      integralRelativeCochains A ⊞ integralRelativeCochains B :=
  biprod.lift (pullback.fst _ _) (-(pullback.snd _ _))

private theorem cochain_inter_map_inclusion_left (A B : Set X) :
    integralRelativeCochainMap (ContinuousMap.id X)
        (show A ∩ B ⊆ A from inter_subset_left) ≫ integralRelativeCochainInclusion (A ∩ B) =
      integralRelativeCochainInclusion A := by
  erw [integralRelativeCochainMap_inclusion, integralSingularCochainMap_id, Category.comp_id]

private theorem cochain_inter_map_inclusion_right (A B : Set X) :
    integralRelativeCochainMap (ContinuousMap.id X)
        (show A ∩ B ⊆ B from inter_subset_right) ≫ integralRelativeCochainInclusion (A ∩ B) =
      integralRelativeCochainInclusion B := by
  erw [integralRelativeCochainMap_inclusion, integralSingularCochainMap_id, Category.comp_id]

private theorem cochain_inter_sum_inclusion (A B : Set X) :
    integralRelativeCochainInterSum A B ≫ integralRelativeCochainInclusion (A ∩ B) =
      biprod.desc (integralRelativeCochainInclusion A) (integralRelativeCochainInclusion B) := by
  apply biprod.hom_ext' <;>
    simp only [integralRelativeCochainInterSum, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
      biprod.inl_desc, biprod.inr_desc]
  · exact cochain_inter_map_inclusion_left A B
  · exact cochain_inter_map_inclusion_right A B

theorem integralTwoSetRelativeCochainDifference_comp_sum (A B : Set X) :
    integralTwoSetRelativeCochainDifference A B ≫ integralRelativeCochainInterSum A B = 0 := by
  let : Mono (integralRelativeCochainInclusion (A ∩ B)) :=
    (integralRelativeCochainSequence_shortExact (A ∩ B)).mono_f
  apply (cancel_mono (integralRelativeCochainInclusion (A ∩ B))).mp
  rw [Category.assoc, cochain_inter_sum_inclusion]
  unfold integralTwoSetRelativeCochainDifference integralTwoSetRelativeCochains
  rw [
    biprod.lift_desc, Preadditive.neg_comp, pullback.condition, add_neg_cancel, zero_comp]

private def twoSetRelativeCochainKernelFork (A B : Set X) :
    KernelFork (integralRelativeCochainInterSum A B) :=
  KernelFork.ofι (integralTwoSetRelativeCochainDifference A B)
    (integralTwoSetRelativeCochainDifference_comp_sum A B)

private def twoSetRelativeCochainKernelIsLimit (A B : Set X) :
    IsLimit (twoSetRelativeCochainKernelFork A B) := by
  unfold twoSetRelativeCochainKernelFork integralTwoSetRelativeCochains
  refine Fork.IsLimit.mk _ (fun s => pullback.lift
    (s.ι ≫ biprod.fst) (-(s.ι ≫ biprod.snd)) ?_) ?_ ?_
  · rw [Preadditive.neg_comp]
    apply eq_neg_of_add_eq_zero_left
    have h := KernelFork.condition s =≫ integralRelativeCochainInclusion (A ∩ B)
    rw [Category.assoc, cochain_inter_sum_inclusion, zero_comp,
      biprod.desc_eq, Preadditive.comp_add, ← Category.assoc, ← Category.assoc] at h
    exact h
  · intro s
    change _ ≫ integralTwoSetRelativeCochainDifference A B = s.ι
    apply biprod.hom_ext
    · unfold integralTwoSetRelativeCochainDifference
      erw [Category.assoc, biprod.lift_fst, pullback.lift_fst]
    · unfold integralTwoSetRelativeCochainDifference
      erw [Category.assoc, biprod.lift_snd, Preadditive.comp_neg, pullback.lift_snd, neg_neg]
  · intro s m h
    change m ≫ integralTwoSetRelativeCochainDifference A B = s.ι at h
    apply pullback.hom_ext
    · have h' := h =≫ (biprod.fst : integralRelativeCochains A ⊞
          integralRelativeCochains B ⟶ integralRelativeCochains A)
      unfold integralTwoSetRelativeCochainDifference at h'
      erw [Category.assoc, biprod.lift_fst] at h'
      rw [pullback.lift_fst]
      exact h'
    · have h' := h =≫ (biprod.snd : integralRelativeCochains A ⊞
          integralRelativeCochains B ⟶ integralRelativeCochains B)
      unfold integralTwoSetRelativeCochainDifference at h'
      erw [Category.assoc, biprod.lift_snd, Preadditive.comp_neg] at h'
      rw [pullback.lift_snd]
      exact neg_eq_iff_eq_neg.mp h'

def integralTwoSetRelativeCochainSequence (A B : Set X) :
    ShortComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (integralTwoSetRelativeCochainDifference A B)
    (integralRelativeCochainInterSum A B)
    (integralTwoSetRelativeCochainDifference_comp_sum A B)

theorem integralTwoSetRelativeCochainSequence_shortExact (A B : Set X) :
    (integralTwoSetRelativeCochainSequence A B).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := integralRelativeCochainInterSum_epi A B }
  · exact (integralTwoSetRelativeCochainSequence A B).exact_of_f_is_kernel
      (twoSetRelativeCochainKernelIsLimit A B)
  · exact Fork.IsLimit.mono (twoSetRelativeCochainKernelIsLimit A B)

def integralTwoSetRelativeCohomologyConnecting (n : ℕ) (A B : Set X) :
    integralRelativeCohomology n (A ∩ B) →ₗ[ℤ]
      (integralTwoSetRelativeCochains A B).homology (n + 1) :=
  ((integralTwoSetRelativeCochainSequence_shortExact A B).δ n (n + 1) (by simp)).hom

theorem integralTwoSetRelativeCohomology_exact_inter (n : ℕ) (A B : Set X) :
    Function.Exact
      (HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom
      (integralTwoSetRelativeCohomologyConnecting n A B) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralTwoSetRelativeCochainSequence_shortExact A B).homology_exact₃ n (n + 1) (by simp))

theorem integralTwoSetRelativeCohomology_exact_biprod (n : ℕ) (A B : Set X) :
    Function.Exact
      (HomologicalComplex.homologyMap (integralTwoSetRelativeCochainDifference A B) n).hom
      (HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralTwoSetRelativeCochainSequence_shortExact A B).homology_exact₂ n)

theorem integralTwoSetRelativeCohomology_exact_twoSet (n : ℕ) (A B : Set X) :
    Function.Exact (integralTwoSetRelativeCohomologyConnecting n A B)
      (HomologicalComplex.homologyMap (integralTwoSetRelativeCochainDifference A B) (n + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralTwoSetRelativeCochainSequence_shortExact A B).homology_exact₁ n (n + 1) (by simp))

end DifferentialGeometry.Topology

end


noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def integralTwoSetRelativeCochainMap (f : ContinuousMap X Y)
    {A B : Set X} {C D : Set Y} (hA : MapsTo f A C) (hB : MapsTo f B D) :
    integralTwoSetRelativeCochains C D ⟶ integralTwoSetRelativeCochains A B :=
  pullback.lift
    (pullback.fst (integralRelativeCochainInclusion C) (integralRelativeCochainInclusion D) ≫
      integralRelativeCochainMap f hA)
    (pullback.snd (integralRelativeCochainInclusion C) (integralRelativeCochainInclusion D) ≫
      integralRelativeCochainMap f hB) (by
    erw [Category.assoc, integralRelativeCochainMap_inclusion, ← Category.assoc,
      pullback.condition, Category.assoc, Category.assoc, integralRelativeCochainMap_inclusion])

theorem integralTwoSetRelativeCochainDifference_natural (f : ContinuousMap X Y)
    {A B : Set X} {C D : Set Y} (hA : MapsTo f A C) (hB : MapsTo f B D) :
    integralTwoSetRelativeCochainMap f hA hB ≫ integralTwoSetRelativeCochainDifference A B =
      integralTwoSetRelativeCochainDifference C D ≫
        biprod.map (integralRelativeCochainMap f hA) (integralRelativeCochainMap f hB) := by
  unfold integralTwoSetRelativeCochainMap integralTwoSetRelativeCochainDifference integralTwoSetRelativeCochains
  apply biprod.hom_ext
  · erw [Category.assoc, biprod.lift_fst, pullback.lift_fst,
      Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]
  · erw [Category.assoc, biprod.lift_snd, Preadditive.comp_neg, pullback.lift_snd,
      Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
      Preadditive.neg_comp]

def integralTwoSetRelativeCochainSequenceMap (f : ContinuousMap X Y)
    {A B : Set X} {C D : Set Y} (hA : MapsTo f A C) (hB : MapsTo f B D) :
    integralTwoSetRelativeCochainSequence C D ⟶ integralTwoSetRelativeCochainSequence A B where
  τ₁ := integralTwoSetRelativeCochainMap f hA hB
  τ₂ := biprod.map (integralRelativeCochainMap f hA) (integralRelativeCochainMap f hB)
  τ₃ := integralRelativeCochainMap f
    (show MapsTo f (A ∩ B) (C ∩ D) from fun _ hx => ⟨hA hx.1, hB hx.2⟩)
  comm₁₂ := integralTwoSetRelativeCochainDifference_natural f hA hB
  comm₂₃ := integralRelativeCochainInterSum_natural f hA hB

theorem integralTwoSetRelativeCohomologyConnecting_natural (n : ℕ) (f : ContinuousMap X Y)
    {A B : Set X} {C D : Set Y} (hA : MapsTo f A C) (hB : MapsTo f B D) :
    (HomologicalComplex.homologyMap (integralTwoSetRelativeCochainMap f hA hB) (n + 1)).hom.comp
        (integralTwoSetRelativeCohomologyConnecting n C D) =
      (integralTwoSetRelativeCohomologyConnecting n A B).comp
        (integralRelativeCohomologyMap n f
          (show MapsTo f (A ∩ B) (C ∩ D) from fun _ hx => ⟨hA hx.1, hB hx.2⟩)) := by
  exact congrArg ModuleCat.Hom.hom
    (HomologicalComplex.HomologySequence.δ_naturality (integralTwoSetRelativeCochainSequenceMap f hA hB)
      (integralTwoSetRelativeCochainSequence_shortExact C D)
      (integralTwoSetRelativeCochainSequence_shortExact A B) n (n + 1) (by simp))

def integralRelativeCochainUnionComparison (A B : Set X) :
    integralRelativeCochains (A ∪ B) ⟶ integralTwoSetRelativeCochains A B :=
  pullback.lift
    (integralRelativeCochainMap (ContinuousMap.id X)
      (show MapsTo (ContinuousMap.id X) A (A ∪ B) from fun _ hx => Or.inl hx))
    (integralRelativeCochainMap (ContinuousMap.id X)
      (show MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ hx => Or.inr hx)) (by
    rw [integralRelativeCochainMap_inclusion, integralRelativeCochainMap_inclusion])

theorem integralRelativeCochainUnionComparison_natural (f : ContinuousMap X Y)
    {A B : Set X} {C D : Set Y} (hA : MapsTo f A C) (hB : MapsTo f B D) :
    integralRelativeCochainUnionComparison C D ≫ integralTwoSetRelativeCochainMap f hA hB =
      integralRelativeCochainMap f
        (show MapsTo f (A ∪ B) (C ∪ D) from fun _ hx => hx.elim
          (fun h => Or.inl (hA h)) (fun h => Or.inr (hB h))) ≫
        integralRelativeCochainUnionComparison A B := by
  unfold integralRelativeCochainUnionComparison integralTwoSetRelativeCochainMap
    integralTwoSetRelativeCochains
  apply pullback.hom_ext
  · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    conv_rhs => rw [Category.assoc]
    erw [pullback.lift_fst,
      ← integralRelativeCochainMap_comp, ← integralRelativeCochainMap_comp]
    rfl
  · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    conv_rhs => rw [Category.assoc]
    erw [pullback.lift_snd,
      ← integralRelativeCochainMap_comp, ← integralRelativeCochainMap_comp]
    rfl

end DifferentialGeometry.Topology

end


noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private def twoSetCochainProjection (A B : Set X) :
    integralTwoSetRelativeCochains A B ⟶ integralRelativeCochains A := pullback.fst _ _

private def relativeCochainRestriction (A B : Set X) :
    integralRelativeCochains A ⟶ integralRelativeCochains (subspaceIntersection A B) :=
  integralRelativeCochainMap (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B)

private theorem twoSet_projection_restriction_zero (A B : Set X) :
    twoSetCochainProjection A B ≫ relativeCochainRestriction A B = 0 := by
  let : Mono (integralRelativeCochainInclusion (subspaceIntersection A B)) :=
    (integralRelativeCochainSequence_shortExact (subspaceIntersection A B)).mono_f
  apply (cancel_mono (integralRelativeCochainInclusion (subspaceIntersection A B))).mp
  unfold twoSetCochainProjection relativeCochainRestriction integralTwoSetRelativeCochains
  rw [Category.assoc, integralRelativeCochainMap_inclusion, ← Category.assoc, pullback.condition,
    Category.assoc, integralRelativeCochainInclusion_comp, comp_zero, zero_comp]

private def twoSetProjectionKernelIsLimit (A B : Set X) :
    IsLimit (KernelFork.ofι (twoSetCochainProjection A B)
      (twoSet_projection_restriction_zero A B)) := by
  let r := relativeCochainRestriction A B
  let ιA := integralRelativeCochainInclusion A
  let ιB := integralRelativeCochainInclusion B
  have hker (s : KernelFork r) :
      (s.ι ≫ ιA) ≫ integralSingularCochainMap (singularSubspaceInclusion B) = 0 := by
    have h := KernelFork.condition s =≫ integralRelativeCochainInclusion (subspaceIntersection A B)
    change (s.ι ≫ relativeCochainRestriction A B) ≫ _ = _ at h
    unfold relativeCochainRestriction at h
    rw [Category.assoc, integralRelativeCochainMap_inclusion, ← Category.assoc, zero_comp] at h
    exact h
  let b (s : KernelFork r) : s.pt ⟶ integralRelativeCochains B :=
    kernel.lift _ (s.ι ≫ ιA) (hker s)
  have hb (s : KernelFork r) : b s ≫ ιB = s.ι ≫ ιA := kernel.lift_ι _ _ _
  refine Fork.IsLimit.mk _ (fun s => pullback.lift s.ι (b s) (hb s).symm) ?_ ?_
  · intro s
    change pullback.lift s.ι (b s) (hb s).symm ≫ pullback.fst ιA ιB = s.ι
    exact pullback.lift_fst _ _ _
  · intro s m hm
    change m ≫ pullback.fst ιA ιB = s.ι at hm
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact hm
    · rw [pullback.lift_snd]
      have : Mono ιB := (integralRelativeCochainSequence_shortExact B).mono_f
      apply (cancel_mono ιB).mp
      erw [hb, Category.assoc, ← pullback.condition, ← Category.assoc, hm]

private def relativeUnionCochainInclusion (A B : Set X) :
    integralRelativeCochains (A ∪ B) ⟶ integralRelativeCochains A :=
  integralRelativeCochainMap (ContinuousMap.id X)
    (show MapsTo (ContinuousMap.id X) A (A ∪ B) from fun _ hx => Or.inl hx)

private theorem relative_union_inclusion_absolute (A B : Set X) :
    relativeUnionCochainInclusion A B ≫ integralRelativeCochainInclusion A =
      integralRelativeCochainInclusion (A ∪ B) := by
  unfold relativeUnionCochainInclusion
  rw [integralRelativeCochainMap_inclusion, integralSingularCochainMap_id, Category.comp_id]

private theorem relative_union_inclusion_restriction_zero (A B : Set X) :
    relativeUnionCochainInclusion A B ≫ relativeCochainRestriction A (A ∪ B) = 0 := by
  let : Mono (integralRelativeCochainInclusion (subspaceIntersection A (A ∪ B))) :=
    (integralRelativeCochainSequence_shortExact (subspaceIntersection A (A ∪ B))).mono_f
  apply (cancel_mono (integralRelativeCochainInclusion (subspaceIntersection A (A ∪ B)))).mp
  unfold relativeCochainRestriction
  rw [Category.assoc, integralRelativeCochainMap_inclusion, ← Category.assoc,
    relative_union_inclusion_absolute, integralRelativeCochainInclusion_comp, zero_comp]

private def relativeUnionCochainKernelIsLimit (A B : Set X) :
    IsLimit (KernelFork.ofι (relativeUnionCochainInclusion A B)
      (relative_union_inclusion_restriction_zero A B)) := by
  let r := relativeCochainRestriction A (A ∪ B)
  let ιA := integralRelativeCochainInclusion A
  let ιU := integralRelativeCochainInclusion (A ∪ B)
  have hker (s : KernelFork r) :
      (s.ι ≫ ιA) ≫ integralSingularCochainMap (singularSubspaceInclusion (A ∪ B)) = 0 := by
    have h := KernelFork.condition s =≫
      integralRelativeCochainInclusion (subspaceIntersection A (A ∪ B))
    change (s.ι ≫ relativeCochainRestriction A (A ∪ B)) ≫ _ = _ at h
    unfold relativeCochainRestriction at h
    rw [Category.assoc, integralRelativeCochainMap_inclusion, ← Category.assoc, zero_comp] at h
    exact h
  let b (s : KernelFork r) : s.pt ⟶ integralRelativeCochains (A ∪ B) :=
    kernel.lift _ (s.ι ≫ ιA) (hker s)
  have hb (s : KernelFork r) : b s ≫ ιU = s.ι ≫ ιA := kernel.lift_ι _ _ _
  refine Fork.IsLimit.mk _ b ?_ ?_
  · intro s
    change b s ≫ relativeUnionCochainInclusion A B = s.ι
    have : Mono ιA := (integralRelativeCochainSequence_shortExact A).mono_f
    apply (cancel_mono ιA).mp
    change (b s ≫ relativeUnionCochainInclusion A B) ≫ integralRelativeCochainInclusion A = _
    rw [Category.assoc, relative_union_inclusion_absolute]
    exact hb s
  · intro s m hm
    change m ≫ relativeUnionCochainInclusion A B = s.ι at hm
    have : Mono ιU := (integralRelativeCochainSequence_shortExact (A ∪ B)).mono_f
    apply (cancel_mono ιU).mp
    rw [hb]
    change m ≫ integralRelativeCochainInclusion (A ∪ B) = s.ι ≫ integralRelativeCochainInclusion A
    rw [← relative_union_inclusion_absolute, ← Category.assoc, hm]

private def relativeUnionRestrictionSequence (A B : Set X) :
    ShortComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (relativeUnionCochainInclusion A B) (relativeCochainRestriction A (A ∪ B))
    (relative_union_inclusion_restriction_zero A B)

private def twoSetRelativeRestrictionSequence (A B : Set X) :
    ShortComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (twoSetCochainProjection A B) (relativeCochainRestriction A B)
    (twoSet_projection_restriction_zero A B)

private def subspaceUnionInclusion (A B : Set X) : C(B, ↥(A ∪ B)) :=
  ⟨fun x => ⟨x.val, Or.inr x.property⟩, continuous_subtype_val.subtype_mk _⟩

private def relativeUnionRestrictionComparison (A B : Set X) :
    relativeUnionRestrictionSequence A B ⟶ twoSetRelativeRestrictionSequence A B where
  τ₁ := integralRelativeCochainUnionComparison A B
  τ₂ := 𝟙 _
  τ₃ := integralRelativeCochainMap (subspaceUnionInclusion A B)
    (show MapsTo (subspaceUnionInclusion A B) (subspaceIntersection A B)
      (subspaceIntersection A (A ∪ B)) from fun _ hx => hx)
  comm₁₂ := by
    change integralRelativeCochainUnionComparison A B ≫ twoSetCochainProjection A B =
      relativeUnionCochainInclusion A B ≫ 𝟙 _
    unfold integralRelativeCochainUnionComparison twoSetCochainProjection
    erw [pullback.lift_fst, Category.comp_id]
    rfl
  comm₂₃ := by
    change 𝟙 _ ≫ relativeCochainRestriction A B = relativeCochainRestriction A (A ∪ B) ≫ _
    rw [Category.id_comp]
    unfold relativeCochainRestriction
    rw [← integralRelativeCochainMap_comp]
    rfl

private theorem relative_restriction_epi (A B : Set X) : Epi (relativeCochainRestriction A B) :=
  HomologicalComplex.epi_of_epi_f _ (fun n => (ModuleCat.epi_iff_surjective _).2
    (integralRelativeCochainMap_subspace_surjective n A B))

private theorem relativeUnionRestrictionSequence_shortExact (A B : Set X) :
    (relativeUnionRestrictionSequence A B).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := relative_restriction_epi A (A ∪ B) }
  · exact (relativeUnionRestrictionSequence A B).exact_of_f_is_kernel
      (relativeUnionCochainKernelIsLimit A B)
  · exact Fork.IsLimit.mono (relativeUnionCochainKernelIsLimit A B)

private theorem twoSetRelativeRestrictionSequence_shortExact (A B : Set X) :
    (twoSetRelativeRestrictionSequence A B).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := relative_restriction_epi A B }
  · exact (twoSetRelativeRestrictionSequence A B).exact_of_f_is_kernel
      (twoSetProjectionKernelIsLimit A B)
  · exact Fork.IsLimit.mono (twoSetProjectionKernelIsLimit A B)

theorem integralRelativeCochainUnionComparison_quasiIso (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) : QuasiIso (integralRelativeCochainUnionComparison A B) := by
  let φ := relativeUnionRestrictionComparison A B
  let F := HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.up ℕ)
  have h₃ : QuasiIso φ.τ₃ := integralRelativeCochainMap_union_excision A B hA hB
  have h₂ : QuasiIso φ.τ₂ := inferInstanceAs (QuasiIso (𝟙 (integralRelativeCochains A)))
  have h := HomologicalComplex.HomologySequence.quasiIso_τ₃
    (F.mapShortComplex.map (ShortComplex.opMap φ))
    ((twoSetRelativeRestrictionSequence_shortExact A B).op.map_of_exact F)
    ((relativeUnionRestrictionSequence_shortExact A B).op.map_of_exact F)
    ((HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₃).mpr h₃)
    ((HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₂).mpr h₂)
  exact (HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₁).mp h

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

def integralRelativeMayerVietorisConnecting (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) :
    integralRelativeCohomology n (A ∩ B) →ₗ[ℤ] integralRelativeCohomology (n + 1) (A ∪ B) := by
  let := integralRelativeCochainUnionComparison_quasiIso A B hA hB
  exact (asIso (HomologicalComplex.homologyMap
    (integralRelativeCochainUnionComparison A B) (n + 1))).inv.hom.comp
      (integralTwoSetRelativeCohomologyConnecting n A B)

theorem integralRelativeMayerVietorisConnecting_comparison (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) :
    (HomologicalComplex.homologyMap (integralRelativeCochainUnionComparison A B) (n + 1)).hom.comp
        (integralRelativeMayerVietorisConnecting n A B hA hB) =
      integralTwoSetRelativeCohomologyConnecting n A B := by
  let := integralRelativeCochainUnionComparison_quasiIso A B hA hB
  let e := asIso (HomologicalComplex.homologyMap
    (integralRelativeCochainUnionComparison A B) (n + 1))
  change e.hom.hom.comp (e.inv.hom.comp _) = _
  rw [← LinearMap.comp_assoc]
  change (e.inv ≫ e.hom).hom.comp _ = _
  rw [Iso.inv_hom_id]
  rfl

theorem integralRelativeCohomology_mayerVietoris_exact_inter (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) :
    Function.Exact
      (HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom
      (integralRelativeMayerVietorisConnecting n A B hA hB) := by
  let := integralRelativeCochainUnionComparison_quasiIso A B hA hB
  have hinj : Function.Injective
      (HomologicalComplex.homologyMap (integralRelativeCochainUnionComparison A B) (n + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  intro α
  rw [← (integralTwoSetRelativeCohomology_exact_inter n A B) α]
  have h := LinearMap.congr_fun (integralRelativeMayerVietorisConnecting_comparison n A B hA hB) α
  constructor
  · intro hα
    erw [LinearMap.comp_apply, hα, map_zero] at h
    exact h.symm
  · intro hα
    apply hinj
    erw [map_zero, ← hα]
    exact h

def integralRelativeCochainUnionDifference (A B : Set X) :
    integralRelativeCochains (A ∪ B) ⟶ integralRelativeCochains A ⊞ integralRelativeCochains B :=
  biprod.lift
    (integralRelativeCochainMap (ContinuousMap.id X)
      (show MapsTo (ContinuousMap.id X) A (A ∪ B) from fun _ hx => Or.inl hx))
    (-(integralRelativeCochainMap (ContinuousMap.id X)
      (show MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ hx => Or.inr hx)))

theorem integralRelativeCochainUnionComparison_difference (A B : Set X) :
    integralRelativeCochainUnionComparison A B ≫ integralTwoSetRelativeCochainDifference A B =
      integralRelativeCochainUnionDifference A B := by
  unfold integralRelativeCochainUnionComparison integralTwoSetRelativeCochainDifference
    integralRelativeCochainUnionDifference integralTwoSetRelativeCochains
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst, pullback.lift_fst, biprod.lift_fst]
  · rw [Category.assoc, biprod.lift_snd, Preadditive.comp_neg, pullback.lift_snd, biprod.lift_snd]

theorem integralRelativeCohomology_mayerVietoris_exact_union (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) :
    Function.Exact (integralRelativeMayerVietorisConnecting n A B hA hB)
      (HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) (n + 1)).hom := by
  let := integralRelativeCochainUnionComparison_quasiIso A B hA hB
  let q := (HomologicalComplex.homologyMap
    (integralRelativeCochainUnionComparison A B) (n + 1)).hom
  have hinj : Function.Injective q := (ModuleCat.mono_iff_injective _).1 inferInstance
  have hcomp := HomologicalComplex.homologyMap_comp
    (integralRelativeCochainUnionComparison A B) (integralTwoSetRelativeCochainDifference A B) (n + 1)
  rw [integralRelativeCochainUnionComparison_difference] at hcomp
  intro α
  have heq : (HomologicalComplex.homologyMap
      (integralRelativeCochainUnionDifference A B) (n + 1)).hom α =
      (HomologicalComplex.homologyMap
        (integralTwoSetRelativeCochainDifference A B) (n + 1)).hom (q α) :=
    congrArg (fun f => ModuleCat.Hom.hom f α) hcomp
  rw [heq, (integralTwoSetRelativeCohomology_exact_twoSet n A B) (q α)]
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨β, hinj ?_⟩
    exact (LinearMap.congr_fun
      (integralRelativeMayerVietorisConnecting_comparison n A B hA hB) β).trans hβ
  · rintro ⟨β, rfl⟩
    exact ⟨β, (LinearMap.congr_fun
      (integralRelativeMayerVietorisConnecting_comparison n A B hA hB) β).symm⟩

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralRelativeMayerVietorisConnecting_natural (n : ℕ) (f : ContinuousMap X Y)
    {A B : Set X} {C D : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (hC : IsOpen C) (hD : IsOpen D) (hfA : MapsTo f A C) (hfB : MapsTo f B D) :
    (integralRelativeCohomologyMap (n + 1) f
      (show MapsTo f (A ∪ B) (C ∪ D) from fun _ hx => hx.elim
        (fun h => Or.inl (hfA h)) (fun h => Or.inr (hfB h)))).comp
        (integralRelativeMayerVietorisConnecting n C D hC hD) =
      (integralRelativeMayerVietorisConnecting n A B hA hB).comp
        (integralRelativeCohomologyMap n f
          (show MapsTo f (A ∩ B) (C ∩ D) from fun _ hx => ⟨hfA hx.1, hfB hx.2⟩)) := by
  let := integralRelativeCochainUnionComparison_quasiIso A B hA hB
  have hinj : Function.Injective
      (HomologicalComplex.homologyMap (integralRelativeCochainUnionComparison A B) (n + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hq := congrArg (fun g => HomologicalComplex.homologyMap g (n + 1))
    (integralRelativeCochainUnionComparison_natural f hfA hfB)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hq
  have hd := integralTwoSetRelativeCohomologyConnecting_natural n f hfA hfB
  ext α
  apply hinj
  have hqα := congrArg (fun g => ModuleCat.Hom.hom g
    (integralRelativeMayerVietorisConnecting n C D hC hD α)) hq
  have hc := LinearMap.congr_fun (integralRelativeMayerVietorisConnecting_comparison n C D hC hD) α
  have ha := LinearMap.congr_fun (integralRelativeMayerVietorisConnecting_comparison n A B hA hB)
    (integralRelativeCohomologyMap n f
      (show MapsTo f (A ∩ B) (C ∩ D) from fun _ hx => ⟨hfA hx.1, hfB hx.2⟩) α)
  exact hqα.symm.trans ((congrArg
    (HomologicalComplex.homologyMap (integralTwoSetRelativeCochainMap f hfA hfB) (n + 1)).hom hc).trans
      ((LinearMap.congr_fun hd α).trans ha.symm))

theorem integralRelativeCohomology_mayerVietoris_exact_biprod (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) :
    Function.Exact
      (HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) n).hom
      (HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom := by
  let := integralRelativeCochainUnionComparison_quasiIso A B hA hB
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (integralRelativeCochainUnionComparison A B) n).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hcomp := HomologicalComplex.homologyMap_comp
    (integralRelativeCochainUnionComparison A B) (integralTwoSetRelativeCochainDifference A B) n
  rw [integralRelativeCochainUnionComparison_difference] at hcomp
  intro α
  rw [(integralTwoSetRelativeCohomology_exact_biprod n A B) α]
  constructor
  · rintro ⟨β, hβ⟩
    obtain ⟨γ, hγ⟩ := hsurj β
    refine ⟨γ, ?_⟩
    have h := congrArg (fun g => ModuleCat.Hom.hom g γ) hcomp
    change _ = (HomologicalComplex.homologyMap (integralTwoSetRelativeCochainDifference A B) n).hom
      ((HomologicalComplex.homologyMap (integralRelativeCochainUnionComparison A B) n).hom γ) at h
    rw [hγ] at h
    exact h.trans hβ
  · rintro ⟨β, hβ⟩
    refine ⟨(HomologicalComplex.homologyMap (integralRelativeCochainUnionComparison A B) n).hom β, ?_⟩
    exact (congrArg (fun g => ModuleCat.Hom.hom g β) hcomp).symm.trans hβ

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

def integralCohomologyWithSupportMayerVietorisConnecting (n : ℕ) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) :
    integralRelativeCohomology n (K ∪ L)ᶜ →ₗ[ℤ]
      integralRelativeCohomology (n + 1) (K ∩ L)ᶜ :=
  (eqToHom (congrArg (fun A : Set X => integralRelativeCohomology (n + 1) A)
    (compl_inter K L).symm)).hom.comp
    ((integralRelativeMayerVietorisConnecting n Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl).comp
      (eqToHom (congrArg (fun A : Set X => integralRelativeCohomology n A) (compl_union K L))).hom)

end DifferentialGeometry.Topology

end
