module

public import DifferentialGeometry.Topology.Homology.RelativeCochainMayerVietoris

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem homology_biprod_decomposition (n : ℕ)
    (A B : CochainComplex (ModuleCat.{u} ℤ) ℕ) (x : (A ⊞ B).homology n) :
    (HomologicalComplex.homologyMap (biprod.inl : A ⟶ A ⊞ B) n).hom
        ((HomologicalComplex.homologyMap (biprod.fst : A ⊞ B ⟶ A) n).hom x) +
      (HomologicalComplex.homologyMap (biprod.inr : B ⟶ A ⊞ B) n).hom
        ((HomologicalComplex.homologyMap (biprod.snd : A ⊞ B ⟶ B) n).hom x) = x := by
  have h := congrArg (fun f : A ⊞ B ⟶ A ⊞ B =>
    (HomologicalComplex.homologyMap f n).hom x) (biprod.total (X := A) (Y := B))
  simpa only [HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_id, ModuleCat.hom_add, ModuleCat.hom_comp,
    LinearMap.add_apply, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

private theorem homology_interSum_inl (n : ℕ) (A B : Set X)
    (a : integralRelativeCohomology n A) :
    (HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom
      ((HomologicalComplex.homologyMap
        (biprod.inl : integralRelativeCochains A ⟶
          integralRelativeCochains A ⊞ integralRelativeCochains B) n).hom a) =
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) (A ∩ B) A from fun _ hx => hx.1) a := by
  have h := congrArg (fun f : integralRelativeCochains A ⟶ integralRelativeCochains (A ∩ B) =>
    (HomologicalComplex.homologyMap f n).hom a)
    (biprod.inl_desc
      (integralRelativeCochainMap (ContinuousMap.id X) (show A ∩ B ⊆ A from inter_subset_left))
      (integralRelativeCochainMap (ContinuousMap.id X) (show A ∩ B ⊆ B from inter_subset_right)))
  rw [HomologicalComplex.homologyMap_comp] at h
  exact h

private theorem homology_interSum_inr (n : ℕ) (A B : Set X)
    (b : integralRelativeCohomology n B) :
    (HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom
      ((HomologicalComplex.homologyMap
        (biprod.inr : integralRelativeCochains B ⟶
          integralRelativeCochains A ⊞ integralRelativeCochains B) n).hom b) =
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) (A ∩ B) B from fun _ hx => hx.2) b := by
  have h := congrArg (fun f : integralRelativeCochains B ⟶ integralRelativeCochains (A ∩ B) =>
    (HomologicalComplex.homologyMap f n).hom b)
    (biprod.inr_desc
      (integralRelativeCochainMap (ContinuousMap.id X) (show A ∩ B ⊆ A from inter_subset_left))
      (integralRelativeCochainMap (ContinuousMap.id X) (show A ∩ B ⊆ B from inter_subset_right)))
  rw [HomologicalComplex.homologyMap_comp] at h
  exact h

private theorem integralRelativeCochainInterSum_homology_image_iff (n : ℕ) (A B : Set X)
    (x : integralRelativeCohomology n (A ∩ B)) :
    (∃ y : (integralRelativeCochains A ⊞ integralRelativeCochains B).homology n,
      (HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom y = x) ↔
    ∃ a : integralRelativeCohomology n A, ∃ b : integralRelativeCohomology n B,
      integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) (A ∩ B) A from fun _ hx => hx.1) a +
        integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) (A ∩ B) B from fun _ hx => hx.2) b = x := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(HomologicalComplex.homologyMap
      (biprod.fst : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶ _) n).hom y,
      (HomologicalComplex.homologyMap
      (biprod.snd : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶ _) n).hom y, ?_⟩
    erw [← homology_interSum_inl n A B, ← homology_interSum_inr n A B, ← map_add,
      homology_biprod_decomposition]
    rfl
  · rintro ⟨a, b, hab⟩
    refine ⟨(HomologicalComplex.homologyMap
      (biprod.inl : integralRelativeCochains A ⟶ integralRelativeCochains A ⊞
        integralRelativeCochains B) n).hom a +
      (HomologicalComplex.homologyMap
      (biprod.inr : integralRelativeCochains B ⟶ integralRelativeCochains A ⊞
        integralRelativeCochains B) n).hom b, ?_⟩
    rw [map_add, homology_interSum_inl, homology_interSum_inr]
    exact hab

private theorem homology_unionDifference_fst (n : ℕ) (A B : Set X)
    (x : integralRelativeCohomology n (A ∪ B)) :
    (HomologicalComplex.homologyMap
      (biprod.fst : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶
        integralRelativeCochains A) n).hom
      ((HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) n).hom x) =
    integralRelativeCohomologyMap n (ContinuousMap.id X)
      (show MapsTo (ContinuousMap.id X) A (A ∪ B) from fun _ hx => Or.inl hx) x := by
  have h := congrArg (fun f : integralRelativeCochains (A ∪ B) ⟶ integralRelativeCochains A =>
    (HomologicalComplex.homologyMap f n).hom x)
    (biprod.lift_fst
      (integralRelativeCochainMap (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) A (A ∪ B) from fun _ hx => Or.inl hx))
      (-(integralRelativeCochainMap (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ hx => Or.inr hx))))
  rw [HomologicalComplex.homologyMap_comp] at h
  exact h

private theorem homology_unionDifference_snd (n : ℕ) (A B : Set X)
    (x : integralRelativeCohomology n (A ∪ B)) :
    (HomologicalComplex.homologyMap
      (biprod.snd : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶
        integralRelativeCochains B) n).hom
      ((HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) n).hom x) =
    -integralRelativeCohomologyMap n (ContinuousMap.id X)
      (show MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ hx => Or.inr hx) x := by
  have h := congrArg (fun f : integralRelativeCochains (A ∪ B) ⟶ integralRelativeCochains B =>
    (HomologicalComplex.homologyMap f n).hom x)
    (biprod.lift_snd
      (integralRelativeCochainMap (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) A (A ∪ B) from fun _ hx => Or.inl hx))
      (-(integralRelativeCochainMap (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ hx => Or.inr hx))))
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_neg] at h
  exact h

private theorem integralRelativeCochainUnionDifference_homology_eq_zero_iff (n : ℕ) (A B : Set X)
    (x : integralRelativeCohomology n (A ∪ B)) :
    (HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) n).hom x = 0 ↔
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) A (A ∪ B) from fun _ hx => Or.inl hx) x = 0 ∧
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ hx => Or.inr hx) x = 0 := by
  constructor
  · intro hx
    have hA := homology_unionDifference_fst n A B x
    have hB := homology_unionDifference_snd n A B x
    rw [hx, map_zero] at hA hB
    exact ⟨hA.symm, neg_eq_zero.mp hB.symm⟩
  · rintro ⟨hA, hB⟩
    have h := homology_biprod_decomposition n (integralRelativeCochains A)
      (integralRelativeCochains B)
      ((HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) n).hom x)
    erw [homology_unionDifference_fst, homology_unionDifference_snd, hA, hB,
      neg_zero, map_zero, map_zero, add_zero] at h
    exact h.symm


private theorem homology_biprod_fst_add (n : ℕ)
    (A B : CochainComplex (ModuleCat.{u} ℤ) ℕ) (a : A.homology n) (b : B.homology n) :
    (HomologicalComplex.homologyMap (biprod.fst : A ⊞ B ⟶ A) n).hom
      ((HomologicalComplex.homologyMap (biprod.inl : A ⟶ A ⊞ B) n).hom a +
        (HomologicalComplex.homologyMap (biprod.inr : B ⟶ A ⊞ B) n).hom b) = a := by
  have ha := congrArg (fun f : A ⟶ A => (HomologicalComplex.homologyMap f n).hom a)
    (biprod.inl_fst (X := A) (Y := B))
  have hb := congrArg (fun f : B ⟶ A => (HomologicalComplex.homologyMap f n).hom b)
    (biprod.inr_fst (X := A) (Y := B))
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at ha
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_zero] at hb
  rw [map_add]
  exact (congrArg₂ (fun x y : A.homology n => x + y) ha hb).trans (add_zero a)

private theorem homology_biprod_snd_add (n : ℕ)
    (A B : CochainComplex (ModuleCat.{u} ℤ) ℕ) (a : A.homology n) (b : B.homology n) :
    (HomologicalComplex.homologyMap (biprod.snd : A ⊞ B ⟶ B) n).hom
      ((HomologicalComplex.homologyMap (biprod.inl : A ⟶ A ⊞ B) n).hom a +
        (HomologicalComplex.homologyMap (biprod.inr : B ⟶ A ⊞ B) n).hom b) = b := by
  have ha := congrArg (fun f : A ⟶ B => (HomologicalComplex.homologyMap f n).hom a)
    (biprod.inl_snd (X := A) (Y := B))
  have hb := congrArg (fun f : B ⟶ B => (HomologicalComplex.homologyMap f n).hom b)
    (biprod.inr_snd (X := A) (Y := B))
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_zero] at ha
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at hb
  rw [map_add]
  exact (congrArg₂ (fun x y : B.homology n => x + y) ha hb).trans (zero_add b)

private theorem integralRelativeMayerVietoris_middle_exact_elementwise (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B)
    (a : integralRelativeCohomology n A) (b : integralRelativeCohomology n B) :
    integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) (A ∩ B) A from fun _ hx => hx.1) a +
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) (A ∩ B) B from fun _ hx => hx.2) b = 0 ↔
    ∃ γ : integralRelativeCohomology n (A ∪ B),
      integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) A (A ∪ B) from fun _ hx => Or.inl hx) γ = a ∧
      -integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ hx => Or.inr hx) γ = b := by
  let y := (HomologicalComplex.homologyMap
    (biprod.inl : integralRelativeCochains A ⟶ integralRelativeCochains A ⊞
      integralRelativeCochains B) n).hom a +
    (HomologicalComplex.homologyMap
    (biprod.inr : integralRelativeCochains B ⟶ integralRelativeCochains A ⊞
      integralRelativeCochains B) n).hom b
  have hy : (HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom y =
      integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) (A ∩ B) A from fun _ hx => hx.1) a +
        integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) (A ∩ B) B from fun _ hx => hx.2) b := by
    dsimp only [y]
    rw [map_add, homology_interSum_inl, homology_interSum_inr]
    rfl
  have hF := homology_biprod_fst_add n (integralRelativeCochains A)
    (integralRelativeCochains B) a b
  have hS := homology_biprod_snd_add n (integralRelativeCochains A)
    (integralRelativeCochains B) a b
  erw [← hy, (integralRelativeCohomology_mayerVietoris_exact_biprod n A B hA hB) y]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_, ?_⟩
    · have h := homology_unionDifference_fst n A B γ
      rw [hγ] at h
      exact h.symm.trans hF
    · have h := homology_unionDifference_snd n A B γ
      rw [hγ] at h
      exact h.symm.trans hS
  · rintro ⟨γ, hγA, hγB⟩
    refine ⟨γ, ?_⟩
    have h := homology_biprod_decomposition n (integralRelativeCochains A)
      (integralRelativeCochains B)
      ((HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) n).hom γ)
    erw [homology_unionDifference_fst, homology_unionDifference_snd, hγA, hγB] at h
    exact h.symm

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

private theorem exact_transport_middle_right
    {M N N' P P' : ModuleCat.{u} ℤ} (eN : N' = N) (eP : P = P')
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] P) (h : Function.Exact f g) :
    Function.Exact ((eqToHom eN.symm).hom.comp f)
      ((eqToHom eP).hom.comp (g.comp (eqToHom eN).hom)) := by
  subst N'
  subst P'
  exact h

private theorem exact_transport_left_middle
    {M M' N N' P : ModuleCat.{u} ℤ} (eM : M' = M) (eN : N = N')
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] P) (h : Function.Exact f g) :
    Function.Exact ((eqToHom eN).hom.comp (f.comp (eqToHom eM).hom))
      (g.comp (eqToHom eN.symm).hom) := by
  subst M'
  subst N'
  exact h

variable {X : Type u} [TopologicalSpace X]

private def supportSum (n : ℕ) (K L : Set X) :
    (integralRelativeCochains Kᶜ ⊞ integralRelativeCochains Lᶜ).homology n →ₗ[ℤ]
      integralRelativeCohomology n (K ∪ L)ᶜ :=
  (eqToHom (congrArg (integralRelativeCohomology n) (compl_union K L).symm)).hom.comp
    (HomologicalComplex.homologyMap (integralRelativeCochainInterSum Kᶜ Lᶜ) n).hom

private def supportDifference (n : ℕ) (K L : Set X) :
    integralRelativeCohomology n (K ∩ L)ᶜ →ₗ[ℤ]
      (integralRelativeCochains Kᶜ ⊞ integralRelativeCochains Lᶜ).homology n :=
  (HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference Kᶜ Lᶜ) n).hom.comp
    (eqToHom (congrArg (integralRelativeCohomology n) (compl_inter K L))).hom

private theorem support_exact_union (n : ℕ) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) :
    Function.Exact (supportSum n K L)
      (integralCohomologyWithSupportMayerVietorisConnecting n K L hK hL) :=
  exact_transport_middle_right
    (congrArg (integralRelativeCohomology n) (compl_union K L))
    (congrArg (integralRelativeCohomology (n + 1)) (compl_inter K L).symm)
    _ _ (integralRelativeCohomology_mayerVietoris_exact_inter n Kᶜ Lᶜ
      hK.isOpen_compl hL.isOpen_compl)

private theorem support_exact_inter (n : ℕ) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) :
    Function.Exact (integralCohomologyWithSupportMayerVietorisConnecting n K L hK hL)
      (supportDifference (n + 1) K L) :=
  exact_transport_left_middle
    (congrArg (integralRelativeCohomology n) (compl_union K L))
    (congrArg (integralRelativeCohomology (n + 1)) (compl_inter K L).symm)
    _ _ (integralRelativeCohomology_mayerVietoris_exact_union n Kᶜ Lᶜ
      hK.isOpen_compl hL.isOpen_compl)

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem relative_sum_image_cast (n : ℕ) (A B C : Set X)
    (e : C = A ∩ B) (hA : MapsTo (ContinuousMap.id X) C A)
    (hB : MapsTo (ContinuousMap.id X) C B) (x : integralRelativeCohomology n C) :
    (∃ y : (integralRelativeCochains A ⊞ integralRelativeCochains B).homology n,
      (eqToHom (congrArg (integralRelativeCohomology n) e.symm)).hom
        ((HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom y) = x) ↔
    ∃ a : integralRelativeCohomology n A, ∃ b : integralRelativeCohomology n B,
      integralRelativeCohomologyMap n (ContinuousMap.id X) hA a +
        integralRelativeCohomologyMap n (ContinuousMap.id X) hB b = x := by
  subst C
  exact integralRelativeCochainInterSum_homology_image_iff n A B x

theorem integralCohomologyWithSupport_mayerVietoris_exact_union
    (n : ℕ) (K L : Set X) (hK : IsClosed K) (hL : IsClosed L)
    (x : integralRelativeCohomology n (K ∪ L)ᶜ) :
    integralCohomologyWithSupportMayerVietorisConnecting n K L hK hL x = 0 ↔
      ∃ a : integralRelativeCohomology n Kᶜ, ∃ b : integralRelativeCohomology n Lᶜ,
        integralRelativeCohomologyMap n (ContinuousMap.id X)
            (show MapsTo (ContinuousMap.id X) (K ∪ L)ᶜ Kᶜ from
              compl_subset_compl.mpr subset_union_left) a +
          integralRelativeCohomologyMap n (ContinuousMap.id X)
            (show MapsTo (ContinuousMap.id X) (K ∪ L)ᶜ Lᶜ from
              compl_subset_compl.mpr subset_union_right) b = x := by
  rw [support_exact_union n K L hK hL x]
  exact relative_sum_image_cast n Kᶜ Lᶜ (K ∪ L)ᶜ (compl_union K L) _ _ x

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem relative_difference_kernel_cast (n : ℕ) (A B C : Set X)
    (e : C = A ∪ B) (hA : MapsTo (ContinuousMap.id X) A C)
    (hB : MapsTo (ContinuousMap.id X) B C) (x : integralRelativeCohomology n C) :
    (HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) n).hom
      ((eqToHom (congrArg (integralRelativeCohomology n) e)).hom x) = 0 ↔
      integralRelativeCohomologyMap n (ContinuousMap.id X) hA x = 0 ∧
        integralRelativeCohomologyMap n (ContinuousMap.id X) hB x = 0 := by
  subst C
  exact integralRelativeCochainUnionDifference_homology_eq_zero_iff n A B x

theorem integralCohomologyWithSupport_mayerVietoris_exact_inter
    (n : ℕ) (K L : Set X) (hK : IsClosed K) (hL : IsClosed L)
    (x : integralRelativeCohomology (n + 1) (K ∩ L)ᶜ) :
    (integralRelativeCohomologyMap (n + 1) (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) Kᶜ (K ∩ L)ᶜ from
          compl_subset_compl.mpr inter_subset_left) x = 0 ∧
      integralRelativeCohomologyMap (n + 1) (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) Lᶜ (K ∩ L)ᶜ from
          compl_subset_compl.mpr inter_subset_right) x = 0) ↔
      ∃ y : integralRelativeCohomology n (K ∪ L)ᶜ,
        integralCohomologyWithSupportMayerVietorisConnecting n K L hK hL y = x := by
  rw [← relative_difference_kernel_cast (n + 1) Kᶜ Lᶜ (K ∩ L)ᶜ (compl_inter K L)]
  exact support_exact_inter n K L hK hL x

end DifferentialGeometry.Topology

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Set
universe u
namespace DifferentialGeometry.Topology
variable {X : Type u} [TopologicalSpace X]

theorem integralCohomologyWithSupport_mayerVietoris_middle_exact
    (n : ℕ) (K L : Set X) (hK : IsClosed K) (hL : IsClosed L)
    (a : integralRelativeCohomology n Kᶜ) (b : integralRelativeCohomology n Lᶜ) :
    integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) (K ∪ L)ᶜ Kᶜ from
          compl_subset_compl.mpr subset_union_left) a +
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) (K ∪ L)ᶜ Lᶜ from
          compl_subset_compl.mpr subset_union_right) b = 0 ↔
    ∃ γ : integralRelativeCohomology n (K ∩ L)ᶜ,
      integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) Kᶜ (K ∩ L)ᶜ from
            compl_subset_compl.mpr inter_subset_left) γ = a ∧
      -integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) Lᶜ (K ∩ L)ᶜ from
            compl_subset_compl.mpr inter_subset_right) γ = b := by
  have aux (C D : Set X) (eC : C = Kᶜ ∩ Lᶜ) (eD : D = Kᶜ ∪ Lᶜ)
      (hCK : MapsTo (ContinuousMap.id X) C Kᶜ)
      (hCL : MapsTo (ContinuousMap.id X) C Lᶜ)
      (hKD : MapsTo (ContinuousMap.id X) Kᶜ D)
      (hLD : MapsTo (ContinuousMap.id X) Lᶜ D) :
      integralRelativeCohomologyMap n (ContinuousMap.id X) hCK a +
        integralRelativeCohomologyMap n (ContinuousMap.id X) hCL b = 0 ↔
      ∃ γ : integralRelativeCohomology n D,
        integralRelativeCohomologyMap n (ContinuousMap.id X) hKD γ = a ∧
          -integralRelativeCohomologyMap n (ContinuousMap.id X) hLD γ = b := by
    subst C
    subst D
    exact integralRelativeMayerVietoris_middle_exact_elementwise n Kᶜ Lᶜ
      hK.isOpen_compl hL.isOpen_compl a b
  exact aux (K ∪ L)ᶜ (K ∩ L)ᶜ (compl_union K L) (compl_inter K L) _ _ _ _

end DifferentialGeometry.Topology
end

noncomputable section

open CategoryTheory Set

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

private theorem relative_cohomology_map_eqToHom
    {Y : Type u} [TopologicalSpace Y] (n : ℕ) (f : ContinuousMap X Y)
    {A A' : Set X} {B B' : Set Y} (eA : A = A') (eB : B = B')
    (hf : MapsTo f A B) (hf' : MapsTo f A' B') :
    (eqToHom (congrArg (integralRelativeCohomology n) eA)).hom.comp
        (integralRelativeCohomologyMap n f hf) =
      (integralRelativeCohomologyMap n f hf').comp
        (eqToHom (congrArg (integralRelativeCohomology n) eB)).hom := by
  subst A'
  subst B'
  ext α
  rfl

theorem integralCohomologyWithSupportMayerVietorisConnecting_map (n : ℕ)
    (f : ContinuousMap X Y) (K L : Set X) (P Q : Set Y)
    (hK : IsClosed K) (hL : IsClosed L) (hP : IsClosed P) (hQ : IsClosed Q)
    (hfK : MapsTo f Kᶜ Pᶜ) (hfL : MapsTo f Lᶜ Qᶜ) :
    (integralRelativeCohomologyMap (n + 1) f
      (show MapsTo f (K ∩ L)ᶜ (P ∩ Q)ᶜ from by
        simpa only [compl_inter] using hfK.union_union hfL)).comp
      (integralCohomologyWithSupportMayerVietorisConnecting n P Q hP hQ) =
      (integralCohomologyWithSupportMayerVietorisConnecting n K L hK hL).comp
        (integralRelativeCohomologyMap n f
          (show MapsTo f (K ∪ L)ᶜ (P ∪ Q)ᶜ from by
            simpa only [compl_union] using hfK.inter_inter hfL)) := by
  have h := integralRelativeMayerVietorisConnecting_natural n f
    hK.isOpen_compl hL.isOpen_compl hP.isOpen_compl hQ.isOpen_compl hfK hfL
  have hOut := relative_cohomology_map_eqToHom (n + 1) f
    (compl_inter K L).symm (compl_inter P Q).symm
    (hfK.union_union hfL)
    (show MapsTo f (K ∩ L)ᶜ (P ∩ Q)ᶜ from by
      simpa only [compl_inter] using hfK.union_union hfL)
  have hIn := relative_cohomology_map_eqToHom n f
    (compl_union K L) (compl_union P Q)
    (show MapsTo f (K ∪ L)ᶜ (P ∪ Q)ᶜ from by
      simpa only [compl_union] using hfK.inter_inter hfL)
    (hfK.inter_inter hfL)
  unfold integralCohomologyWithSupportMayerVietorisConnecting
  ext α
  simp only [LinearMap.comp_apply]
  exact (LinearMap.congr_fun hOut _).symm.trans
    ((congrArg _ (LinearMap.congr_fun h _)).trans
      (congrArg _ (congrArg
        (integralRelativeMayerVietorisConnecting n Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl)
        (LinearMap.congr_fun hIn α).symm)))

end DifferentialGeometry.Topology

end

noncomputable section
open CategoryTheory Set
universe u
namespace DifferentialGeometry.Topology
variable {X : Type u} [TopologicalSpace X]

theorem integralCohomologyWithSupportMayerVietorisConnecting_natural
    (n : ℕ) (K L K' L' : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (hK' : IsClosed K') (hL' : IsClosed L')
    (hKK' : K ⊆ K') (hLL' : L ⊆ L') :
    (integralRelativeCohomologyMap (n + 1) (ContinuousMap.id X)
      (show MapsTo (ContinuousMap.id X) (K' ∩ L')ᶜ (K ∩ L)ᶜ from
        fun _ hx => compl_subset_compl.mpr (inter_subset_inter hKK' hLL') hx)).comp
      (integralCohomologyWithSupportMayerVietorisConnecting n K L hK hL) =
      (integralCohomologyWithSupportMayerVietorisConnecting n K' L' hK' hL').comp
      (integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) (K' ∪ L')ᶜ (K ∪ L)ᶜ from
          fun _ hx => compl_subset_compl.mpr (union_subset_union hKK' hLL') hx)) := by
  exact integralCohomologyWithSupportMayerVietorisConnecting_map n (ContinuousMap.id X)
    K' L' K L hK' hL' hK hL
    (show MapsTo (ContinuousMap.id X) K'ᶜ Kᶜ from fun _ hx => compl_subset_compl.mpr hKK' hx)
    (show MapsTo (ContinuousMap.id X) L'ᶜ Lᶜ from fun _ hx => compl_subset_compl.mpr hLL' hx)

end DifferentialGeometry.Topology
end
