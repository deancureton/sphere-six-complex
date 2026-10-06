module

public import DifferentialGeometry.Topology.Homology.RelativeCochainMayerVietoris
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyConnecting
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem integralTwoSetRelativeCochainDifference_fst (n : ℕ) (A B : Set X)
    (ω : (integralTwoSetRelativeCochains A B).X n) :
    (biprod.fst : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶
      integralRelativeCochains A).f n ((integralTwoSetRelativeCochainDifference A B).f n ω) =
      (pullback.fst (integralRelativeCochainInclusion A)
        (integralRelativeCochainInclusion B)).f n ω := by
  exact congrArg (fun f : (integralTwoSetRelativeCochains A B).X n ⟶
    (integralRelativeCochains A).X n => f ω)
    (HomologicalComplex.biprod_lift_fst_f _ _ n)

private theorem integralRelativeCochainInterSum_apply (n : ℕ) (A B : Set X)
    (b : (integralRelativeCochains A ⊞ integralRelativeCochains B).X n) :
    (integralRelativeCochainInterSum A B).f n b =
      (integralRelativeCochainMap (ContinuousMap.id X)
        (show A ∩ B ⊆ A from Set.inter_subset_left)).f n
        ((biprod.fst : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶
          integralRelativeCochains A).f n b) +
      (integralRelativeCochainMap (ContinuousMap.id X)
        (show A ∩ B ⊆ B from Set.inter_subset_right)).f n
        ((biprod.snd : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶
          integralRelativeCochains B).f n b) := by
  have h := congrArg (fun f : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶
    integralRelativeCochains (A ∩ B) => f.f n b)
    (biprod.desc_eq
      (f := integralRelativeCochainMap (ContinuousMap.id X)
        (show A ∩ B ⊆ A from Set.inter_subset_left))
      (g := integralRelativeCochainMap (ContinuousMap.id X)
        (show A ∩ B ⊆ B from Set.inter_subset_right)))
  exact h

private theorem integralTwoSetRelativeCochainDifference_fst_of_eq_coboundary (n : ℕ) (A B : Set X)
    (ω : (integralTwoSetRelativeCochains A B).X (n + 1))
    (b : (integralRelativeCochains A ⊞ integralRelativeCochains B).X n)
    (h : (integralTwoSetRelativeCochainDifference A B).f (n + 1) ω =
      (integralRelativeCochains A ⊞ integralRelativeCochains B).d n (n + 1) b) :
    (pullback.fst (integralRelativeCochainInclusion A)
      (integralRelativeCochainInclusion B)).f (n + 1) ω =
      (integralRelativeCochains A).d n (n + 1)
        ((biprod.fst : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶
          integralRelativeCochains A).f n b) := by
  let p : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶
    integralRelativeCochains A := biprod.fst
  have hp := congrArg (p.f (n + 1)) h
  rw [integralTwoSetRelativeCochainDifference_fst] at hp
  exact hp.trans (congrArg (fun f : (integralRelativeCochains A ⊞
    integralRelativeCochains B).X n ⟶ (integralRelativeCochains A).X (n + 1) => f b)
    (p.comm n (n + 1))).symm

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem relative_cochain_pullback_zero (n : ℕ) (A : Set X)
    (p : (integralRelativeCochains A).X n) :
    integralSingularCochainPullback n (singularSubspaceInclusion A)
      ((integralRelativeCochainInclusion A).f n p) = 0 :=
  congrArg (fun f : integralRelativeCochains A ⟶ integralSingularCochains A => f.f n p)
    (integralRelativeCochainInclusion_comp A)

private theorem twoSet_cochain_ambient_eq (n : ℕ) (A B : Set X)
    (p : (integralTwoSetRelativeCochains A B).X n) :
    (integralRelativeCochainInclusion A).f n
      ((pullback.fst (integralRelativeCochainInclusion A)
        (integralRelativeCochainInclusion B)).f n p) =
    (integralRelativeCochainInclusion B).f n
      ((pullback.snd (integralRelativeCochainInclusion A)
        (integralRelativeCochainInclusion B)).f n p) :=
  congrArg (fun f : integralTwoSetRelativeCochains A B ⟶ integralSingularCochains X => f.f n p)
    (pullback.condition (f := integralRelativeCochainInclusion A)
      (g := integralRelativeCochainInclusion B))

private theorem twoSet_cochain_comparison_ambient (n : ℕ) (A B : Set X)
    (p : (integralRelativeCochains (A ∪ B)).X n) :
    (integralRelativeCochainInclusion A).f n
      ((pullback.fst (integralRelativeCochainInclusion A)
        (integralRelativeCochainInclusion B)).f n
        ((integralRelativeCochainUnionComparison A B).f n p)) =
      (integralRelativeCochainInclusion (A ∪ B)).f n p := by
  have h : integralRelativeCochainUnionComparison A B ≫
      pullback.fst (integralRelativeCochainInclusion A)
        (integralRelativeCochainInclusion B) ≫ integralRelativeCochainInclusion A =
      integralRelativeCochainInclusion (A ∪ B) := by
    unfold integralRelativeCochainUnionComparison
    erw [pullback.lift_fst_assoc, integralRelativeCochainMap_inclusion,
      integralSingularCochainMap_id, Category.comp_id]
  exact congrArg (fun f : integralRelativeCochains (A ∪ B) ⟶
    integralSingularCochains X => f.f n p) h

private theorem relative_cochain_inter_map_ambient (n : ℕ) (A C : Set X) (hCA : C ⊆ A)
    (p : (integralRelativeCochains A).X n) :
    (integralRelativeCochainInclusion C).f n
      ((integralRelativeCochainMap (ContinuousMap.id X) hCA).f n p) =
      (integralRelativeCochainInclusion A).f n p := by
  have h := integralRelativeCochainMap_inclusion (ContinuousMap.id X) hCA
  rw [integralSingularCochainMap_id, Category.comp_id] at h
  exact congrArg (fun f : integralRelativeCochains A ⟶ integralSingularCochains X => f.f n p) h

private theorem cochain_differential_apply {K L : CochainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ L) (n : ℕ) (p : K.X n) :
    L.d n (n + 1) (f.f n p) = f.f (n + 1) (K.d n (n + 1) p) :=
  congrArg (fun g : K.X n ⟶ L.X (n + 1) => g p) (f.comm n (n + 1))

private theorem exists_relative_cochain_decomposition_of_correction (n : ℕ) (A B : Set X)
    (φ : (integralRelativeCochains (A ∩ B)).X n)
    (b : (integralRelativeCochains A ⊞ integralRelativeCochains B).X n)
    (ω : (integralTwoSetRelativeCochains A B).X (n + 1))
    (β : (integralRelativeCochains (A ∪ B)).X (n + 1))
    (η : (integralTwoSetRelativeCochains A B).X n)
    (hb : (integralRelativeCochainInterSum A B).f n b = φ)
    (hω : (integralTwoSetRelativeCochainDifference A B).f (n + 1) ω =
      (integralRelativeCochains A ⊞ integralRelativeCochains B).d n (n + 1) b)
    (hη : (integralTwoSetRelativeCochains A B).d n (n + 1) η =
      (integralRelativeCochainUnionComparison A B).f (n + 1) β - ω) :
    ∃ p q : integralSingularCochain n X,
      integralSingularCochainPullback n (singularSubspaceInclusion A) p = 0 ∧
      integralSingularCochainPullback n (singularSubspaceInclusion B) q = 0 ∧
      p + q = (integralRelativeCochainInclusion (A ∩ B)).f n φ ∧
      (integralSingularCochains X).d n (n + 1) p =
        (integralRelativeCochainInclusion (A ∪ B)).f (n + 1) β := by
  let pA : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶ integralRelativeCochains A :=
    biprod.fst
  let pB : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶ integralRelativeCochains B :=
    biprod.snd
  let fA : integralTwoSetRelativeCochains A B ⟶ integralRelativeCochains A :=
    pullback.fst (integralRelativeCochainInclusion A) (integralRelativeCochainInclusion B)
  let fB : integralTwoSetRelativeCochains A B ⟶ integralRelativeCochains B :=
    pullback.snd (integralRelativeCochainInclusion A) (integralRelativeCochainInclusion B)
  let ιA := integralRelativeCochainInclusion A
  let ιB := integralRelativeCochainInclusion B
  let p := ιA.f n (pA.f n b + fA.f n η)
  let q := ιB.f n (pB.f n b - fB.f n η)
  refine ⟨p, q, relative_cochain_pullback_zero n A _, relative_cochain_pullback_zero n B _, ?_, ?_⟩
  · have hc : ιA.f n (fA.f n η) = ιB.f n (fB.f n η) :=
      twoSet_cochain_ambient_eq n A B η
    have hs := congrArg ((integralRelativeCochainInclusion (A ∩ B)).f n) hb
    rw [integralRelativeCochainInterSum_apply, map_add,
      relative_cochain_inter_map_ambient, relative_cochain_inter_map_ambient] at hs
    dsimp only [p, q]
    rw [map_add, map_sub, hc]
    calc
      _ = ιA.f n (pA.f n b) + ιB.f n (pB.f n b) := by abel
      _ = _ := hs
  · have hc := cochain_differential_apply ιA n (pA.f n b + fA.f n η)
    have hp : fA.f (n + 1) ω =
        (integralRelativeCochains A).d n (n + 1) (pA.f n b) :=
      integralTwoSetRelativeCochainDifference_fst_of_eq_coboundary n A B ω b hω
    have he := cochain_differential_apply fA n η
    rw [hη, map_sub] at he
    have he' : ιA.f (n + 1)
        (fA.f (n + 1) ((integralRelativeCochainUnionComparison A B).f (n + 1) β)) =
        (integralRelativeCochainInclusion (A ∪ B)).f (n + 1) β :=
      twoSet_cochain_comparison_ambient (n + 1) A B β
    change (integralSingularCochains X).d n (n + 1)
      (ιA.f n (pA.f n b + fA.f n η)) = _
    rw [hc, map_add, ← hp, he]
    rw [map_add, map_sub, he']
    abel

end DifferentialGeometry.Topology

end
noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem integralRelativeMayerVietorisConnecting_comparison_class
    (n : ℕ) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (φ : LinearMap.ker ((integralRelativeCochains (A ∩ B)).sc n).g.hom)
    (b : (integralRelativeCochains A ⊞ integralRelativeCochains B).X n)
    (hb : (integralRelativeCochainInterSum A B).f n b = φ.val)
    (ω : LinearMap.ker ((integralTwoSetRelativeCochains A B).sc (n + 1)).g.hom)
    (hω : (integralTwoSetRelativeCochainDifference A B).f (n + 1) ω.val =
      (integralRelativeCochains A ⊞ integralRelativeCochains B).d n (n + 1) b) :
    (HomologicalComplex.homologyMap (integralRelativeCochainUnionComparison A B)
        (n + 1)).hom
      (integralRelativeMayerVietorisConnecting n A B hA hB
        (moduleHomologyClass ((integralRelativeCochains (A ∩ B)).sc n) φ)) =
      moduleHomologyClass ((integralTwoSetRelativeCochains A B).sc (n + 1)) ω := by
  have hc := LinearMap.congr_fun
    (integralRelativeMayerVietorisConnecting_comparison n A B hA hB)
    (moduleHomologyClass ((integralRelativeCochains (A ∩ B)).sc n) φ)
  exact hc.trans (moduleHomologyClass_connecting
    (integralTwoSetRelativeCochainSequence_shortExact A B) n (n + 1) (by simp) φ b hb ω hω)

private theorem exists_relative_connecting_correction
    (n : ℕ) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (φ : LinearMap.ker ((integralRelativeCochains (A ∩ B)).sc n).g.hom)
    (b : (integralRelativeCochains A ⊞ integralRelativeCochains B).X n)
    (hb : (integralRelativeCochainInterSum A B).f n b = φ.val)
    (ω : LinearMap.ker ((integralTwoSetRelativeCochains A B).sc (n + 1)).g.hom)
    (hω : (integralTwoSetRelativeCochainDifference A B).f (n + 1) ω.val =
      (integralRelativeCochains A ⊞ integralRelativeCochains B).d n (n + 1) b) :
    ∃ β : LinearMap.ker ((integralRelativeCochains (A ∪ B)).sc (n + 1)).g.hom,
      ∃ η : (integralTwoSetRelativeCochains A B).X n,
        integralRelativeMayerVietorisConnecting n A B hA hB
          (moduleHomologyClass ((integralRelativeCochains (A ∩ B)).sc n) φ) =
            moduleHomologyClass ((integralRelativeCochains (A ∪ B)).sc (n + 1)) β ∧
        (integralTwoSetRelativeCochains A B).d n (n + 1) η =
          (integralRelativeCochainUnionComparison A B).f (n + 1) β.val -
            (show (integralTwoSetRelativeCochains A B).X (n + 1) from ω.val) := by
  obtain ⟨β, hβ⟩ := moduleHomologyClass_surjective
    ((integralRelativeCochains (A ∪ B)).sc (n + 1))
    (integralRelativeMayerVietorisConnecting n A B hA hB
      (moduleHomologyClass ((integralRelativeCochains (A ∩ B)).sc n) φ))
  have hc := integralRelativeMayerVietorisConnecting_comparison_class n A B hA hB φ b hb ω hω
  rw [← hβ] at hc
  let P := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ)
    (ComplexShape.up ℕ) (n + 1)).map (integralRelativeCochainUnionComparison A B)
  change (ShortComplex.homologyMap P).hom _ = _ at hc
  rw [moduleHomologyClass_map, moduleHomologyClass_eq_iff] at hc
  obtain ⟨η, hη⟩ := hc
  refine ⟨β, ((integralTwoSetRelativeCochains A B).xPrevIso
    (i := n) (j := n + 1) rfl).hom η, hβ.symm, ?_⟩
  change (integralTwoSetRelativeCochains A B).dTo (n + 1) η = _ at hη
  rw [(integralTwoSetRelativeCochains A B).dTo_eq (i := n) rfl] at hη
  exact hη

end DifferentialGeometry.Topology

end
noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem exists_integralRelativeMayerVietorisConnecting_cochain_representative
    (n : ℕ) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (φ : LinearMap.ker ((integralRelativeCochains (A ∩ B)).sc n).g.hom) :
    ∃ β : LinearMap.ker ((integralRelativeCochains (A ∪ B)).sc (n + 1)).g.hom,
      ∃ p q : integralSingularCochain n X,
        integralRelativeMayerVietorisConnecting n A B hA hB
          (moduleHomologyClass ((integralRelativeCochains (A ∩ B)).sc n) φ) =
            moduleHomologyClass ((integralRelativeCochains (A ∪ B)).sc (n + 1)) β ∧
        integralSingularCochainPullback n (singularSubspaceInclusion A) p = 0 ∧
        integralSingularCochainPullback n (singularSubspaceInclusion B) q = 0 ∧
        p + q = (integralRelativeCochainInclusion (A ∩ B)).f n φ.val ∧
        (integralSingularCochains X).d n (n + 1) p =
          (integralRelativeCochainInclusion (A ∪ B)).f (n + 1) β.val := by
  obtain ⟨b, ω, hb, hω⟩ := exists_moduleCycle_connecting_lifts
    (integralTwoSetRelativeCochainSequence_shortExact A B) n (n + 1) (by simp) φ
  obtain ⟨β, η, hβ, hη⟩ := exists_relative_connecting_correction
    n A B hA hB φ b hb ω hω
  obtain ⟨p, q, hp, hq, hpq, hdp⟩ := exists_relative_cochain_decomposition_of_correction
    n A B φ.val b ω.val β.val η hb hω hη
  exact ⟨β, p, q, hβ, hp, hq, hpq, hdp⟩

private theorem relative_class_cast
    (n : ℕ) (A B : Set X) (h : A = B)
    (φ : LinearMap.ker ((integralRelativeCochains A).sc n).g.hom) :
    (eqToHom (congrArg (integralRelativeCohomology n) h)).hom
      (moduleHomologyClass ((integralRelativeCochains A).sc n) φ) =
      moduleHomologyClass ((integralRelativeCochains B).sc n)
        (moduleCycleMap ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ)
          (ComplexShape.up ℕ) n).map (eqToHom (congrArg integralRelativeCochains h))) φ) := by
  subst B
  rfl

private theorem relative_inclusion_cast
    (n : ℕ) (A B : Set X) (h : A = B) (φ : (integralRelativeCochains A).X n) :
    (integralRelativeCochainInclusion B).f n
        ((eqToHom (congrArg integralRelativeCochains h)).f n φ) =
      (integralRelativeCochainInclusion A).f n φ := by
  subst B
  rfl

theorem exists_integralCohomologyWithSupportMayerVietorisConnecting_cochain_representative
    (n : ℕ) (K L : Set X) (hK : IsClosed K) (hL : IsClosed L)
    (φ : LinearMap.ker ((integralRelativeCochains (K ∪ L)ᶜ).sc n).g.hom) :
    ∃ β : LinearMap.ker ((integralRelativeCochains (K ∩ L)ᶜ).sc (n + 1)).g.hom,
      ∃ p q : integralSingularCochain n X,
        integralCohomologyWithSupportMayerVietorisConnecting n K L hK hL
          (moduleHomologyClass ((integralRelativeCochains (K ∪ L)ᶜ).sc n) φ) =
            moduleHomologyClass ((integralRelativeCochains (K ∩ L)ᶜ).sc (n + 1)) β ∧
        integralSingularCochainPullback n (singularSubspaceInclusion Kᶜ) p = 0 ∧
        integralSingularCochainPullback n (singularSubspaceInclusion Lᶜ) q = 0 ∧
        p + q = (integralRelativeCochainInclusion (K ∪ L)ᶜ).f n φ.val ∧
        (integralSingularCochains X).d n (n + 1) p =
          (integralRelativeCochainInclusion (K ∩ L)ᶜ).f (n + 1) β.val := by
  let P := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ)
    (ComplexShape.up ℕ) n).map
    (eqToHom (congrArg integralRelativeCochains (compl_union K L)))
  let φ' := moduleCycleMap P φ
  obtain ⟨β, p, q, hβ, hp, hq, hpq, hdp⟩ :=
    exists_integralRelativeMayerVietorisConnecting_cochain_representative
      n Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl φ'
  let Q := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ)
    (ComplexShape.up ℕ) (n + 1)).map
    (eqToHom (congrArg integralRelativeCochains (compl_inter K L).symm))
  let β' := moduleCycleMap Q β
  refine ⟨β', p, q, ?_, hp, hq, ?_, ?_⟩
  · change (eqToHom (congrArg (integralRelativeCohomology (n + 1))
      (compl_inter K L).symm)).hom
      (integralRelativeMayerVietorisConnecting n Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl
        ((eqToHom (congrArg (integralRelativeCohomology n) (compl_union K L))).hom
          (moduleHomologyClass ((integralRelativeCochains (K ∪ L)ᶜ).sc n) φ))) = _
    erw [relative_class_cast n (K ∪ L)ᶜ (Kᶜ ∩ Lᶜ) (compl_union K L) φ]
    change (eqToHom (congrArg (integralRelativeCohomology (n + 1))
      (compl_inter K L).symm)).hom
      (integralRelativeMayerVietorisConnecting n Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl
        (moduleHomologyClass ((integralRelativeCochains (Kᶜ ∩ Lᶜ)).sc n) φ')) = _
    rw [hβ]
    exact relative_class_cast (n + 1) (Kᶜ ∪ Lᶜ) (K ∩ L)ᶜ (compl_inter K L).symm β
  · exact hpq.trans (relative_inclusion_cast n (K ∪ L)ᶜ (Kᶜ ∩ Lᶜ)
      (compl_union K L) φ.val)
  · exact hdp.trans (relative_inclusion_cast (n + 1) (Kᶜ ∪ Lᶜ) (K ∩ L)ᶜ
      (compl_inter K L).symm β.val).symm

end DifferentialGeometry.Topology

end
