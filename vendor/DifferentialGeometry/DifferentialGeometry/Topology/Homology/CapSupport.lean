module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CapProduct
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TwoSetSmallChains
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps

@[expose] public section

noncomputable section

open CategoryTheory Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSingularCapProduct_mem_carrier
    (k m : ℕ) (φ : integralSingularCochain k X) (A : Set X)
    {c : (integralSingularChains X).X (k + m)}
    (hc : c ∈ integralSingularChainsIn (k + m) A) :
    integralSingularCapProduct k m φ c ∈ integralSingularChainsIn m A := by
  rw [integralSingularChainsIn_eq_range] at hc ⊢
  obtain ⟨b, rfl⟩ := hc
  exact ⟨integralSingularCapProduct k m
    (integralSingularCochainPullback k (singularSubspaceInclusion A) φ) b,
    LinearMap.congr_fun (integralSingularCapProduct_natural k m
      (singularSubspaceInclusion A) φ) b⟩

theorem integralSingularCapProduct_eq_zero_of_pullback_eq_zero
    (k m : ℕ) (φ : integralSingularCochain k X) (A : Set X)
    (hφ : integralSingularCochainPullback k (singularSubspaceInclusion A) φ = 0)
    {c : (integralSingularChains X).X (k + m)}
    (hc : c ∈ integralSingularChainsIn (k + m) A) :
    integralSingularCapProduct k m φ c = 0 := by
  rw [integralSingularChainsIn_eq_range] at hc
  obtain ⟨b, rfl⟩ := hc
  have h := LinearMap.congr_fun (integralSingularCapProduct_natural k m
    (singularSubspaceInclusion A) φ) b
  simpa only [LinearMap.comp_apply, hφ, map_zero, LinearMap.zero_apply] using h.symm

theorem integralSingularCapProduct_mem_carrier_of_small
    (k m : ℕ) (φ : integralSingularCochain k X) (A B : Set X)
    (hφ : integralSingularCochainPullback k (singularSubspaceInclusion B) φ = 0)
    {c : (integralSingularChains X).X (k + m)}
    (hc : c ∈ integralSingularSmallChains (k + m) (twoSetCover A B)) :
    integralSingularCapProduct k m φ c ∈ integralSingularChainsIn m A := by
  rw [integralSingularTwoSetSmallChains_eq, Submodule.mem_sup] at hc
  obtain ⟨a, ha, b, hb, rfl⟩ := hc
  rw [map_add, integralSingularCapProduct_eq_zero_of_pullback_eq_zero k m φ B hφ hb,
    add_zero]
  exact integralSingularCapProduct_mem_carrier k m φ A ha

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSingularCapProduct_coboundary_of_boundary_carrier
    (k m : ℕ) (φ : integralSingularCochain k X) (A : Set X)
    (hφ : integralSingularCochainPullback k (singularSubspaceInclusion A) φ = 0)
    (c : (integralSingularChains X).X (k + m + 1))
    (hc : (integralSingularChains X).d (k + m + 1) (k + m) c ∈
      integralSingularChainsIn (k + m) A) :
    integralSingularCapProduct (k + 1) m (integralSingularCoboundary X k (k + 1) φ)
        (((integralSingularChains X).XIsoOfEq
          (show k + m + 1 = (k + 1) + m by omega)).hom c) =
      (-1 : ℤ) ^ (k + 1) • (integralSingularChains X).d (m + 1) m
        (integralSingularCapProduct k (m + 1) φ c) := by
  have h := LinearMap.congr_fun (integralSingularCapProduct_boundary k m φ) c
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h
  have heval := map_zsmul
    (LinearMap.applyₗ (R := ℤ) (M₂ := (integralSingularChains X).X m) c)
    ((-1 : ℤ) ^ k) (((integralSingularChains X).d (m + 1) m).hom.comp
      (integralSingularCapProduct k (m + 1) φ))
  rw [integralSingularCapProduct_eq_zero_of_pullback_eq_zero k m φ A hφ hc] at h
  have hp := h.trans (congrArg (fun z =>
    integralSingularCapProduct (k + 1) m (integralSingularCoboundary X k (k + 1) φ)
      (((integralSingularChains X).XIsoOfEq
        (show k + m + 1 = (k + 1) + m by omega)).hom c) + z) heval)
  rw [pow_succ, mul_neg_one, neg_zsmul]
  exact eq_neg_of_add_eq_zero_left hp.symm

theorem integralSingularCapProduct_boundary_eq_zero_of_boundary_carrier
    (k m : ℕ) (φ : integralSingularCochain k X) (A : Set X)
    (hφ : integralSingularCochainPullback k (singularSubspaceInclusion A) φ = 0)
    (hdφ : integralSingularCoboundary X k (k + 1) φ = 0)
    (c : (integralSingularChains X).X (k + m + 1))
    (hc : (integralSingularChains X).d (k + m + 1) (k + m) c ∈
      integralSingularChainsIn (k + m) A) :
    (integralSingularChains X).d (m + 1) m
      (integralSingularCapProduct k (m + 1) φ c) = 0 := by
  have h := integralSingularCapProduct_coboundary_of_boundary_carrier k m φ A hφ c hc
  rw [hdφ, map_zero, LinearMap.zero_apply] at h
  rcases Nat.even_or_odd (k + 1) with hk | hk
  · simpa only [hk.neg_one_pow, one_zsmul] using h.symm
  · simpa only [hk.neg_one_pow, neg_one_zsmul, neg_eq_zero] using h.symm

private theorem cap_sum_boundary_eq_zero
    (k m : ℕ) (φ ψ : integralSingularCochain k X) (A B : Set X)
    (hφ : integralSingularCochainPullback k (singularSubspaceInclusion A) φ = 0)
    (hψ : integralSingularCochainPullback k (singularSubspaceInclusion B) ψ = 0)
    (hd : integralSingularCoboundary X k (k + 1) (φ + ψ) = 0)
    (c : (integralSingularChains X).X (k + m + 1))
    (hc : (integralSingularChains X).d (k + m + 1) (k + m) c ∈
      integralSingularChainsIn (k + m) (A ∩ B)) :
    (integralSingularChains X).d (m + 1) m
        (integralSingularCapProduct k (m + 1) φ c) +
      (integralSingularChains X).d (m + 1) m
        (integralSingularCapProduct k (m + 1) ψ c) = 0 := by
  have hφc := integralSingularCapProduct_coboundary_of_boundary_carrier k m φ A hφ c
    (integralSingularChainsIn_mono (k + m) inter_subset_left hc)
  have hψc := integralSingularCapProduct_coboundary_of_boundary_carrier k m ψ B hψ c
    (integralSingularChainsIn_mono (k + m) inter_subset_right hc)
  have hsum := congrArg (fun L : integralSingularCochain (k + 1) X =>
    integralSingularCapProduct (k + 1) m L
      (((integralSingularChains X).XIsoOfEq
        (show k + m + 1 = (k + 1) + m by omega)).hom c)) hd
  rw [map_add, map_add, LinearMap.add_apply, map_zero, LinearMap.zero_apply,
    hφc, hψc] at hsum
  rcases Nat.even_or_odd (k + 1) with hk | hk
  · simpa only [hk.neg_one_pow, one_zsmul] using hsum
  · have hn := congrArg Neg.neg hsum
    simpa only [hk.neg_one_pow, neg_one_zsmul, neg_neg, neg_add_rev, neg_zero, add_comm] using hn

theorem integralSingularCapProduct_boundary_mem_inter_of_small
    (k m : ℕ) (φ ψ : integralSingularCochain k X) (U V A B : Set X)
    (hφ : integralSingularCochainPullback k (singularSubspaceInclusion A) φ = 0)
    (hψ : integralSingularCochainPullback k (singularSubspaceInclusion B) ψ = 0)
    (hd : integralSingularCoboundary X k (k + 1) (φ + ψ) = 0)
    (c : (integralSingularChains X).X (k + m + 1))
    (hcU : c ∈ integralSingularSmallChains (k + m + 1) (twoSetCover U A))
    (hcV : c ∈ integralSingularSmallChains (k + m + 1) (twoSetCover V B))
    (hc : (integralSingularChains X).d (k + m + 1) (k + m) c ∈
      integralSingularChainsIn (k + m) (A ∩ B)) :
    (integralSingularChains X).d (m + 1) m
      (integralSingularCapProduct k (m + 1) φ c) ∈
        integralSingularChainsIn m (U ∩ V) := by
  rw [integralSingularChainsIn_inter]
  refine ⟨integralSingularChainsIn_boundary m U
    (integralSingularCapProduct_mem_carrier_of_small k (m + 1) φ U A hφ hcU), ?_⟩
  have hV := integralSingularChainsIn_boundary m V
    (integralSingularCapProduct_mem_carrier_of_small k (m + 1) ψ V B hψ hcV)
  rw [eq_neg_of_add_eq_zero_left (cap_sum_boundary_eq_zero k m φ ψ A B hφ hψ hd c hc)]
  exact (integralSingularChainsIn m V).neg_mem hV

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem exists_carrier_boundary_cycle (m : ℕ) (W : Set X)
    (b : (integralSingularChains X).X (m + 1))
    (hb : (integralSingularChains X).d (m + 1) m b ∈ integralSingularChainsIn m W) :
    ∃ z : LinearMap.ker ((integralSingularChains W).sc m).g.hom,
      (integralSingularChainMap (singularSubspaceInclusion W)).f m z.val =
        (integralSingularChains X).d (m + 1) m b := by
  let z := integralSingularChainRestriction m W ⟨_, hb⟩
  have hz : (integralSingularChainMap (singularSubspaceInclusion W)).f m z =
      (integralSingularChains X).d (m + 1) m b :=
    integralSingularChainRestriction_inclusion m W ⟨_, hb⟩
  refine ⟨⟨z, ?_⟩, hz⟩
  change (integralSingularChains W).d m ((ComplexShape.down ℕ).next m) z = 0
  apply integralSingularChainInclusion_injective ((ComplexShape.down ℕ).next m) W
  have h := congrArg (fun f : (integralSingularChains W).X m ⟶
    (integralSingularChains X).X ((ComplexShape.down ℕ).next m) => f z)
    ((integralSingularChainMap (singularSubspaceInclusion W)).comm m ((ComplexShape.down ℕ).next m))
  simp only [ModuleCat.comp_apply] at h
  rw [map_zero, ← h, hz]
  change (((integralSingularChains X).d (m + 1) m ≫
    (integralSingularChains X).d m ((ComplexShape.down ℕ).next m)) b) = 0
  rw [HomologicalComplex.d_comp_d]
  rfl

private theorem inclusion_comp_apply (n : ℕ) (A B : Set X) (h : A ⊆ B)
    (z : (integralSingularChains A).X n) :
    (integralSingularChainMap (singularSubspaceInclusion B)).f n
      ((integralSingularChainMap (ContinuousMap.inclusion h)).f n z) =
        (integralSingularChainMap (singularSubspaceInclusion A)).f n z := by
  have he : (singularSubspaceInclusion B).comp (ContinuousMap.inclusion h) =
      singularSubspaceInclusion A := rfl
  rw [← he, integralSingularChainMap_comp]
  rfl

theorem exists_integralSingularCapProduct_inter_boundary_cycle
    (k m : ℕ) (φ ψ : integralSingularCochain k X) (U V A B : Set X)
    (hφ : integralSingularCochainPullback k (singularSubspaceInclusion A) φ = 0)
    (hψ : integralSingularCochainPullback k (singularSubspaceInclusion B) ψ = 0)
    (hd : integralSingularCoboundary X k (k + 1) (φ + ψ) = 0)
    (c : (integralSingularChains X).X (k + m + 1))
    (hcU : c ∈ integralSingularSmallChains (k + m + 1) (twoSetCover U A))
    (hcV : c ∈ integralSingularSmallChains (k + m + 1) (twoSetCover V B))
    (hc : (integralSingularChains X).d (k + m + 1) (k + m) c ∈
      integralSingularChainsIn (k + m) (A ∩ B)) :
    ∃ a : (integralSingularChains U).X (m + 1),
      ∃ b : (integralSingularChains V).X (m + 1),
      ∃ z : LinearMap.ker ((integralSingularChains ↥(U ∩ V)).sc m).g.hom,
        (integralSingularChainMap (singularSubspaceInclusion U)).f (m + 1) a =
          integralSingularCapProduct k (m + 1) φ c ∧
        (integralSingularChainMap (singularSubspaceInclusion V)).f (m + 1) b =
          integralSingularCapProduct k (m + 1) ψ c ∧
        (integralSingularChains U).d (m + 1) m a =
          (integralSingularChainMap (ContinuousMap.inclusion
            (show U ∩ V ⊆ U from inter_subset_left))).f m z.val ∧
        (integralSingularChains V).d (m + 1) m b =
          -(integralSingularChainMap (ContinuousMap.inclusion
            (show U ∩ V ⊆ V from inter_subset_right))).f m z.val ∧
        integralSingularCapProduct (k + 1) m (integralSingularCoboundary X k (k + 1) φ)
            (((integralSingularChains X).XIsoOfEq
              (show k + m + 1 = (k + 1) + m by omega)).hom c) =
          (-1 : ℤ) ^ (k + 1) •
            (integralSingularChainMap (singularSubspaceInclusion (U ∩ V))).f m z.val := by
  let a := integralSingularChainRestriction (m + 1) U
    ⟨_, integralSingularCapProduct_mem_carrier_of_small k (m + 1) φ U A hφ hcU⟩
  let b := integralSingularChainRestriction (m + 1) V
    ⟨_, integralSingularCapProduct_mem_carrier_of_small k (m + 1) ψ V B hψ hcV⟩
  have ha := integralSingularChainRestriction_inclusion (m + 1) U
    ⟨_, integralSingularCapProduct_mem_carrier_of_small k (m + 1) φ U A hφ hcU⟩
  have hb := integralSingularChainRestriction_inclusion (m + 1) V
    ⟨_, integralSingularCapProduct_mem_carrier_of_small k (m + 1) ψ V B hψ hcV⟩
  obtain ⟨z, hz⟩ := exists_carrier_boundary_cycle m (U ∩ V)
    (integralSingularCapProduct k (m + 1) φ c)
    (integralSingularCapProduct_boundary_mem_inter_of_small k m φ ψ U V A B
      hφ hψ hd c hcU hcV hc)
  refine ⟨a, b, z, ha, hb, ?_, ?_, ?_⟩
  · apply integralSingularChainInclusion_injective m U
    rw [integralSingularChainMap_boundary, ha]
    exact hz.symm.trans (inclusion_comp_apply m (U ∩ V) U inter_subset_left z.val).symm
  · apply integralSingularChainInclusion_injective m V
    rw [integralSingularChainMap_boundary, hb, map_neg]
    have hinc := inclusion_comp_apply m (U ∩ V) V inter_subset_right z.val
    have he := hinc.trans hz
    rw [he]
    have hφc := integralSingularCapProduct_coboundary_of_boundary_carrier k m φ A hφ c
      (integralSingularChainsIn_mono (k + m) inter_subset_left hc)
    have hψc := integralSingularCapProduct_coboundary_of_boundary_carrier k m ψ B hψ c
      (integralSingularChainsIn_mono (k + m) inter_subset_right hc)
    have hsum := congrArg (fun L : integralSingularCochain (k + 1) X =>
      integralSingularCapProduct (k + 1) m L
        (((integralSingularChains X).XIsoOfEq
          (show k + m + 1 = (k + 1) + m by omega)).hom c)) hd
    rw [map_add, map_add, LinearMap.add_apply, map_zero, LinearMap.zero_apply,
      hφc, hψc] at hsum
    rcases Nat.even_or_odd (k + 1) with hk | hk
    · simp only [hk.neg_one_pow, one_zsmul] at hsum
      exact eq_neg_of_add_eq_zero_right hsum
    · simp only [hk.neg_one_pow, neg_one_zsmul] at hsum
      exact eq_neg_of_add_eq_zero_right (by
        simpa only [neg_add, neg_neg, neg_zero] using congrArg Neg.neg hsum)
  · rw [integralSingularCapProduct_coboundary_of_boundary_carrier k m φ A hφ c
      (integralSingularChainsIn_mono (k + m) inter_subset_left hc), hz]

end DifferentialGeometry.Topology

end
