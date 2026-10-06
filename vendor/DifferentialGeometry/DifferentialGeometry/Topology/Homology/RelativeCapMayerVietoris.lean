module

public import DifferentialGeometry.Topology.Homology.MayerVietorisCap
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCapToAbsoluteHomology
public import DifferentialGeometry.Topology.Homology.RelativeCochainMayerVietorisRepresentatives
public import DifferentialGeometry.Topology.Homology.SmallRelativeRepresentatives
public import DifferentialGeometry.Topology.Homology.ModuleHomologyDegree
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OpenExcision
public import DifferentialGeometry.Topology.Homology.TwoSetCoverSubdivision

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem exists_integralRelativeCycle_projection_of_eq {n t : ℕ} (h : n = t)
    (A B : Set X) (hAB : A ⊆ B) (c : (integralSingularChains X).X n)
    (z : LinearMap.ker ((integralRelativeChains A).sc n).g.hom)
    (hz : (integralRelativeChainSequence A).g.f n c = z.val) :
    ∃ zB : LinearMap.ker ((integralRelativeChains B).sc t).g.hom,
      zB.val = (integralRelativeChainSequence B).g.f t
        (((integralSingularChains X).XIsoOfEq h).hom c) ∧
      moduleHomologyClass ((integralRelativeChains B).sc t) zB =
        eqToHom (congrArg (fun i => integralRelativeHomology i B) h)
          (integralRelativeHomologyMap n (ContinuousMap.id X) hAB
            (moduleHomologyClass ((integralRelativeChains A).sc n) z)) := by
  obtain ⟨zB, hval, hclass⟩ := exists_moduleCycle_map_of_eq
    (integralRelativeChainMap (ContinuousMap.id X) hAB) h z
  refine ⟨zB, ?_, hclass⟩
  rw [hval, ← hz]
  have hπ := integralRelativeChainMap_π (ContinuousMap.id X) hAB
  rw [integralSingularChainMap_id, Category.id_comp] at hπ
  have hπc := congrArg (fun f => f.f n c) hπ
  have hcast := congrArg (fun f => f c)
    (HomologicalComplex.XIsoOfEq_hom_naturality (integralRelativeChainSequence B).g h)
  change (integralRelativeChainMap (ContinuousMap.id X) hAB).f n
    ((integralRelativeChainSequence A).g.f n c) =
      (integralRelativeChainSequence B).g.f n c at hπc
  rw [hπc]
  exact hcast

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem moduleHomologyClass_eq_of_openExcision
    (n : ℕ) (A W : Set X) (hA : IsOpen A) (hW : IsOpen W) (hcover : A ∪ W = univ)
    (w : LinearMap.ker ((integralRelativeChains (subspaceIntersection A W)).sc n).g.hom)
    (z : LinearMap.ker ((integralRelativeChains A).sc n).g.hom)
    (hw : (integralRelativeChainMap (singularSubspaceInclusion W)
      (subspaceIntersection_mapsTo A W)).f n w.val = z.val)
    (ω : integralRelativeHomology n (subspaceIntersection A W))
    (hω : integralRelativeHomologyMap n (singularSubspaceInclusion W)
      (subspaceIntersection_mapsTo A W) ω =
        moduleHomologyClass ((integralRelativeChains A).sc n) z) :
    moduleHomologyClass ((integralRelativeChains (subspaceIntersection A W)).sc n) w = ω := by
  have hmap : integralRelativeHomologyMap n (singularSubspaceInclusion W)
      (subspaceIntersection_mapsTo A W)
      (moduleHomologyClass ((integralRelativeChains (subspaceIntersection A W)).sc n) w) =
        moduleHomologyClass ((integralRelativeChains A).sc n) z := by
    let f := integralRelativeChainMap (singularSubspaceInclusion W) (subspaceIntersection_mapsTo A W)
    let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ)
      (ComplexShape.down ℕ) n).map f
    change ShortComplex.homologyMap φ
      (moduleHomologyClass ((integralRelativeChains (subspaceIntersection A W)).sc n) w) = _
    rw [moduleHomologyClass_map]
    congr 1
    exact Subtype.ext hw
  apply (ModuleCat.mono_iff_injective
    (integralRelativeOpenExcisionIso n A W hA hW hcover).hom).mp inferInstance
  exact hmap.trans hω.symm

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem integralRelativeCohomologyCapToAbsolute_class_of_representative
    (A : Set X) (k m : ℕ)
    (φ : LinearMap.ker ((integralRelativeCochains A).sc k).g.hom)
    (c : (integralSingularChains X).X (k + m))
    (z : LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom)
    (hz : (integralRelativeChainSequence A).g.f (k + m) c = z.val)
    (r : LinearMap.ker ((integralSingularChains X).sc m).g.hom)
    (hr : r.val = integralSingularCapProduct k m
      ((integralRelativeCochainInclusion A).f k φ.val) c) :
    integralRelativeCohomologyCapToAbsolute A k m
        (moduleHomologyClass ((integralRelativeCochains A).sc k) φ)
        (moduleHomologyClass ((integralRelativeChains A).sc (k + m)) z) =
      moduleHomologyClass ((integralSingularChains X).sc m) r := by
  rw [integralRelativeCohomologyCapToAbsolute_class]
  congr 1
  apply Subtype.ext
  rw [integralRelativeCapToAbsoluteCycleMap_apply]
  exact (congrArg (integralRelativeCapProductToAbsolute A k m φ.val) hz).symm.trans
    ((integralRelativeCapProductToAbsolute_π A k m φ.val c).trans hr.symm)

private theorem integralRelativeCapProductToAbsolute_subspace_representative
    (A W : Set X) (k m : ℕ) (φ : (integralRelativeCochains A).X k)
    (c : (integralSingularChains X).X (k + m))
    (a : (integralSingularChains W).X (k + m))
    (hca : c - (integralSingularChainMap (singularSubspaceInclusion W)).f (k + m) a ∈
      integralSingularChainsIn (k + m) A) :
    (integralSingularChainMap (singularSubspaceInclusion W)).f m
        (integralRelativeCapProductToAbsolute (subspaceIntersection A W) k m
          ((integralRelativeCochainMap (singularSubspaceInclusion W)
            (show MapsTo (singularSubspaceInclusion W) (subspaceIntersection A W) A from
              fun _ hx => hx)).f k φ)
          ((integralRelativeChainSequence (subspaceIntersection A W)).g.f (k + m) a)) =
      integralSingularCapProduct k m ((integralRelativeCochainInclusion A).f k φ) c := by
  let η := (integralRelativeCochainInclusion A).f k φ
  have hη : integralSingularCochainPullback k (singularSubspaceInclusion A) η = 0 :=
    congrArg (fun f : integralRelativeCochains A ⟶ integralSingularCochains A => f.f k φ)
      (integralRelativeCochainInclusion_comp A)
  have hrem := integralSingularCapProduct_eq_zero_of_pullback_eq_zero k m η A hη hca
  rw [map_sub] at hrem
  have hφ := congrArg (fun f : integralRelativeCochains A ⟶ integralSingularCochains W => f.f k φ)
    (integralRelativeCochainMap_inclusion (singularSubspaceInclusion W)
      (show MapsTo (singularSubspaceInclusion W) (subspaceIntersection A W) A from
        fun _ hx => hx))
  change (integralRelativeCochainInclusion (subspaceIntersection A W)).f k
      ((integralRelativeCochainMap (singularSubspaceInclusion W)
        (show MapsTo (singularSubspaceInclusion W) (subspaceIntersection A W) A from
          fun _ hx => hx)).f k φ) =
    integralSingularCochainPullback k (singularSubspaceInclusion W) η at hφ
  have hn := LinearMap.congr_fun
    (integralSingularCapProduct_natural k m (singularSubspaceInclusion W) η) a
  rw [integralRelativeCapProductToAbsolute_π, hφ]
  exact hn.trans (sub_eq_zero.mp hrem).symm

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set

namespace DifferentialGeometry.Topology

variable {X : Type} [TopologicalSpace X]

private theorem integralRelativeCohomologyCapToAbsolute_mayerVietoris_representative
    (k m : ℕ) (U V A B : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : ∀ x : X, x ∈ U ∨ x ∈ V)
    (α : LinearMap.ker ((integralRelativeCochains (A ∩ B)).sc k).g.hom)
    (β : LinearMap.ker ((integralRelativeCochains (A ∪ B)).sc (k + 1)).g.hom)
    (p q : integralSingularCochain k X)
    (hp : integralSingularCochainPullback k (singularSubspaceInclusion A) p = 0)
    (hq : integralSingularCochainPullback k (singularSubspaceInclusion B) q = 0)
    (hpq : p + q = (integralRelativeCochainInclusion (A ∩ B)).f k α.val)
    (hdp : integralSingularCoboundary X k (k + 1) p =
      (integralRelativeCochainInclusion (A ∪ B)).f (k + 1) β.val)
    (c : (integralSingularChains X).X (k + m + 1))
    (hcU : c ∈ integralSingularSmallChains (k + m + 1) (twoSetCover U A))
    (hcV : c ∈ integralSingularSmallChains (k + m + 1) (twoSetCover V B))
    (hdc : (integralSingularChains X).d (k + m + 1) (k + m) c ∈
      integralSingularChainsIn (k + m) (A ∩ B))
    (z : LinearMap.ker ((integralRelativeChains (A ∩ B)).sc (k + m + 1)).g.hom)
    (hz : (integralRelativeChainSequence (A ∩ B)).g.f (k + m + 1) c = z.val)
    (a : (integralSingularChains ↥(U ∩ V)).X ((k + 1) + m))
    (w : LinearMap.ker
      ((integralRelativeChains (subspaceIntersection (A ∪ B) (U ∩ V))).sc ((k + 1) + m)).g.hom)
    (hw : (integralRelativeChainSequence (subspaceIntersection (A ∪ B) (U ∩ V))).g.f
      ((k + 1) + m) a = w.val)
    (hca : ((integralSingularChains X).XIsoOfEq
        (show k + m + 1 = (k + 1) + m by omega)).hom c -
      (integralSingularChainMap (singularSubspaceInclusion (U ∩ V))).f ((k + 1) + m) a ∈
        integralSingularChainsIn ((k + 1) + m) (A ∪ B)) :
    integralRelativeCohomologyCapToAbsolute (subspaceIntersection (A ∪ B) (U ∩ V))
        (k + 1) m
        (integralRelativeCohomologyMap (k + 1) (singularSubspaceInclusion (U ∩ V))
          (show MapsTo (singularSubspaceInclusion (U ∩ V))
            (subspaceIntersection (A ∪ B) (U ∩ V)) (A ∪ B) from fun _ hx => hx)
          (moduleHomologyClass ((integralRelativeCochains (A ∪ B)).sc (k + 1)) β))
        (moduleHomologyClass
          ((integralRelativeChains (subspaceIntersection (A ∪ B) (U ∩ V))).sc ((k + 1) + m)) w) =
      (-1 : ℤ) ^ (k + 1) •
        Homology.singularMayerVietorisConnectingMap integralSingularCoefficients
          (TopCat.of X) U V hU hV hUV m
          (integralRelativeCohomologyCapToAbsolute (A ∩ B) k (m + 1)
            (moduleHomologyClass ((integralRelativeCochains (A ∩ B)).sc k) α)
            (moduleHomologyClass ((integralRelativeChains (A ∩ B)).sc (k + m + 1)) z)) := by
  have hd : integralSingularCoboundary X k (k + 1) (p + q) = 0 := by
    rw [hpq]
    have h := congrArg (fun f : (integralRelativeCochains (A ∩ B)).X k ⟶
      (integralSingularCochains X).X (k + 1) => f α.val)
      ((integralRelativeCochainInclusion (A ∩ B)).comm k (k + 1))
    change integralSingularCoboundary X k (k + 1)
        ((integralRelativeCochainInclusion (A ∩ B)).f k α.val) =
      (integralRelativeCochainInclusion (A ∩ B)).f (k + 1)
        ((integralRelativeCochains (A ∩ B)).d k (k + 1) α.val) at h
    have hα := α.property
    change (integralRelativeCochains (A ∩ B)).d k ((ComplexShape.up ℕ).next k) α.val = 0 at hα
    rw [CochainComplex.next] at hα
    rw [h, hα, map_zero]
    rfl
  obtain ⟨r, s, hr, hδ, hs⟩ := exists_integralSingularCapProduct_mayerVietoris_cycles
    k m p q U V A B hU hV hUV hp hq hd c hcU hcV hdc
  have hrclass := integralRelativeCohomologyCapToAbsolute_class_of_representative
    (A ∩ B) k (m + 1) α c z hz r (hr.trans (by rw [hpq]))
  erw [hrclass, hδ]
  let f := integralRelativeCochainMap (singularSubspaceInclusion (U ∩ V))
    (show MapsTo (singularSubspaceInclusion (U ∩ V))
      (subspaceIntersection (A ∪ B) (U ∩ V)) (A ∪ B) from fun _ hx => hx)
  let P := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ)
    (ComplexShape.up ℕ) (k + 1)).map f
  let βW := moduleCycleMap P β
  have hβclass : integralRelativeCohomologyMap (k + 1) (singularSubspaceInclusion (U ∩ V))
      (show MapsTo (singularSubspaceInclusion (U ∩ V))
        (subspaceIntersection (A ∪ B) (U ∩ V)) (A ∪ B) from fun _ hx => hx)
      (moduleHomologyClass ((integralRelativeCochains (A ∪ B)).sc (k + 1)) β) =
    moduleHomologyClass
      ((integralRelativeCochains (subspaceIntersection (A ∪ B) (U ∩ V))).sc (k + 1)) βW :=
    moduleHomologyClass_map P β
  rw [hβclass, integralRelativeCohomologyCapToAbsolute_class]
  erw [← map_zsmul]
  congr 1
  apply Subtype.ext
  apply integralSingularChainInclusion_injective m (U ∩ V)
  rw [integralRelativeCapToAbsoluteCycleMap_apply]
  change (integralSingularChainMap (singularSubspaceInclusion (U ∩ V))).f m
      (integralRelativeCapProductToAbsolute (subspaceIntersection (A ∪ B) (U ∩ V))
        (k + 1) m (f.f (k + 1) β.val) w.val) =
    (integralSingularChainMap (singularSubspaceInclusion (U ∩ V))).f m
      ((-1 : ℤ) ^ (k + 1) • s.val)
  rw [← hw]
  erw [map_zsmul]
  exact (integralRelativeCapProductToAbsolute_subspace_representative (A ∪ B) (U ∩ V)
    (k + 1) m β.val _ a hca).trans (by simpa only [hdp] using hs)

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set

namespace DifferentialGeometry.Topology

variable {X : Type} [TopologicalSpace X]

private theorem integralSingularSmallChains_cast {n t : ℕ} (h : n = t)
    {ι : Type*} (U : ι → Set X) (c : (integralSingularChains X).X n)
    (hc : c ∈ integralSingularSmallChains n U) :
    ((integralSingularChains X).XIsoOfEq h).hom c ∈ integralSingularSmallChains t U := by
  subst t
  exact hc

omit [TopologicalSpace X] in
private theorem inter_union_cover (U V A B : Set X)
    (hUA : U ∪ A = univ) (hVB : V ∪ B = univ) :
    (A ∪ B) ∪ (U ∩ V) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hxUA : x ∈ U ∪ A := by rw [hUA]; trivial
  have hxVB : x ∈ V ∪ B := by rw [hVB]; trivial
  rcases hxUA with hxU | hxA
  · rcases hxVB with hxV | hxB
    · exact Or.inr ⟨hxU, hxV⟩
    · exact Or.inl (Or.inr hxB)
  · exact Or.inl (Or.inl hxA)

private theorem exists_relative_cap_mayerVietoris_representatives
    (k m : ℕ) (U V A B : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hA : IsOpen A) (hB : IsOpen B)
    (hUA : U ∪ A = univ) (hVB : V ∪ B = univ)
    (γ : integralRelativeHomology (k + m + 1) (A ∩ B))
    (ω : integralRelativeHomology ((k + 1) + m) (subspaceIntersection (A ∪ B) (U ∩ V)))
    (hω : integralRelativeHomologyMap ((k + 1) + m) (singularSubspaceInclusion (U ∩ V))
      (subspaceIntersection_mapsTo (A ∪ B) (U ∩ V)) ω =
        eqToHom (congrArg (fun i => integralRelativeHomology i (A ∪ B))
          (show k + m + 1 = (k + 1) + m by omega))
          (integralRelativeHomologyMap (k + m + 1) (ContinuousMap.id X)
            (show A ∩ B ⊆ A ∪ B from inter_subset_left.trans subset_union_left) γ)) :
    ∃ (c : (integralSingularChains X).X (k + m + 1))
      (z : LinearMap.ker ((integralRelativeChains (A ∩ B)).sc (k + m + 1)).g.hom)
      (a : (integralSingularChains ↥(U ∩ V)).X ((k + 1) + m))
      (w : LinearMap.ker
        ((integralRelativeChains (subspaceIntersection (A ∪ B) (U ∩ V))).sc ((k + 1) + m)).g.hom),
      c ∈ integralSingularSmallChains (k + m + 1) (twoSetCover U A) ∧
      c ∈ integralSingularSmallChains (k + m + 1) (twoSetCover V B) ∧
      (integralSingularChains X).d (k + m + 1) (k + m) c ∈
        integralSingularChainsIn (k + m) (A ∩ B) ∧
      (integralRelativeChainSequence (A ∩ B)).g.f (k + m + 1) c = z.val ∧
      moduleHomologyClass ((integralRelativeChains (A ∩ B)).sc (k + m + 1)) z = γ ∧
      (integralRelativeChainSequence (subspaceIntersection (A ∪ B) (U ∩ V))).g.f
        ((k + 1) + m) a = w.val ∧
      ((integralSingularChains X).XIsoOfEq
          (show k + m + 1 = (k + 1) + m by omega)).hom c -
        (integralSingularChainMap (singularSubspaceInclusion (U ∩ V))).f ((k + 1) + m) a ∈
          integralSingularChainsIn ((k + 1) + m) (A ∪ B) ∧
      moduleHomologyClass
        ((integralRelativeChains (subspaceIntersection (A ∪ B) (U ∩ V))).sc ((k + 1) + m)) w = ω := by
  let T : Fin 3 → Bool → Set X := ![twoSetCover U A, twoSetCover V B,
    twoSetCover (U ∩ V) (A ∪ B)]
  have hT : ∀ j i, IsOpen (T j i) := by
    intro j
    fin_cases j
    · exact twoSetCover_isOpen U A hU hA
    · exact twoSetCover_isOpen V B hV hB
    · exact twoSetCover_isOpen (U ∩ V) (A ∪ B) (hU.inter hV) (hA.union hB)
  have hcover : (A ∪ B) ∪ (U ∩ V) = univ := inter_union_cover U V A B hUA hVB
  have hcoverT : ∀ j x, ∃ i, x ∈ T j i := by
    intro j
    fin_cases j
    · exact twoSetCover_cover U A hUA
    · exact twoSetCover_cover V B hVB
    · exact twoSetCover_cover (U ∩ V) (A ∪ B) (by rw [union_comm]; exact hcover)
  obtain ⟨c, z, hc, hdc, hz, hzclass⟩ :=
    exists_small_relative_homology_representative_finite_covers (k + m + 1) (A ∩ B) T hT hcoverT γ
  have hdeg : k + m + 1 = (k + 1) + m := by omega
  obtain ⟨zB, hzB, hzBclass⟩ := exists_integralRelativeCycle_projection_of_eq hdeg
    (A ∩ B) (A ∪ B) (inter_subset_left.trans subset_union_left) c z hz
  obtain ⟨a, w, hw, hwmap, hca⟩ := exists_relative_subspace_cycle_of_small
    ((k + 1) + m) (U ∩ V) (A ∪ B) (((integralSingularChains X).XIsoOfEq hdeg).hom c)
    (integralSingularSmallChains_cast hdeg (twoSetCover (U ∩ V) (A ∪ B)) c (hc 2)) zB hzB.symm
  have hwclass : moduleHomologyClass
      ((integralRelativeChains (subspaceIntersection (A ∪ B) (U ∩ V))).sc ((k + 1) + m)) w = ω := by
    apply moduleHomologyClass_eq_of_openExcision ((k + 1) + m) (A ∪ B) (U ∩ V)
      (hA.union hB) (hU.inter hV) hcover w zB hwmap ω
    rw [hzBclass, hzclass]
    exact hω
  refine ⟨c, z, a, w, hc 0, hc 1, ?_, hz, hzclass, hw, hca, hwclass⟩
  have hnext : (ComplexShape.down ℕ).next (k + m + 1) = k + m :=
    (ComplexShape.down ℕ).next_eq' rfl
  rwa [hnext] at hdc

theorem integralRelativeCohomologyCapToAbsolute_mayerVietoris
    (k m : ℕ) (U V A B : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hA : IsOpen A) (hB : IsOpen B)
    (hUV : ∀ x : X, x ∈ U ∨ x ∈ V)
    (hUA : U ∪ A = univ) (hVB : V ∪ B = univ)
    (α : integralRelativeCohomology k (A ∩ B))
    (γ : integralRelativeHomology (k + m + 1) (A ∩ B))
    (ω : integralRelativeHomology ((k + 1) + m) (subspaceIntersection (A ∪ B) (U ∩ V)))
    (hω : integralRelativeHomologyMap ((k + 1) + m) (singularSubspaceInclusion (U ∩ V))
      (subspaceIntersection_mapsTo (A ∪ B) (U ∩ V)) ω =
        eqToHom (congrArg (fun i => integralRelativeHomology i (A ∪ B))
          (show k + m + 1 = (k + 1) + m by omega))
          (integralRelativeHomologyMap (k + m + 1) (ContinuousMap.id X)
            (show A ∩ B ⊆ A ∪ B from inter_subset_left.trans subset_union_left) γ)) :
    integralRelativeCohomologyCapToAbsolute (subspaceIntersection (A ∪ B) (U ∩ V))
        (k + 1) m
        (integralRelativeCohomologyMap (k + 1) (singularSubspaceInclusion (U ∩ V))
          (subspaceIntersection_mapsTo (A ∪ B) (U ∩ V))
          (integralRelativeMayerVietorisConnecting k A B hA hB α)) ω =
      (-1 : ℤ) ^ (k + 1) •
        Homology.singularMayerVietorisConnectingMap integralSingularCoefficients
          (TopCat.of X) U V hU hV hUV m
          (integralRelativeCohomologyCapToAbsolute (A ∩ B) k (m + 1) α γ) := by
  obtain ⟨φ, hφ⟩ := moduleHomologyClass_surjective ((integralRelativeCochains (A ∩ B)).sc k) α
  obtain ⟨β, p, q, hβ, hp, hq, hpq, hdp⟩ :=
    exists_integralRelativeMayerVietorisConnecting_cochain_representative k A B hA hB φ
  obtain ⟨c, z, a, w, hcU, hcV, hdc, hz, hzclass, hw, hca, hwclass⟩ :=
    exists_relative_cap_mayerVietoris_representatives k m U V A B hU hV hA hB hUA hVB γ ω hω
  have hs := integralRelativeCohomologyCapToAbsolute_mayerVietoris_representative
    k m U V A B hU hV hUV φ β p q hp hq hpq hdp c hcU hcV hdc z hz a w hw hca
  rw [hφ] at hβ
  rw [hφ, hzclass, hwclass, ← hβ] at hs
  exact hs

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set

namespace DifferentialGeometry.Topology

variable {X : Type} [TopologicalSpace X]

private theorem cap_mayerVietoris_set_transport
    (k m : ℕ) (U V A B C D : Set X)
    (hC : C = A ∩ B) (hD : D = A ∪ B)
    (hU : IsOpen U) (hV : IsOpen V) (hA : IsOpen A) (hB : IsOpen B)
    (hUV : ∀ x : X, x ∈ U ∨ x ∈ V)
    (hUA : U ∪ A = univ) (hVB : V ∪ B = univ)
    (α : integralRelativeCohomology k C)
    (γ : integralRelativeHomology (k + m + 1) C)
    (ω : integralRelativeHomology ((k + 1) + m) (subspaceIntersection D (U ∩ V)))
    (hω : integralRelativeHomologyMap ((k + 1) + m) (singularSubspaceInclusion (U ∩ V))
      (subspaceIntersection_mapsTo D (U ∩ V)) ω =
        eqToHom (congrArg (fun i => integralRelativeHomology i D)
          (show k + m + 1 = (k + 1) + m by omega))
          (integralRelativeHomologyMap (k + m + 1) (ContinuousMap.id X)
            (show C ⊆ D from by rw [hC, hD]; exact inter_subset_left.trans subset_union_left) γ)) :
    integralRelativeCohomologyCapToAbsolute (subspaceIntersection D (U ∩ V))
        (k + 1) m
        (integralRelativeCohomologyMap (k + 1) (singularSubspaceInclusion (U ∩ V))
          (subspaceIntersection_mapsTo D (U ∩ V))
          (eqToHom (congrArg (fun S => integralRelativeCohomology (k + 1) S) hD.symm)
            (integralRelativeMayerVietorisConnecting k A B hA hB
              (eqToHom (congrArg (fun S => integralRelativeCohomology k S) hC) α)))) ω =
      (-1 : ℤ) ^ (k + 1) •
        Homology.singularMayerVietorisConnectingMap integralSingularCoefficients
          (TopCat.of X) U V hU hV hUV m
          (integralRelativeCohomologyCapToAbsolute C k (m + 1) α γ) := by
  subst C
  subst D
  exact integralRelativeCohomologyCapToAbsolute_mayerVietoris
    k m U V A B hU hV hA hB hUV hUA hVB α γ ω hω

theorem integralCohomologyWithSupportCapToAbsolute_mayerVietoris
    (k m : ℕ) (U V K L : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsClosed K) (hL : IsClosed L)
    (hUV : ∀ x : X, x ∈ U ∨ x ∈ V) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (α : integralRelativeCohomology k (K ∪ L)ᶜ)
    (γ : integralRelativeHomology (k + m + 1) (K ∪ L)ᶜ)
    (ω : integralRelativeHomology ((k + 1) + m)
      (subspaceIntersection (K ∩ L)ᶜ (U ∩ V)))
    (hω : integralRelativeHomologyMap ((k + 1) + m) (singularSubspaceInclusion (U ∩ V))
      (subspaceIntersection_mapsTo (K ∩ L)ᶜ (U ∩ V)) ω =
        eqToHom (congrArg (fun i => integralRelativeHomology i (K ∩ L)ᶜ)
          (show k + m + 1 = (k + 1) + m by omega))
          (integralRelativeHomologyMap (k + m + 1) (ContinuousMap.id X)
            (show (K ∪ L)ᶜ ⊆ (K ∩ L)ᶜ from compl_subset_compl.mpr
              (inter_subset_left.trans subset_union_left)) γ)) :
    integralRelativeCohomologyCapToAbsolute (subspaceIntersection (K ∩ L)ᶜ (U ∩ V))
        (k + 1) m
        (integralRelativeCohomologyMap (k + 1) (singularSubspaceInclusion (U ∩ V))
          (subspaceIntersection_mapsTo (K ∩ L)ᶜ (U ∩ V))
          (integralCohomologyWithSupportMayerVietorisConnecting k K L hK hL α)) ω =
      (-1 : ℤ) ^ (k + 1) •
        Homology.singularMayerVietorisConnectingMap integralSingularCoefficients
          (TopCat.of X) U V hU hV hUV m
          (integralRelativeCohomologyCapToAbsolute (K ∪ L)ᶜ k (m + 1) α γ) := by
  have hUA : U ∪ Kᶜ = univ := by
    ext x
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hx : x ∈ K
    · exact Or.inl (hKU hx)
    · exact Or.inr hx
  have hVB : V ∪ Lᶜ = univ := by
    ext x
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hx : x ∈ L
    · exact Or.inl (hLV hx)
    · exact Or.inr hx
  exact cap_mayerVietoris_set_transport k m U V Kᶜ Lᶜ (K ∪ L)ᶜ (K ∩ L)ᶜ
    (compl_union K L) (compl_inter K L) hU hV hK.isOpen_compl hL.isOpen_compl
    hUV hUA hVB α γ ω hω

end DifferentialGeometry.Topology

end
