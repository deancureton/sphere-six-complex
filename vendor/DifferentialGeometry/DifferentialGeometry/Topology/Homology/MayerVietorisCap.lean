module

public import DifferentialGeometry.Topology.Homology.MayerVietoris
public import DifferentialGeometry.Topology.Homology.CapSupport

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace DifferentialGeometry.Topology

variable {X : Type} [TopologicalSpace X]

private theorem first_subspace_inclusion (U V : Set X) :
    SSet.chainComplexMap (Homology.firstSubspaceToSmall (TopCat.of X) U V)
        integralSingularCoefficients ≫
      Homology.smallChainMap (TopCat.of X) (Homology.twoSetFamily (TopCat.of X) U V)
        integralSingularCoefficients =
      integralSingularChainMap (singularSubspaceInclusion U) := by
  exact (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj integralSingularCoefficients).map_comp
    (Homology.firstSubspaceToSmall (TopCat.of X) U V)
    (Homology.smallSingularSimplices (TopCat.of X)
      (Homology.twoSetFamily (TopCat.of X) U V)).ι).symm

private theorem second_subspace_inclusion (U V : Set X) :
    SSet.chainComplexMap (Homology.secondSubspaceToSmall (TopCat.of X) U V)
        integralSingularCoefficients ≫
      Homology.smallChainMap (TopCat.of X) (Homology.twoSetFamily (TopCat.of X) U V)
        integralSingularCoefficients =
      integralSingularChainMap (singularSubspaceInclusion V) := by
  exact (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj integralSingularCoefficients).map_comp
    (Homology.secondSubspaceToSmall (TopCat.of X) U V)
    (Homology.smallSingularSimplices (TopCat.of X)
      (Homology.twoSetFamily (TopCat.of X) U V)).ι).symm

theorem integralSingularMayerVietorisConnectingMap_ambient_representative
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : ∀ x : X, x ∈ U ∨ x ∈ V) (m : ℕ)
    (a : (integralSingularChains U).X (m + 1))
    (b : (integralSingularChains V).X (m + 1))
    (z : LinearMap.ker ((integralSingularChains ↥(U ∩ V)).sc m).g.hom)
    (ha : (integralSingularChains U).d (m + 1) m a =
      (integralSingularChainMap (ContinuousMap.inclusion
        (show U ∩ V ⊆ U from Set.inter_subset_left))).f m z.val)
    (hb : (integralSingularChains V).d (m + 1) m b =
      -(integralSingularChainMap (ContinuousMap.inclusion
        (show U ∩ V ⊆ V from Set.inter_subset_right))).f m z.val) :
    ∃ c : LinearMap.ker ((integralSingularChains X).sc (m + 1)).g.hom,
      c.val = (integralSingularChainMap (singularSubspaceInclusion U)).f (m + 1) a +
        (integralSingularChainMap (singularSubspaceInclusion V)).f (m + 1) b ∧
      Homology.singularMayerVietorisConnectingMap integralSingularCoefficients
        (TopCat.of X) U V hU hV hUV m
          (moduleHomologyClass ((integralSingularChains X).sc (m + 1)) c) =
        moduleHomologyClass ((integralSingularChains ↥(U ∩ V)).sc m) z := by
  let P := SSet.chainComplexMap (Homology.firstSubspaceToSmall (TopCat.of X) U V)
    integralSingularCoefficients
  let Q := SSet.chainComplexMap (Homology.secondSubspaceToSmall (TopCat.of X) U V)
    integralSingularCoefficients
  let J := Homology.smallChainMap (TopCat.of X) (Homology.twoSetFamily (TopCat.of X) U V)
    integralSingularCoefficients
  let S := Homology.subspaceSmallShortComplex (TopCat.of X) U V integralSingularCoefficients
  let w := P.f (m + 1) a + Q.f (m + 1) b
  have hw : S.X₃.d (m + 1) m w = 0 := by
    have hP := congrArg (fun f => f a) (P.comm (m + 1) m)
    have hQ := congrArg (fun f => f b) (Q.comm (m + 1) m)
    change S.X₃.d (m + 1) m (P.f (m + 1) a) =
      P.f m ((integralSingularChains U).d (m + 1) m a) at hP
    change S.X₃.d (m + 1) m (Q.f (m + 1) b) =
      Q.f m ((integralSingularChains V).d (m + 1) m b) at hQ
    change S.X₃.d (m + 1) m (P.f (m + 1) a + Q.f (m + 1) b) = 0
    rw [map_add, hP, hQ, ha, hb]
    have hneg := map_neg (Q.f m).hom
      ((integralSingularChainMap (ContinuousMap.inclusion
        (show U ∩ V ⊆ V from Set.inter_subset_right))).f m z.val)
    have hsq := (Homology.subspaceSmallChainSquare (TopCat.of X) U V
      integralSingularCoefficients).w
    have h := congrArg (fun f => f.f m z.val) hsq
    change P.f m ((integralSingularChainMap (ContinuousMap.inclusion
      (show U ∩ V ⊆ U from Set.inter_subset_left))).f m z.val) =
      Q.f m ((integralSingularChainMap (ContinuousMap.inclusion
        (show U ∩ V ⊆ V from Set.inter_subset_right))).f m z.val) at h
    exact (congrArg (fun y => P.f m ((integralSingularChainMap (ContinuousMap.inclusion
      (show U ∩ V ⊆ U from Set.inter_subset_left))).f m z.val) + y) hneg).trans
      (by
        change P.f m ((integralSingularChainMap (ContinuousMap.inclusion
          (show U ∩ V ⊆ U from Set.inter_subset_left))).f m z.val) +
          -(Q.f m ((integralSingularChainMap (ContinuousMap.inclusion
            (show U ∩ V ⊆ V from Set.inter_subset_right))).f m z.val)) = 0
        exact (congrArg (fun x => x + -(Q.f m ((integralSingularChainMap (ContinuousMap.inclusion
          (show U ∩ V ⊆ V from Set.inter_subset_right))).f m z.val))) h).trans
            (add_neg_cancel _))
  let wc : LinearMap.ker (S.X₃.sc (m + 1)).g.hom := ⟨w, by
    change S.X₃.d (m + 1) ((ComplexShape.down ℕ).next (m + 1)) w = 0
    rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (m + 1) m from rfl)]
    exact hw⟩
  let f := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ)
    (ComplexShape.down ℕ) (m + 1)).map J
  let c := moduleCycleMap f wc
  have hc : c.val = (integralSingularChainMap (singularSubspaceInclusion U)).f (m + 1) a +
      (integralSingularChainMap (singularSubspaceInclusion V)).f (m + 1) b := by
    change J.f (m + 1) (P.f (m + 1) a + Q.f (m + 1) b) = _
    rw [map_add]
    have hp := congrArg (fun g => g.f (m + 1) a) (first_subspace_inclusion U V)
    have hq := congrArg (fun g => g.f (m + 1) b) (second_subspace_inclusion U V)
    exact congrArg₂ (· + ·) hp hq
  refine ⟨c, hc, ?_⟩
  have hclass := moduleHomologyClass_map f wc
  have h := Homology.singularMayerVietorisConnectingMap_representative
    integralSingularCoefficients (TopCat.of X) U V hU hV hUV m wc a b rfl z ha.symm hb.symm
  have he : HomologicalComplex.homologyMap J (m + 1)
      (moduleHomologyClass (S.X₃.sc (m + 1)) wc) =
      moduleHomologyClass ((integralSingularChains X).sc (m + 1)) c := hclass
  exact (congrArg (Homology.singularMayerVietorisConnectingMap integralSingularCoefficients
    (TopCat.of X) U V hU hV hUV m) he).symm.trans h

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set

namespace DifferentialGeometry.Topology

variable {X : Type} [TopologicalSpace X]

theorem exists_integralSingularCapProduct_mayerVietoris_cycles
    (k m : ℕ) (φ ψ : integralSingularCochain k X) (U V A B : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : ∀ x : X, x ∈ U ∨ x ∈ V)
    (hφ : integralSingularCochainPullback k (singularSubspaceInclusion A) φ = 0)
    (hψ : integralSingularCochainPullback k (singularSubspaceInclusion B) ψ = 0)
    (hd : integralSingularCoboundary X k (k + 1) (φ + ψ) = 0)
    (c : (integralSingularChains X).X (k + m + 1))
    (hcU : c ∈ integralSingularSmallChains (k + m + 1) (twoSetCover U A))
    (hcV : c ∈ integralSingularSmallChains (k + m + 1) (twoSetCover V B))
    (hc : (integralSingularChains X).d (k + m + 1) (k + m) c ∈
      integralSingularChainsIn (k + m) (A ∩ B)) :
    ∃ r : LinearMap.ker ((integralSingularChains X).sc (m + 1)).g.hom,
      ∃ z : LinearMap.ker ((integralSingularChains ↥(U ∩ V)).sc m).g.hom,
        r.val = integralSingularCapProduct k (m + 1) (φ + ψ) c ∧
        Homology.singularMayerVietorisConnectingMap integralSingularCoefficients
          (TopCat.of X) U V hU hV hUV m
            (moduleHomologyClass ((integralSingularChains X).sc (m + 1)) r) =
          moduleHomologyClass ((integralSingularChains ↥(U ∩ V)).sc m) z ∧
        integralSingularCapProduct (k + 1) m (integralSingularCoboundary X k (k + 1) φ)
            (((integralSingularChains X).XIsoOfEq
              (show k + m + 1 = (k + 1) + m by omega)).hom c) =
          (-1 : ℤ) ^ (k + 1) •
            (integralSingularChainMap (singularSubspaceInclusion (U ∩ V))).f m z.val := by
  obtain ⟨a, b, z, ha, hb, hda, hdb, hsign⟩ :=
    exists_integralSingularCapProduct_inter_boundary_cycle k m φ ψ U V A B
      hφ hψ hd c hcU hcV hc
  obtain ⟨r, hr, hδ⟩ := integralSingularMayerVietorisConnectingMap_ambient_representative
    U V hU hV hUV m a b z hda hdb
  refine ⟨r, z, ?_, hδ, hsign⟩
  rw [hr, ha, hb, map_add, LinearMap.add_apply]

end DifferentialGeometry.Topology

end
