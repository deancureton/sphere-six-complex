module

public import DifferentialGeometry.Topology.Homology.Relative.Basic
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ContractiblePair
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeFunctoriality
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionIterationHomotopy

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem chainComplex_homologyMap_liftCycles_apply
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (φ : K ⟶ L) (n : ℕ)
    (z : integralSingularCoefficients ⟶ K.X (n + 1)) (hz : z ≫ K.d (n + 1) n = 0)
    (h : (z ≫ φ.f (n + 1)) ≫ L.d (n + 1) n = 0) :
    (HomologicalComplex.homologyMap φ (n + 1)).hom
      (((K.liftCycles z n ((ComplexShape.down ℕ).next_eq' (by rfl)) hz) ≫ K.homologyπ (n + 1))
        (ULift.up 1)) =
      (((L.liftCycles (z ≫ φ.f (n + 1)) n ((ComplexShape.down ℕ).next_eq' (by rfl)) h) ≫
        L.homologyπ (n + 1)) (ULift.up 1)) := by
  have hm :
      (K.liftCycles z n ((ComplexShape.down ℕ).next_eq' (by rfl)) hz ≫ K.homologyπ (n + 1)) ≫
        HomologicalComplex.homologyMap φ (n + 1) =
      L.liftCycles (z ≫ φ.f (n + 1)) n ((ComplexShape.down ℕ).next_eq' (by rfl)) h ≫
        L.homologyπ (n + 1) := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      HomologicalComplex.liftCycles_comp_cyclesMap]
  exact congrArg (fun k : integralSingularCoefficients ⟶ L.homology (n + 1) => k (ULift.up 1)) hm

theorem chainComplex_liftCycles_homologyπ_congr
    {K : ChainComplex (ModuleCat.{u} ℤ) ℕ} (n : ℕ)
    (k₁ k₂ : integralSingularCoefficients ⟶ K.X (n + 1))
    (h₁ : k₁ ≫ K.d (n + 1) n = 0) (h₂ : k₂ ≫ K.d (n + 1) n = 0) (h : k₁ = k₂) :
    (K.liftCycles k₁ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₁ ≫ K.homologyπ (n + 1)) =
      (K.liftCycles k₂ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₂ ≫ K.homologyπ (n + 1)) := by
  cases h
  have heq : K.liftCycles k₁ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₁ =
      K.liftCycles k₁ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₂ :=
    (cancel_mono (K.iCycles (n + 1))).mp (by
      rw [HomologicalComplex.liftCycles_i])
  rw [heq]

theorem chainComplex_liftCycles_homologyπ_boundary
    {K : ChainComplex (ModuleCat.{u} ℤ) ℕ} (n : ℕ)
    (w : integralSingularCoefficients ⟶ K.X (n + 2))
    (h : (w ≫ K.d (n + 2) (n + 1)) ≫ K.d (n + 1) n = 0) :
    K.liftCycles (w ≫ K.d (n + 2) (n + 1)) n ((ComplexShape.down ℕ).next_eq' (by rfl)) h ≫
      K.homologyπ (n + 1) = 0 := by
  rw [chainComplex_liftCycles_homologyπ_congr n (w ≫ K.d (n + 2) (n + 1))
    (w ≫ K.d (n + 2) (n + 1)) h _ rfl]
  exact K.liftCycles_homologyπ_eq_zero_of_boundary (w ≫ K.d (n + 2) (n + 1)) n
    ((ComplexShape.down ℕ).next_eq' (by rfl)) w rfl

theorem chainComplex_liftCycles_homologyπ_congr_of_sub_eq_boundary
    {K : ChainComplex (ModuleCat.{u} ℤ) ℕ} (n : ℕ)
    (k₁ k₂ : integralSingularCoefficients ⟶ K.X (n + 1))
    (h₁ : k₁ ≫ K.d (n + 1) n = 0) (h₂ : k₂ ≫ K.d (n + 1) n = 0)
    (w : integralSingularCoefficients ⟶ K.X (n + 2))
    (hw : k₁ - k₂ = w ≫ K.d (n + 2) (n + 1)) :
    K.liftCycles k₁ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₁ ≫ K.homologyπ (n + 1) =
      K.liftCycles k₂ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₂ ≫ K.homologyπ (n + 1) := by
  have hsub : K.liftCycles k₁ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₁ -
        K.liftCycles k₂ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₂ =
      K.liftCycles (k₁ - k₂) n ((ComplexShape.down ℕ).next_eq' (by rfl))
        (by rw [Preadditive.sub_comp, h₁, h₂, sub_self]) := by
    apply (cancel_mono (K.iCycles (n + 1))).mp
    rw [Preadditive.sub_comp, HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i,
      HomologicalComplex.liftCycles_i]
  have hzero : (K.liftCycles k₁ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₁ -
      K.liftCycles k₂ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₂) ≫ K.homologyπ (n + 1) = 0 := by
    rw [hsub]
    rw [chainComplex_liftCycles_homologyπ_congr n (k₁ - k₂) (w ≫ K.d (n + 2) (n + 1))
      (by rw [Preadditive.sub_comp, h₁, h₂, sub_self])
      (by rw [Category.assoc, HomologicalComplex.d_comp_d, comp_zero]) hw]
    exact chainComplex_liftCycles_homologyπ_boundary n w _
  have hzero' : K.liftCycles k₁ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₁ ≫ K.homologyπ (n + 1) -
      K.liftCycles k₂ n ((ComplexShape.down ℕ).next_eq' (by rfl)) h₂ ≫ K.homologyπ (n + 1) = 0 := by
    simpa only [Preadditive.sub_comp] using hzero
  exact sub_eq_zero.mp hzero'

theorem integralHomologyContractibleCoverEquiv_liftCycles_apply (n : ℕ) (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 2))
    (hz : z ≫ (integralSingularChains X).d (n + 2) (n + 1) = 0)
    (zA : integralSingularCoefficients ⟶ (integralSingularChains A).X (n + 2))
    (zB : integralSingularCoefficients ⟶ (integralSingularChains B).X (n + 2))
    (hsplit : zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 2) +
      zB ≫ (integralSingularChainMap (singularSubspaceInclusion B)).f (n + 2) = z)
    (a : integralSingularCoefficients ⟶
      (integralSingularChains (subspaceIntersection A B)).X (n + 1))
    (hac : a ≫ (integralSingularChains (subspaceIntersection A B)).d (n + 1) n = 0)
    (ha : a ≫ (integralSingularChainMap
        (singularSubspaceInclusion (subspaceIntersection A B))).f (n + 1) =
      zB ≫ (integralSingularChains B).d (n + 2) (n + 1)) :
    integralHomologyContractibleCoverEquiv n A B hA hB hcover
      (((integralSingularChains X).liftCycles z (n + 1) ((ComplexShape.down ℕ).next_eq' (by rfl)) hz ≫
        (integralSingularChains X).homologyπ (n + 2)) (ULift.up 1)) =
      (((integralSingularChains (subspaceIntersection A B)).liftCycles a n
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hac ≫
        (integralSingularChains (subspaceIntersection A B)).homologyπ (n + 1)) (ULift.up 1)) := by
  have hdecomp : (integralHomologyContractibleCoverEquiv (X := X) n A B hA hB hcover).toLinearMap =
      (integralRelativeConnectingEquivOfContractible (X := B) (n + 1) (by omega)
        (subspaceIntersection A B)).toLinearMap.comp
      (((integralRelativeOpenExcisionIso (X := X) (n + 2) A B hA hB hcover).symm.toLinearEquiv.toLinearMap).comp
        (integralAbsoluteToRelativeIsoOfContractible (X := X) n A).toLinearEquiv.toLinearMap) := by
    rw [integralHomologyContractibleCoverEquiv]
    rfl
  have hdecomp_fun :
      ⇑(integralHomologyContractibleCoverEquiv (X := X) n A B hA hB hcover) =
        ⇑((integralRelativeConnectingEquivOfContractible (X := B) (n + 1) (by omega)
          (subspaceIntersection A B)).toLinearMap.comp
        (((integralRelativeOpenExcisionIso (X := X) (n + 2) A B hA hB hcover).symm.toLinearEquiv.toLinearMap).comp
          (integralAbsoluteToRelativeIsoOfContractible (X := X) n A).toLinearEquiv.toLinearMap)) := by
    funext x
    exact DFunLike.congr_fun hdecomp x
  rw [hdecomp_fun, LinearMap.comp_apply, LinearMap.comp_apply]
  let πA : integralSingularChains X ⟶ integralRelativeChains A :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))
  let πI : integralSingularChains B ⟶ integralRelativeChains (subspaceIntersection A B) :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion (subspaceIntersection A B)))
  let ι : integralRelativeChains (subspaceIntersection A B) ⟶ integralRelativeChains A :=
    integralRelativeChainMap (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B)
  have hzA : (z ≫ πA.f (n + 2)) ≫ (integralRelativeChains A).d (n + 2) (n + 1) = 0 := by
    rw [Category.assoc, HomologicalComplex.Hom.comm, ← Category.assoc, hz, zero_comp]
  have hcondA :
      (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 2) ≫ πA.f (n + 2) = 0 := by
    have h : ((integralSingularChainMap (singularSubspaceInclusion A) ≫
        cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))).f (n + 2)) = 0 := by
      rw [cokernel.condition (integralSingularChainMap (singularSubspaceInclusion A)),
        HomologicalComplex.zero_f]
    rw [HomologicalComplex.comp_f] at h
    exact h
  have hzI :
      (zB ≫ πI.f (n + 2)) ≫
        (integralRelativeChains (subspaceIntersection A B)).d (n + 2) (n + 1) = 0 := by
    have hcondI : (integralSingularChainMap
        (singularSubspaceInclusion (subspaceIntersection A B))).f (n + 1) ≫ πI.f (n + 1) = 0 := by
      have h : ((integralSingularChainMap (singularSubspaceInclusion (subspaceIntersection A B)) ≫
          cokernel.π (integralSingularChainMap
            (singularSubspaceInclusion (subspaceIntersection A B)))).f (n + 1)) = 0 := by
        rw [cokernel.condition (integralSingularChainMap
            (singularSubspaceInclusion (subspaceIntersection A B))), HomologicalComplex.zero_f]
      rw [HomologicalComplex.comp_f] at h
      exact h
    rw [Category.assoc, HomologicalComplex.Hom.comm, ← Category.assoc, ← ha, Category.assoc, hcondI,
      comp_zero]
  have hchain : (zB ≫ πI.f (n + 2)) ≫ ι.f (n + 2) = z ≫ πA.f (n + 2) := by
    have hπ : πI ≫ ι = (integralSingularChainMap (singularSubspaceInclusion B)) ≫ πA :=
      integralRelativeChainMap_π (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B)
    have hπf : πI.f (n + 2) ≫ ι.f (n + 2) =
        (integralSingularChainMap (singularSubspaceInclusion B)).f (n + 2) ≫ πA.f (n + 2) := by
      have h : (πI ≫ ι).f (n + 2) =
          ((integralSingularChainMap (singularSubspaceInclusion B)) ≫ πA).f (n + 2) := by
        rw [hπ]
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at h
      exact h
    have hsplit' : zB ≫ (integralSingularChainMap (singularSubspaceInclusion B)).f (n + 2) =
        z - zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 2) := by
      rw [← hsplit]
      abel
    rw [Category.assoc, hπf, ← Category.assoc, hsplit', Preadditive.sub_comp, Category.assoc, hcondA,
      comp_zero, sub_zero]
  have h1 : (integralAbsoluteToRelativeIsoOfContractible (X := X) n A).toLinearEquiv
      (((integralSingularChains X).liftCycles z (n + 1) ((ComplexShape.down ℕ).next_eq' (by rfl)) hz ≫
        (integralSingularChains X).homologyπ (n + 2)) (ULift.up 1)) =
      (((integralRelativeChains A).liftCycles (z ≫ πA.f (n + 2)) (n + 1)
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hzA ≫
        (integralRelativeChains A).homologyπ (n + 2)) (ULift.up 1)) := by
    change (HomologicalComplex.homologyMap πA (n + 2)).hom
      (((integralSingularChains X).liftCycles z (n + 1) ((ComplexShape.down ℕ).next_eq' (by rfl)) hz ≫
        (integralSingularChains X).homologyπ (n + 2)) (ULift.up 1)) =
      (((integralRelativeChains A).liftCycles (z ≫ πA.f (n + 2)) (n + 1)
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hzA ≫
        (integralRelativeChains A).homologyπ (n + 2)) (ULift.up 1))
    exact chainComplex_homologyMap_liftCycles_apply πA (n + 1) z hz hzA
  have h2 : (integralRelativeOpenExcisionIso (X := X) (n + 2) A B hA hB hcover).symm.toLinearEquiv
      (((integralRelativeChains A).liftCycles (z ≫ πA.f (n + 2)) (n + 1)
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hzA ≫
        (integralRelativeChains A).homologyπ (n + 2)) (ULift.up 1)) =
      (((integralRelativeChains (subspaceIntersection A B)).liftCycles (zB ≫ πI.f (n + 2)) (n + 1)
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hzI ≫
        (integralRelativeChains (subspaceIntersection A B)).homologyπ (n + 2)) (ULift.up 1)) := by
    rw [← Iso.toLinearEquiv_symm]
    have hstep : (integralRelativeOpenExcisionIso (X := X) (n + 2) A B hA hB hcover).toLinearEquiv
        (((integralRelativeChains (subspaceIntersection A B)).liftCycles (zB ≫ πI.f (n + 2)) (n + 1)
          ((ComplexShape.down ℕ).next_eq' (by rfl)) hzI ≫
          (integralRelativeChains (subspaceIntersection A B)).homologyπ (n + 2)) (ULift.up 1)) =
        (((integralRelativeChains A).liftCycles (z ≫ πA.f (n + 2)) (n + 1)
          ((ComplexShape.down ℕ).next_eq' (by rfl)) hzA ≫
          (integralRelativeChains A).homologyπ (n + 2)) (ULift.up 1)) := by
      change (HomologicalComplex.homologyMap ι (n + 2)).hom
        (((integralRelativeChains (subspaceIntersection A B)).liftCycles (zB ≫ πI.f (n + 2)) (n + 1)
          ((ComplexShape.down ℕ).next_eq' (by rfl)) hzI ≫
          (integralRelativeChains (subspaceIntersection A B)).homologyπ (n + 2)) (ULift.up 1)) =
        (((integralRelativeChains A).liftCycles (z ≫ πA.f (n + 2)) (n + 1)
          ((ComplexShape.down ℕ).next_eq' (by rfl)) hzA ≫
          (integralRelativeChains A).homologyπ (n + 2)) (ULift.up 1))
      have hzι : ((zB ≫ πI.f (n + 2)) ≫ ι.f (n + 2)) ≫
          (integralRelativeChains A).d (n + 2) (n + 1) = 0 := by
        rw [hchain, Category.assoc, HomologicalComplex.Hom.comm, ← Category.assoc, hz, zero_comp]
      refine (chainComplex_homologyMap_liftCycles_apply ι (n + 1) (zB ≫ πI.f (n + 2)) hzI
        hzι).trans ?_
      exact congrArg (fun k : integralSingularCoefficients ⟶ (integralRelativeChains A).homology (n + 2) =>
        k (ULift.up 1)) (chainComplex_liftCycles_homologyπ_congr (n + 1)
          ((zB ≫ πI.f (n + 2)) ≫ ι.f (n + 2)) (z ≫ πA.f (n + 2)) hzι hzA hchain)
    rw [← hstep, LinearEquiv.symm_apply_apply]
  have hconn : (integralRelativeConnectingEquivOfContractible (X := B) (n + 1) (by omega)
      (subspaceIntersection A B)).toLinearMap = integralRelativeConnecting (n + 1)
        (subspaceIntersection A B) := rfl
  have h3 : (integralRelativeConnectingEquivOfContractible (X := B) (n + 1) (by omega)
      (subspaceIntersection A B))
      (((integralRelativeChains (subspaceIntersection A B)).liftCycles (zB ≫ πI.f (n + 2)) (n + 1)
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hzI ≫
        (integralRelativeChains (subspaceIntersection A B)).homologyπ (n + 2)) (ULift.up 1)) =
      (((integralSingularChains (subspaceIntersection A B)).liftCycles a n
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hac ≫
        (integralSingularChains (subspaceIntersection A B)).homologyπ (n + 1)) (ULift.up 1)) := by
    have hconn' : ⇑(integralRelativeConnectingEquivOfContractible (X := B) (n + 1) (by omega)
        (subspaceIntersection A B)) = ⇑(integralRelativeConnecting (n + 1)
          (subspaceIntersection A B)) := by
      funext x
      exact DFunLike.congr_fun hconn x
    rw [hconn']
    exact integralRelativeConnecting_liftCycles_apply n (subspaceIntersection A B) zB hzI a hac ha
  let cn : integralRelativeHomology (n + 2) (subspaceIntersection A B) →
      integralSingularHomology (n + 1) (subspaceIntersection A B) :=
    fun x => integralRelativeConnectingEquivOfContractible (X := B) (n + 1) (by omega)
      (subspaceIntersection A B) x
  let ex : integralRelativeHomology (n + 2) A →
      integralRelativeHomology (n + 2) (subspaceIntersection A B) :=
    fun x => (integralRelativeOpenExcisionIso (X := X) (n + 2) A B hA hB hcover).symm.toLinearEquiv x
  exact ((congrArg (fun x => cn (ex x)) h1).trans (congrArg cn h2)).trans h3

theorem integralSingularCoefficients_hom_ext {M : ModuleCat.{u} ℤ}
    (f g : integralSingularCoefficients ⟶ M)
    (h : f (ULift.up (1 : ℤ)) = g (ULift.up (1 : ℤ))) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨m⟩ := x
  have hmul : (ULift.up m : ULift.{u} ℤ) = m • (ULift.up (1 : ℤ) : ULift.{u} ℤ) := by
    ext
    simp
  rw [hmul]
  rw [map_zsmul, map_zsmul, h]

def integralSingularChainOfElement {M : ModuleCat.{u} ℤ} (c : M) :
    integralSingularCoefficients ⟶ M :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton ℤ M c).comp
    (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ).toLinearMap)

theorem integralSingularChainOfElement_apply_one {M : ModuleCat.{u} ℤ} (c : M) :
    integralSingularChainOfElement c (ULift.up (1 : ℤ)) = c := by
  change (LinearMap.toSpanSingleton ℤ M c)
    ((ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ) (ULift.up (1 : ℤ))) = c
  simp only [ULift.moduleEquiv_apply, LinearMap.toSpanSingleton_apply_one]

theorem integralSingularChainOfElement_comp {M N : ModuleCat.{u} ℤ} (f : M ⟶ N) (c : M) :
    integralSingularChainOfElement c ≫ f = integralSingularChainOfElement (f c) := by
  apply integralSingularCoefficients_hom_ext
  simp [integralSingularChainOfElement]

def integralSingularSubdivisionIterateChain (n k : ℕ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1)) :
    integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1) :=
  z ≫ ModuleCat.ofHom (integralSingularSubdivisionIterate (n + 1) k)

theorem integralSingularSubdivisionIterate_cycle (n k : ℕ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1))
    (hz : z ≫ (integralSingularChains X).d (n + 1) n = 0) :
    integralSingularSubdivisionIterateChain n k z ≫
      (integralSingularChains X).d (n + 1) n = 0 := by
  apply integralSingularCoefficients_hom_ext
  change (integralSingularChains X).d (n + 1) n
      (integralSingularSubdivisionIterate (n + 1) k (z (ULift.up (1 : ℤ)))) = 0
  rw [integralSingularSubdivisionIterate_boundary]
  have hz1 : (integralSingularChains X).d (n + 1) n (z (ULift.up (1 : ℤ))) = 0 := by
    have h := congrArg (fun f : integralSingularCoefficients ⟶ (integralSingularChains X).X n =>
      f (ULift.up (1 : ℤ))) hz
    simpa using h
  rw [hz1, map_zero]

def integralSingularSubdivisionIterateHomotopyChain (n k : ℕ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1)) :
    integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 2) :=
  Neg.neg (z ≫ ModuleCat.ofHom (integralSingularSubdivisionIterateHomotopy (n + 1) k))

theorem integralSingularSubdivisionIterate_sub_eq_boundary (n k : ℕ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1))
    (hz : z ≫ (integralSingularChains X).d (n + 1) n = 0) :
    integralSingularSubdivisionIterateChain n k z - z =
      integralSingularSubdivisionIterateHomotopyChain n k z ≫
        (integralSingularChains X).d (n + 2) (n + 1) := by
  apply integralSingularCoefficients_hom_ext
  change integralSingularSubdivisionIterate (n + 1) k (z (ULift.up (1 : ℤ))) -
      z (ULift.up (1 : ℤ)) =
    (integralSingularChains X).d (n + 2) (n + 1)
      (-(integralSingularSubdivisionIterateHomotopy (n + 1) k (z (ULift.up (1 : ℤ)))))
  have hz1 : (integralSingularChains X).d (n + 1) n (z (ULift.up (1 : ℤ))) = 0 := by
    have h := congrArg (fun f : integralSingularCoefficients ⟶ (integralSingularChains X).X n =>
      f (ULift.up (1 : ℤ))) hz
    simpa using h
  rw [map_neg, integralSingularSubdivisionIterateHomotopy_cycle n k (z (ULift.up (1 : ℤ))) hz1]
  abel

theorem integralSingularSubdivisionIterate_liftCycles_homologyπ (n k : ℕ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1))
    (hz : z ≫ (integralSingularChains X).d (n + 1) n = 0)
    (hs : integralSingularSubdivisionIterateChain n k z ≫
      (integralSingularChains X).d (n + 1) n = 0) :
    (integralSingularChains X).liftCycles
        (integralSingularSubdivisionIterateChain n k z) n
        ((ComplexShape.down ℕ).next_eq' (by rfl))
        hs ≫
      (integralSingularChains X).homologyπ (n + 1) =
    (integralSingularChains X).liftCycles z n ((ComplexShape.down ℕ).next_eq' (by rfl)) hz ≫
      (integralSingularChains X).homologyπ (n + 1) :=
  chainComplex_liftCycles_homologyπ_congr_of_sub_eq_boundary n
    (integralSingularSubdivisionIterateChain n k z) z
    hs hz
    (integralSingularSubdivisionIterateHomotopyChain n k z)
    (integralSingularSubdivisionIterate_sub_eq_boundary n k z hz)

theorem integralHomologyContractibleCoverEquiv_liftCycles_apply_of_subdivision (n k : ℕ)
    (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 2))
    (hz : z ≫ (integralSingularChains X).d (n + 2) (n + 1) = 0)
    (zA : integralSingularCoefficients ⟶ (integralSingularChains A).X (n + 2))
    (zB : integralSingularCoefficients ⟶ (integralSingularChains B).X (n + 2))
    (hsplit : zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 2) +
      zB ≫ (integralSingularChainMap (singularSubspaceInclusion B)).f (n + 2) =
        integralSingularSubdivisionIterateChain (n + 1) k z)
    (a : integralSingularCoefficients ⟶
      (integralSingularChains (subspaceIntersection A B)).X (n + 1))
    (hac : a ≫ (integralSingularChains (subspaceIntersection A B)).d (n + 1) n = 0)
    (ha : a ≫ (integralSingularChainMap
        (singularSubspaceInclusion (subspaceIntersection A B))).f (n + 1) =
      zB ≫ (integralSingularChains B).d (n + 2) (n + 1)) :
    integralHomologyContractibleCoverEquiv n A B hA hB hcover
      (((integralSingularChains X).liftCycles z (n + 1) ((ComplexShape.down ℕ).next_eq' (by rfl)) hz ≫
        (integralSingularChains X).homologyπ (n + 2)) (ULift.up 1)) =
      (((integralSingularChains (subspaceIntersection A B)).liftCycles a n
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hac ≫
        (integralSingularChains (subspaceIntersection A B)).homologyπ (n + 1)) (ULift.up 1)) := by
  rw [← congrArg (fun f => f (ULift.up 1))
    (integralSingularSubdivisionIterate_liftCycles_homologyπ (n + 1) k z hz
      (integralSingularSubdivisionIterate_cycle (n + 1) k z hz))]
  exact integralHomologyContractibleCoverEquiv_liftCycles_apply n A B hA hB hcover
    (integralSingularSubdivisionIterateChain (n + 1) k z)
    (integralSingularSubdivisionIterate_cycle (n + 1) k z hz)
    zA zB hsplit a hac ha

end DifferentialGeometry.Topology
