module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCapToAbsoluteHomology
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyConnecting

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace DifferentialGeometry.Topology

private theorem moduleHomologyClass_transport
    {R : Type u} [Ring R] {ι : Type*} {shape : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) shape) {i j : ι} (h : i = j)
    (c : LinearMap.ker (K.sc i).g.hom) :
    (eqToHom (congrArg (fun n => K.homology n) h)) (moduleHomologyClass (K.sc i) c) =
      moduleHomologyClass (K.sc j)
        ⟨(K.XIsoOfEq h).hom c.val, by subst j; exact c.property⟩ := by
  subst j
  rfl

variable {X : Type u} [TopologicalSpace X]

local instance RelativeCapCohomologyConnecting.connectingCycle_module (S : ShortComplex (ModuleCat.{u} ℤ)) :
    Module ℤ (LinearMap.ker S.g.hom) := (LinearMap.ker S.g.hom).module

private theorem connecting_absolute_cocycle_closed {Y : Type u} [TopologicalSpace Y] (k : ℕ)
    (φ : LinearMap.ker ((integralSingularCochains Y).sc k).g.hom) :
    integralSingularCoboundary Y k (k + 1) φ.val = 0 := by
  have h := φ.property
  change integralSingularCoboundary Y k ((ComplexShape.up ℕ).next k) φ.val = 0 at h
  rwa [CochainComplex.next] at h

private theorem cohomology_cap_connecting_class (A : Set X) (k m : ℕ)
    (α : LinearMap.ker ((integralSingularCochains A).sc k).g.hom)
    (φ : LinearMap.ker ((integralRelativeCochains A).sc (k + 1)).g.hom)
    (ψ : integralSingularCochain k X)
    (hψ : integralSingularCochainPullback k (singularSubspaceInclusion A) ψ = α.val)
    (hdψ : (integralRelativeCochainInclusion A).f (k + 1) φ.val =
      integralSingularCoboundary X k (k + 1) ψ)
    (c : LinearMap.ker ((integralRelativeChains A).sc ((k + 1) + m)).g.hom)
    (a : LinearMap.ker ((integralSingularChains A).sc (k + m)).g.hom)
    (b : (integralSingularChains X).X (k + m + 1))
    (hb : (integralRelativeChainSequence A).g.f ((k + 1) + m)
      (((integralSingularChains X).XIsoOfEq
        (show k + m + 1 = (k + 1) + m by omega)).hom b) = c.val)
    (ha : (integralSingularChainMap (singularSubspaceInclusion A)).f (k + m) a.val =
      (integralSingularChains X).d (k + m + 1) (k + m) b) :
    moduleHomologyClass ((integralSingularChains X).sc m)
        (integralRelativeCapToAbsoluteCycleMap A (k + 1) m φ c) =
      integralSingularHomologyMap m (singularSubspaceInclusion A)
        (moduleHomologyClass ((integralSingularChains A).sc m)
          (integralSingularCapCycleMap k m α.val (connecting_absolute_cocycle_closed k α) a)) := by
  let P := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) m).map
    (integralSingularChainMap (singularSubspaceInclusion A))
  let ac := integralSingularCapCycleMap k m α.val (connecting_absolute_cocycle_closed k α) a
  have hout : integralSingularHomologyMap m (singularSubspaceInclusion A)
      (moduleHomologyClass ((integralSingularChains A).sc m) ac) =
      moduleHomologyClass ((integralSingularChains X).sc m) (moduleCycleMap P ac) :=
    moduleHomologyClass_map P ac
  rw [hout]
  apply (moduleHomologyClass_eq_iff ((integralSingularChains X).sc m) _ _).2
  let q := integralSingularCapProduct k (m + 1) ψ b
  let n : ℤ := (-1) ^ k
  let v := -(n • q)
  let ι := (integralSingularChains X).xPrevIso (i := m + 1) (j := m) rfl
  refine ⟨ι.inv v, ?_⟩
  change (integralSingularChains X).dTo m _ = _
  rw [(integralSingularChains X).dTo_eq (i := m + 1) rfl]
  change (integralSingularChains X).d (m + 1) m (ι.hom (ι.inv v)) = _
  have hι : ι.hom (ι.inv v) = v := by
    change (ι.inv ≫ ι.hom) v = v
    rw [Iso.inv_hom_id]
    rfl
  rw [hι]
  have hc : (integralRelativeCapToAbsoluteCycleMap A (k + 1) m φ c).val =
      integralSingularCapProduct (k + 1) m (integralSingularCoboundary X k (k + 1) ψ)
        (((integralSingularChains X).XIsoOfEq
          (show k + m + 1 = (k + 1) + m by omega)).hom b) := by
    rw [integralRelativeCapToAbsoluteCycleMap_apply, ← hb]
    erw [integralRelativeCapProductToAbsolute_π, hdψ]
  have ha' : (moduleCycleMap P ac).val = integralSingularCapProduct k m ψ
      ((integralSingularChains X).d (k + m + 1) (k + m) b) := by
    have h := LinearMap.congr_fun
      (integralSingularCapProduct_natural k m (singularSubspaceInclusion A) ψ) a.val
    change (integralSingularChainMap (singularSubspaceInclusion A)).f m
      (integralSingularCapProduct k m (integralSingularCochainPullback k
        (singularSubspaceInclusion A) ψ) a.val) =
      integralSingularCapProduct k m ψ
        ((integralSingularChainMap (singularSubspaceInclusion A)).f (k + m) a.val) at h
    erw [hψ, ha] at h
    exact h
  have h := LinearMap.congr_fun (integralSingularCapProduct_boundary k m ψ) b
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h
  have heval := map_zsmul
    (LinearMap.applyₗ (R := ℤ) (M₂ := (integralSingularChains X).X m) b)
    ((-1 : ℤ) ^ k) (((integralSingularChains X).d (m + 1) m).hom.comp
      (integralSingularCapProduct k (m + 1) ψ))
  have hboundary : integralSingularCapProduct k m ψ
      ((integralSingularChains X).d (k + m + 1) (k + m) b) =
      integralSingularCapProduct (k + 1) m (integralSingularCoboundary X k (k + 1) ψ)
        (((integralSingularChains X).XIsoOfEq
          (show k + m + 1 = (k + 1) + m by omega)).hom b) +
        n • (integralSingularChains X).d (m + 1) m q :=
    h.trans (congrArg (fun z => integralSingularCapProduct (k + 1) m
      (integralSingularCoboundary X k (k + 1) ψ)
        (((integralSingularChains X).XIsoOfEq
          (show k + m + 1 = (k + 1) + m by omega)).hom b) + z) heval)
  dsimp only [v]
  rw [map_neg, map_zsmul]
  erw [hc, ha', hboundary]
  abel


theorem integralRelativeCohomologyCapToAbsolute_connecting (A : Set X) (k m : ℕ)
    (α : integralSingularCohomology k A) (c : integralRelativeHomology (k + m + 1) A) :
    integralRelativeCohomologyCapToAbsolute A (k + 1) m
        (integralRelativeCohomologyConnecting k A α)
        ((eqToHom (congrArg (fun n => integralRelativeHomology n A)
          (show k + m + 1 = (k + 1) + m by omega))) c) =
      integralSingularHomologyMap m (singularSubspaceInclusion A)
        (integralSingularCohomologyCapProduct k m α (integralRelativeConnecting (k + m) A c)) := by
  obtain ⟨α, rfl⟩ := moduleHomologyClass_surjective ((integralSingularCochains A).sc k) α
  obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective ((integralRelativeChains A).sc (k + m + 1)) c
  obtain ⟨ψ, φ, hψ, hdψ⟩ := exists_moduleCycle_connecting_lifts
    (integralRelativeCochainSequence_shortExact A) k (k + 1) (by simp) α
  obtain ⟨b, a, hb, ha⟩ := exists_moduleCycle_connecting_lifts
    (integralRelativeChainSequence_shortExact A) (k + m + 1) (k + m) (by simp) c
  have hφα : integralRelativeCohomologyConnecting k A
      (moduleHomologyClass ((integralSingularCochains A).sc k) α) =
      moduleHomologyClass ((integralRelativeCochains A).sc (k + 1)) φ :=
    moduleHomologyClass_connecting (integralRelativeCochainSequence_shortExact A)
      k (k + 1) (by simp) α ψ hψ φ hdψ
  have hca : integralRelativeConnecting (k + m) A
      (moduleHomologyClass ((integralRelativeChains A).sc (k + m + 1)) c) =
      moduleHomologyClass ((integralSingularChains A).sc (k + m)) a :=
    moduleHomologyClass_connecting (integralRelativeChainSequence_shortExact A)
      (k + m + 1) (k + m) (by simp) c b hb a ha
  let h : k + m + 1 = (k + 1) + m := by omega
  let c' : LinearMap.ker ((integralRelativeChains A).sc ((k + 1) + m)).g.hom :=
    ⟨((integralRelativeChains A).XIsoOfEq h).hom c.val, by
      have hmem : ∀ {i j : ℕ} (e : i = j)
          (z : LinearMap.ker ((integralRelativeChains A).sc i).g.hom),
          ((integralRelativeChains A).XIsoOfEq e).hom z.val ∈
            LinearMap.ker ((integralRelativeChains A).sc j).g.hom := by
        intro i j e z
        subst j
        exact z.property
      exact hmem h c⟩
  have hc' : (eqToHom (congrArg (fun n => integralRelativeHomology n A) h))
      (moduleHomologyClass ((integralRelativeChains A).sc (k + m + 1)) c) =
      moduleHomologyClass ((integralRelativeChains A).sc ((k + 1) + m)) c' :=
    moduleHomologyClass_transport (integralRelativeChains A) h c
  have hb' : (integralRelativeChainSequence A).g.f ((k + 1) + m)
      (((integralSingularChains X).XIsoOfEq h).hom b) = c'.val := by
    have hn := congrArg (fun f : (integralSingularChains X).X (k + m + 1) ⟶
      (integralRelativeChains A).X ((k + 1) + m) => f b)
      (HomologicalComplex.XIsoOfEq_hom_naturality (integralRelativeChainSequence A).g h)
    exact hn.symm.trans (congrArg ((integralRelativeChains A).XIsoOfEq h).hom hb)
  rw [hφα, hca, hc']
  erw [integralRelativeCohomologyCapToAbsolute_class, integralSingularCohomologyCapProduct_class]
  exact cohomology_cap_connecting_class A k m α φ ψ hψ hdψ c' a b hb' ha


end DifferentialGeometry.Topology

end
