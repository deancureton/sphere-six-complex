module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCochains
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCapProduct

@[expose] public section

noncomputable section

open CategoryTheory

universe u

section

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

local instance RelativeCapToAbsolute.quotientIntegerModule (M : Type*) [AddCommGroup M]
    [Module ℤ M] (S : Submodule ℤ M) : Module ℤ (M ⧸ S) :=
  Submodule.Quotient.module S

theorem RelativeCapToAbsolute.relative_cochain_pullback_zero (A : Set X) (k : ℕ)
    (φ : (integralRelativeCochains A).X k) :
    integralSingularCochainPullback k (singularSubspaceInclusion A)
      ((integralRelativeCochainInclusion A).f k φ) = 0 := by
  exact congrArg (fun f : integralRelativeCochains A ⟶ integralSingularCochains A => f.f k φ)
    (integralRelativeCochainInclusion_comp A)

theorem RelativeCapToAbsolute.relative_cochain_cap_ker (A : Set X) (k m : ℕ)
    (φ : (integralRelativeCochains A).X k) :
    LinearMap.ker ((integralRelativeChainSequence A).g.f (k + m)).hom ≤
      LinearMap.ker (integralSingularCapProduct k m
        ((integralRelativeCochainInclusion A).f k φ)) := by
  intro c hc
  change (integralRelativeChainSequence A).g.f (k + m) c = 0 at hc
  obtain ⟨b, rfl⟩ := (chainCokernelπ_eq_zero_iff
    (integralSingularChainMap (singularSubspaceInclusion A)) (k + m) c).1 hc
  have h := LinearMap.congr_fun
    (integralSingularCapProduct_natural k m (singularSubspaceInclusion A)
      ((integralRelativeCochainInclusion A).f k φ)) b
  change (integralSingularChainMap (singularSubspaceInclusion A)).f m
    (integralSingularCapProduct k m
      (integralSingularCochainPullback k (singularSubspaceInclusion A)
        ((integralRelativeCochainInclusion A).f k φ)) b) = _ at h
  rw [RelativeCapToAbsolute.relative_cochain_pullback_zero, map_zero, LinearMap.zero_apply, map_zero] at h
  exact h.symm

def RelativeCapToAbsolute.relativeCochainCapLinear (A : Set X) (k m : ℕ)
    (φ : (integralRelativeCochains A).X k) :
    (integralRelativeChains A).X (k + m) →ₗ[ℤ] (integralSingularChains X).X m :=
  (LinearMap.ker ((integralRelativeChainSequence A).g.f (k + m)).hom).liftQ
      (integralSingularCapProduct k m ((integralRelativeCochainInclusion A).f k φ))
      (RelativeCapToAbsolute.relative_cochain_cap_ker A k m φ) |>.comp
    ((((integralRelativeChainSequence A).g.f (k + m)).hom.quotKerEquivOfSurjective
      (chainCokernelπ_surjective _ (k + m))).symm.toLinearMap)

theorem RelativeCapToAbsolute.relativeCochainCapLinear_π (A : Set X) (k m : ℕ)
    (φ : (integralRelativeCochains A).X k) (c : (integralSingularChains X).X (k + m)) :
    RelativeCapToAbsolute.relativeCochainCapLinear A k m φ ((integralRelativeChainSequence A).g.f (k + m) c) =
      integralSingularCapProduct k m ((integralRelativeCochainInclusion A).f k φ) c := by
  let π := ((integralRelativeChainSequence A).g.f (k + m)).hom
  let ψ := integralSingularCapProduct k m ((integralRelativeCochainInclusion A).f k φ)
  exact congrArg (π.ker.liftQ ψ (RelativeCapToAbsolute.relative_cochain_cap_ker A k m φ))
    (LinearMap.quotKerEquivOfSurjective_symm_apply π
      (chainCokernelπ_surjective _ (k + m)) c)

end DifferentialGeometry.Topology

end

section

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def integralRelativeCapProductToAbsolute (A : Set X) (k m : ℕ) :
    (integralRelativeCochains A).X k →ₗ[ℤ]
      (integralRelativeChains A).X (k + m) →ₗ[ℤ] (integralSingularChains X).X m := by
  let L : (integralRelativeCochains A).X k →+
      ((integralRelativeChains A).X (k + m) →ₗ[ℤ] (integralSingularChains X).X m) :=
    { toFun := RelativeCapToAbsolute.relativeCochainCapLinear A k m
      map_zero' := by
        apply LinearMap.ext
        intro c
        obtain ⟨b, rfl⟩ := chainCokernelπ_surjective
          (integralSingularChainMap (singularSubspaceInclusion A)) (k + m) c
        change RelativeCapToAbsolute.relativeCochainCapLinear A k m 0
          ((integralRelativeChainSequence A).g.f (k + m) b) = 0
        erw [RelativeCapToAbsolute.relativeCochainCapLinear_π, map_zero, map_zero, LinearMap.zero_apply]
      map_add' := fun φ ψ => by
        apply LinearMap.ext
        intro c
        obtain ⟨b, rfl⟩ := chainCokernelπ_surjective
          (integralSingularChainMap (singularSubspaceInclusion A)) (k + m) c
        change RelativeCapToAbsolute.relativeCochainCapLinear A k m (φ + ψ)
          ((integralRelativeChainSequence A).g.f (k + m) b) =
            RelativeCapToAbsolute.relativeCochainCapLinear A k m φ
              ((integralRelativeChainSequence A).g.f (k + m) b) +
            RelativeCapToAbsolute.relativeCochainCapLinear A k m ψ
              ((integralRelativeChainSequence A).g.f (k + m) b)
        erw [RelativeCapToAbsolute.relativeCochainCapLinear_π, RelativeCapToAbsolute.relativeCochainCapLinear_π,
          RelativeCapToAbsolute.relativeCochainCapLinear_π, map_add, map_add, LinearMap.add_apply] }
  refine { toFun := L, map_add' := L.map_add, map_smul' := ?_ }
  intro n φ
  exact (congrArg L (int_smul_eq_zsmul
    (inferInstance : Module ℤ ((integralRelativeCochains A).X k)) n φ)).trans
      (map_zsmul L n φ)

theorem integralRelativeCapProductToAbsolute_π (A : Set X) (k m : ℕ)
    (φ : (integralRelativeCochains A).X k) (c : (integralSingularChains X).X (k + m)) :
    integralRelativeCapProductToAbsolute A k m φ ((integralRelativeChainSequence A).g.f (k + m) c) =
      integralSingularCapProduct k m ((integralRelativeCochainInclusion A).f k φ) c :=
  RelativeCapToAbsolute.relativeCochainCapLinear_π A k m φ c

theorem integralRelativeCapProductToAbsolute_project (A : Set X) (k m : ℕ)
    (φ : (integralRelativeCochains A).X k) (c : (integralRelativeChains A).X (k + m)) :
    (integralRelativeChainSequence A).g.f m (integralRelativeCapProductToAbsolute A k m φ c) =
      integralRelativeCapProduct A k m ((integralRelativeCochainInclusion A).f k φ) c := by
  obtain ⟨b, rfl⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion A)) (k + m) c
  change (integralRelativeChainSequence A).g.f m (integralRelativeCapProductToAbsolute A k m φ
    ((integralRelativeChainSequence A).g.f (k + m) b)) = _
  erw [integralRelativeCapProductToAbsolute_π, integralRelativeCapProduct_π]

theorem integralRelativeCapProductToAbsolute_natural (k m : ℕ) (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (φ : (integralRelativeCochains B).X k) :
    ((integralSingularChainMap f).f m).hom.comp
        (integralRelativeCapProductToAbsolute A k m ((integralRelativeCochainMap f hf).f k φ)) =
      (integralRelativeCapProductToAbsolute B k m φ).comp
        ((integralRelativeChainMap f hf).f (k + m)).hom := by
  apply LinearMap.ext
  intro c
  obtain ⟨b, rfl⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion A)) (k + m) c
  have hπ : (integralRelativeChainMap f hf).f (k + m)
      ((integralRelativeChainSequence A).g.f (k + m) b) =
        (integralRelativeChainSequence B).g.f (k + m) ((integralSingularChainMap f).f (k + m) b) :=
    (congrArg (fun h : integralSingularChains X ⟶ integralRelativeChains B => h.f (k + m) b)
      (integralRelativeSequenceMap f hf).comm₂₃).symm
  have hφ : (integralRelativeCochainInclusion A).f k ((integralRelativeCochainMap f hf).f k φ) =
      integralSingularCochainPullback k f ((integralRelativeCochainInclusion B).f k φ) :=
    congrArg (fun h : integralRelativeCochains B ⟶ integralSingularCochains X => h.f k φ)
      (integralRelativeCochainMap_inclusion f hf)
  change (integralSingularChainMap f).f m (integralRelativeCapProductToAbsolute A k m _
    ((integralRelativeChainSequence A).g.f (k + m) b)) =
      integralRelativeCapProductToAbsolute B k m φ ((integralRelativeChainMap f hf).f (k + m)
        ((integralRelativeChainSequence A).g.f (k + m) b))
  rw [integralRelativeCapProductToAbsolute_π, hπ, integralRelativeCapProductToAbsolute_π, hφ]
  exact LinearMap.congr_fun (integralSingularCapProduct_natural k m f
    ((integralRelativeCochainInclusion B).f k φ)) b

end DifferentialGeometry.Topology

end

section

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralRelativeCapProductToAbsolute_boundary (A : Set X) (k m : ℕ)
    (φ : (integralRelativeCochains A).X k) (c : (integralRelativeChains A).X (k + m + 1)) :
    integralRelativeCapProductToAbsolute A k m φ ((integralRelativeChains A).d (k + m + 1) (k + m) c) =
      integralRelativeCapProductToAbsolute A (k + 1) m ((integralRelativeCochains A).d k (k + 1) φ)
        (((integralRelativeChains A).XIsoOfEq
          (show k + m + 1 = (k + 1) + m by omega)).hom c) +
      (-1 : ℤ) ^ k • (integralSingularChains X).d (m + 1) m
        (integralRelativeCapProductToAbsolute A k (m + 1) φ c) := by
  obtain ⟨b, rfl⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion A)) (k + m + 1) c
  have hd : (integralRelativeChains A).d (k + m + 1) (k + m)
      ((integralRelativeChainSequence A).g.f (k + m + 1) b) =
        (integralRelativeChainSequence A).g.f (k + m)
          ((integralSingularChains X).d (k + m + 1) (k + m) b) :=
    congrArg (fun h : (integralSingularChains X).X (k + m + 1) ⟶
      (integralRelativeChains A).X (k + m) => h b)
      ((integralRelativeChainSequence A).g.comm (k + m + 1) (k + m))
  have hcast : ((integralRelativeChains A).XIsoOfEq
      (show k + m + 1 = (k + 1) + m by omega)).hom
        ((integralRelativeChainSequence A).g.f (k + m + 1) b) =
      (integralRelativeChainSequence A).g.f ((k + 1) + m)
        (((integralSingularChains X).XIsoOfEq
          (show k + m + 1 = (k + 1) + m by omega)).hom b) :=
    congrArg (fun h : (integralSingularChains X).X (k + m + 1) ⟶
      (integralRelativeChains A).X ((k + 1) + m) => h b)
      (HomologicalComplex.XIsoOfEq_hom_naturality (integralRelativeChainSequence A).g
        (show k + m + 1 = (k + 1) + m by omega))
  have hφ : (integralRelativeCochainInclusion A).f (k + 1)
      ((integralRelativeCochains A).d k (k + 1) φ) =
        integralSingularCoboundary X k (k + 1) ((integralRelativeCochainInclusion A).f k φ) :=
    (congrArg (fun h : (integralRelativeCochains A).X k ⟶
      (integralSingularCochains X).X (k + 1) => h φ)
      ((integralRelativeCochainInclusion A).comm k (k + 1))).symm
  change integralRelativeCapProductToAbsolute A k m φ ((integralRelativeChains A).d (k + m + 1) (k + m)
    ((integralRelativeChainSequence A).g.f (k + m + 1) b)) = _
  erw [hd, integralRelativeCapProductToAbsolute_π, hcast,
    integralRelativeCapProductToAbsolute_π, integralRelativeCapProductToAbsolute_π, hφ]
  let ψ : integralSingularCochain k X := (integralRelativeCochainInclusion A).f k φ
  have h := LinearMap.congr_fun (integralSingularCapProduct_boundary k m ψ) b
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h
  have heval := map_zsmul
    (LinearMap.applyₗ (R := ℤ) (M₂ := (integralSingularChains X).X m) b)
    ((-1 : ℤ) ^ k) (((integralSingularChains X).d (m + 1) m).hom.comp
      (integralSingularCapProduct k (m + 1) ψ))
  exact h.trans (congrArg (fun z =>
    integralSingularCapProduct (k + 1) m (integralSingularCoboundary X k (k + 1) ψ)
      (((integralSingularChains X).XIsoOfEq
        (show k + m + 1 = (k + 1) + m by omega)).hom b) + z) heval)

theorem integralRelativeCapProductToAbsolute_boundary_eq_zero (A : Set X) (k m : ℕ)
    (φ : (integralRelativeCochains A).X k)
    (hφ : (integralRelativeCochains A).d k (k + 1) φ = 0)
    (c : (integralRelativeChains A).X (k + m + 1))
    (hc : (integralRelativeChains A).d (k + m + 1) (k + m) c = 0) :
    (integralSingularChains X).d (m + 1) m (integralRelativeCapProductToAbsolute A k (m + 1) φ c) = 0 := by
  have h := integralRelativeCapProductToAbsolute_boundary A k m φ c
  rw [hc, hφ, map_zero, map_zero, LinearMap.zero_apply, zero_add] at h
  rcases Nat.even_or_odd k with hk | hk
  · simpa only [hk.neg_one_pow, one_zsmul] using h.symm
  · simpa only [hk.neg_one_pow, neg_one_zsmul, neg_eq_zero] using h.symm

end DifferentialGeometry.Topology

end

end
