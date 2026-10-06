module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CapProduct
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainCokernelElements
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

local instance RelativeCapProduct.quotientIntegerModule (M : Type*) [AddCommGroup M]
    [Module ℤ M] (S : Submodule ℤ M) : Module ℤ (M ⧸ S) :=
  Submodule.Quotient.module S

theorem integralRelativeCapProduct_ker (A : Set X) (k m : ℕ)
    (φ : integralSingularCochain k X) :
    LinearMap.ker ((integralRelativeChainSequence A).g.f (k + m)).hom ≤
      LinearMap.ker (((integralRelativeChainSequence A).g.f m).hom.comp
        (integralSingularCapProduct k m φ)) := by
  intro c hc
  change (integralRelativeChainSequence A).g.f (k + m) c = 0 at hc
  obtain ⟨b, rfl⟩ := (chainCokernelπ_eq_zero_iff
    (integralSingularChainMap (singularSubspaceInclusion A)) (k + m) c).1 hc
  have h := LinearMap.congr_fun
    (integralSingularCapProduct_natural k m (singularSubspaceInclusion A) φ) b
  change (integralSingularChainMap (singularSubspaceInclusion A)).f m
    (integralSingularCapProduct k m
      (integralSingularCochainPullback k (singularSubspaceInclusion A) φ) b) =
        integralSingularCapProduct k m φ
          ((integralSingularChainMap (singularSubspaceInclusion A)).f (k + m) b) at h
  change (integralRelativeChainSequence A).g.f m
    (integralSingularCapProduct k m φ
      ((integralSingularChainMap (singularSubspaceInclusion A)).f (k + m) b)) = 0
  rw [← h]
  exact (chainCokernelπ_eq_zero_iff
    (integralSingularChainMap (singularSubspaceInclusion A)) m _).2 ⟨_, rfl⟩

def integralRelativeCapProductLinear (A : Set X) (k m : ℕ)
    (φ : integralSingularCochain k X) :
    (integralRelativeChains A).X (k + m) →ₗ[ℤ] (integralRelativeChains A).X m :=
  (LinearMap.ker ((integralRelativeChainSequence A).g.f (k + m)).hom).liftQ
      (((integralRelativeChainSequence A).g.f m).hom.comp
        (integralSingularCapProduct k m φ)) (integralRelativeCapProduct_ker A k m φ) |>.comp
    ((((integralRelativeChainSequence A).g.f (k + m)).hom.quotKerEquivOfSurjective
      (chainCokernelπ_surjective _ (k + m))).symm.toLinearMap)

private theorem integralRelativeCapProductLinear_π (A : Set X) (k m : ℕ)
    (φ : integralSingularCochain k X) (c : (integralSingularChains X).X (k + m)) :
    integralRelativeCapProductLinear A k m φ ((integralRelativeChainSequence A).g.f (k + m) c) =
      (integralRelativeChainSequence A).g.f m (integralSingularCapProduct k m φ c) := by
  let π := ((integralRelativeChainSequence A).g.f (k + m)).hom
  let ψ := ((integralRelativeChainSequence A).g.f m).hom.comp
    (integralSingularCapProduct k m φ)
  exact congrArg (π.ker.liftQ ψ (integralRelativeCapProduct_ker A k m φ))
    (LinearMap.quotKerEquivOfSurjective_symm_apply π
      (chainCokernelπ_surjective _ (k + m)) c)

def integralRelativeCapProduct (A : Set X) (k m : ℕ) :
    integralSingularCochain k X →ₗ[ℤ]
      (integralRelativeChains A).X (k + m) →ₗ[ℤ] (integralRelativeChains A).X m :=
  AddMonoidHom.toIntLinearMap
    { toFun := integralRelativeCapProductLinear A k m
      map_zero' := by
        apply LinearMap.ext
        intro c
        obtain ⟨b, rfl⟩ := chainCokernelπ_surjective
          (integralSingularChainMap (singularSubspaceInclusion A)) (k + m) c
        change integralRelativeCapProductLinear A k m 0
          ((integralRelativeChainSequence A).g.f (k + m) b) = 0
        rw [integralRelativeCapProductLinear_π, map_zero, LinearMap.zero_apply]
        exact map_zero ((integralRelativeChainSequence A).g.f m).hom
      map_add' := fun φ ψ => by
        apply LinearMap.ext
        intro c
        obtain ⟨b, rfl⟩ := chainCokernelπ_surjective
          (integralSingularChainMap (singularSubspaceInclusion A)) (k + m) c
        change integralRelativeCapProductLinear A k m (φ + ψ)
          ((integralRelativeChainSequence A).g.f (k + m) b) =
            integralRelativeCapProductLinear A k m φ
              ((integralRelativeChainSequence A).g.f (k + m) b) +
            integralRelativeCapProductLinear A k m ψ
              ((integralRelativeChainSequence A).g.f (k + m) b)
        rw [integralRelativeCapProductLinear_π, integralRelativeCapProductLinear_π,
          integralRelativeCapProductLinear_π, map_add, LinearMap.add_apply]
        exact map_add ((integralRelativeChainSequence A).g.f m).hom _ _ }

theorem integralRelativeCapProduct_π (A : Set X) (k m : ℕ)
    (φ : integralSingularCochain k X) (c : (integralSingularChains X).X (k + m)) :
    integralRelativeCapProduct A k m φ ((integralRelativeChainSequence A).g.f (k + m) c) =
      (integralRelativeChainSequence A).g.f m (integralSingularCapProduct k m φ c) :=
  integralRelativeCapProductLinear_π A k m φ c

end DifferentialGeometry.Topology

end
end

section
noncomputable section

open CategoryTheory

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

private theorem integralRelativeChainMap_projection (n : ℕ) (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (c : (integralSingularChains X).X n) :
    (integralRelativeChainMap f hf).f n ((integralRelativeChainSequence A).g.f n c) =
      (integralRelativeChainSequence B).g.f n ((integralSingularChainMap f).f n c) :=
  (congrArg (fun h : integralSingularChains X ⟶ integralRelativeChains B => h.f n c)
    (integralRelativeSequenceMap f hf).comm₂₃).symm

theorem integralRelativeCapProduct_natural (k m : ℕ) (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (φ : integralSingularCochain k Y) :
    ((integralRelativeChainMap f hf).f m).hom.comp
        (integralRelativeCapProduct A k m (integralSingularCochainPullback k f φ)) =
      (integralRelativeCapProduct B k m φ).comp ((integralRelativeChainMap f hf).f (k + m)).hom := by
  apply LinearMap.ext
  intro c
  obtain ⟨b, rfl⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion A)) (k + m) c
  change (integralRelativeChainMap f hf).f m
    (integralRelativeCapProduct A k m (integralSingularCochainPullback k f φ)
      ((integralRelativeChainSequence A).g.f (k + m) b)) =
    integralRelativeCapProduct B k m φ ((integralRelativeChainMap f hf).f (k + m)
      ((integralRelativeChainSequence A).g.f (k + m) b))
  rw [integralRelativeCapProduct_π, integralRelativeChainMap_projection,
    integralRelativeChainMap_projection, integralRelativeCapProduct_π]
  exact congrArg ((integralRelativeChainSequence B).g.f m)
    (LinearMap.congr_fun (integralSingularCapProduct_natural k m f φ) b)

private theorem integralRelativeProjection_d (A : Set X) (i j : ℕ)
    (c : (integralSingularChains X).X i) :
    (integralRelativeChains A).d i j ((integralRelativeChainSequence A).g.f i c) =
      (integralRelativeChainSequence A).g.f j ((integralSingularChains X).d i j c) :=
  congrArg (fun h : (integralSingularChains X).X i ⟶ (integralRelativeChains A).X j => h c)
    ((integralRelativeChainSequence A).g.comm i j)

private theorem integralRelativeProjection_XIsoOfEq (A : Set X) {i j : ℕ} (h : i = j)
    (c : (integralSingularChains X).X i) :
    ((integralRelativeChains A).XIsoOfEq h).hom ((integralRelativeChainSequence A).g.f i c) =
      (integralRelativeChainSequence A).g.f j (((integralSingularChains X).XIsoOfEq h).hom c) :=
  congrArg (fun g : (integralSingularChains X).X i ⟶ (integralRelativeChains A).X j => g c)
    (HomologicalComplex.XIsoOfEq_hom_naturality (integralRelativeChainSequence A).g h)

theorem integralRelativeCapProduct_boundary (A : Set X) (k m : ℕ)
    (φ : integralSingularCochain k X) (c : (integralRelativeChains A).X (k + m + 1)) :
    integralRelativeCapProduct A k m φ ((integralRelativeChains A).d (k + m + 1) (k + m) c) =
      integralRelativeCapProduct A (k + 1) m (integralSingularCoboundary X k (k + 1) φ)
        (((integralRelativeChains A).XIsoOfEq
          (show k + m + 1 = (k + 1) + m by omega)).hom c) +
      (-1 : ℤ) ^ k • (integralRelativeChains A).d (m + 1) m
        (integralRelativeCapProduct A k (m + 1) φ c) := by
  obtain ⟨b, rfl⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion A)) (k + m + 1) c
  change integralRelativeCapProduct A k m φ ((integralRelativeChains A).d (k + m + 1) (k + m)
      ((integralRelativeChainSequence A).g.f (k + m + 1) b)) = _
  erw [integralRelativeProjection_d, integralRelativeCapProduct_π,
    integralRelativeProjection_XIsoOfEq, integralRelativeCapProduct_π,
    integralRelativeCapProduct_π, integralRelativeProjection_d]
  have h := LinearMap.congr_fun (integralSingularCapProduct_boundary k m φ) b
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h
  have heval := map_zsmul
    (LinearMap.applyₗ (R := ℤ) (M₂ := (integralSingularChains X).X m) b)
    ((-1 : ℤ) ^ k) (((integralSingularChains X).d (m + 1) m).hom.comp
      (integralSingularCapProduct k (m + 1) φ))
  have hpoint := h.trans (congrArg (fun z =>
    integralSingularCapProduct (k + 1) m (integralSingularCoboundary X k (k + 1) φ)
      (((integralSingularChains X).XIsoOfEq
        (show k + m + 1 = (k + 1) + m by omega)).hom b) + z) heval)
  let π : (integralSingularChains X).X m →ₗ[ℤ] (integralRelativeChains A).X m :=
    ((integralRelativeChainSequence A).g.f m).hom
  have hp := congrArg π hpoint
  rw [map_add, map_zsmul] at hp
  exact hp

end DifferentialGeometry.Topology

end
end

section
noncomputable section

open CategoryTheory

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralRelativeCapProduct_augmentation (A : Set X) (m : ℕ) :
    integralRelativeCapProduct A 0 m
        ((ULift.moduleEquiv : integralSingularCoefficients ≃ₗ[ℤ] ℤ).symm.toLinearMap.comp
          integralSingularAugmentation) =
      (((integralRelativeChains A).XIsoOfEq (Nat.zero_add m)).hom.hom) := by
  apply LinearMap.ext
  intro c
  obtain ⟨b, rfl⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion A)) (0 + m) c
  change integralRelativeCapProduct A 0 m _
    ((integralRelativeChainSequence A).g.f (0 + m) b) =
      ((integralRelativeChains A).XIsoOfEq (Nat.zero_add m)).hom
        ((integralRelativeChainSequence A).g.f (0 + m) b)
  rw [integralRelativeCapProduct_π, integralRelativeProjection_XIsoOfEq]
  exact congrArg ((integralRelativeChainSequence A).g.f m)
    (LinearMap.congr_fun (integralSingularCapProduct_augmentation m) b)

theorem integralRelativeCapProduct_boundary_eq_zero (A : Set X) (k m : ℕ)
    (φ : integralSingularCochain k X) (hφ : integralSingularCoboundary X k (k + 1) φ = 0)
    (c : (integralRelativeChains A).X (k + m + 1))
    (hc : (integralRelativeChains A).d (k + m + 1) (k + m) c = 0) :
    (integralRelativeChains A).d (m + 1) m
      (integralRelativeCapProduct A k (m + 1) φ c) = 0 := by
  have h := integralRelativeCapProduct_boundary A k m φ c
  rw [hc, hφ, map_zero, map_zero, LinearMap.zero_apply, zero_add] at h
  rcases Nat.even_or_odd k with hk | hk
  · simpa only [hk.neg_one_pow, one_zsmul] using h.symm
  · simpa only [hk.neg_one_pow, neg_one_zsmul, neg_eq_zero] using h.symm

end DifferentialGeometry.Topology

end
end
