module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainMaps
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CarrierRestriction
public import Mathlib.Algebra.Homology.ShortComplex.Exact

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DifferentialGeometry.Topology

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def integralRelativeCochains (A : Set X) : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  kernel (integralSingularCochainMap (singularSubspaceInclusion A))

def integralRelativeCochainInclusion (A : Set X) :
    integralRelativeCochains A ⟶ integralSingularCochains X :=
  kernel.ι (integralSingularCochainMap (singularSubspaceInclusion A))

theorem integralRelativeCochainInclusion_comp (A : Set X) :
    integralRelativeCochainInclusion A ≫
      integralSingularCochainMap (singularSubspaceInclusion A) = 0 :=
  kernel.condition _

theorem integralSingularCochainMap_pair_square (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralSingularCochainMap (singularSubspaceInclusion B) ≫
        integralSingularCochainMap (singularPairRestriction f hf) =
      integralSingularCochainMap f ≫ integralSingularCochainMap (singularSubspaceInclusion A) := by
  rw [← integralSingularCochainMap_comp, ← integralSingularCochainMap_comp]
  rfl

def integralRelativeCochainMap (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeCochains B ⟶ integralRelativeCochains A :=
  kernel.map _ _ (integralSingularCochainMap f)
    (integralSingularCochainMap (singularPairRestriction f hf))
    (integralSingularCochainMap_pair_square f hf)

theorem integralRelativeCochainMap_inclusion (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeCochainMap f hf ≫ integralRelativeCochainInclusion A =
      integralRelativeCochainInclusion B ≫ integralSingularCochainMap f :=
  kernel.lift_ι _ _ _

theorem integralRelativeCochainMap_id (A : Set X) :
    integralRelativeCochainMap (ContinuousMap.id X) (show Set.MapsTo (ContinuousMap.id X) A A
      from fun _ h => h) = 𝟙 _ := by
  apply (cancel_mono (kernel.ι
    (integralSingularCochainMap (singularSubspaceInclusion A)))).mp
  change integralRelativeCochainMap (ContinuousMap.id X) (show Set.MapsTo (ContinuousMap.id X) A A
    from fun _ h => h) ≫
    integralRelativeCochainInclusion A = 𝟙 _ ≫ integralRelativeCochainInclusion A
  rw [integralRelativeCochainMap_inclusion, integralSingularCochainMap_id]
  simp only [Category.comp_id, Category.id_comp]

theorem integralRelativeCochainMap_comp (f : ContinuousMap X Y) (g : ContinuousMap Y Z)
    {A : Set X} {B : Set Y} {C : Set Z} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    integralRelativeCochainMap (g.comp f) (hg.comp hf) =
      integralRelativeCochainMap g hg ≫ integralRelativeCochainMap f hf := by
  apply (cancel_mono (kernel.ι
    (integralSingularCochainMap (singularSubspaceInclusion A)))).mp
  change integralRelativeCochainMap (g.comp f) (hg.comp hf) ≫
    integralRelativeCochainInclusion A =
      (integralRelativeCochainMap g hg ≫ integralRelativeCochainMap f hf) ≫
        integralRelativeCochainInclusion A
  rw [integralRelativeCochainMap_inclusion, Category.assoc,
    integralRelativeCochainMap_inclusion, ← Category.assoc,
    integralRelativeCochainMap_inclusion, Category.assoc, integralSingularCochainMap_comp]

def integralRelativeCohomology (n : ℕ) (A : Set X) : ModuleCat.{u} ℤ :=
  (integralRelativeCochains A).homology n

def integralRelativeCohomologyMap (n : ℕ) (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeCohomology n B →ₗ[ℤ] integralRelativeCohomology n A :=
  (HomologicalComplex.homologyMap (integralRelativeCochainMap f hf) n).hom

theorem integralRelativeCohomologyMap_id (n : ℕ) (A : Set X) :
    integralRelativeCohomologyMap n (ContinuousMap.id X)
      (show Set.MapsTo (ContinuousMap.id X) A A from fun _ h => h) = LinearMap.id := by
  unfold integralRelativeCohomologyMap
  rw [integralRelativeCochainMap_id, HomologicalComplex.homologyMap_id]
  rfl

theorem integralRelativeCohomologyMap_comp (n : ℕ)
    (f : ContinuousMap X Y) (g : ContinuousMap Y Z)
    {A : Set X} {B : Set Y} {C : Set Z} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    integralRelativeCohomologyMap n (g.comp f) (hg.comp hf) =
      (integralRelativeCohomologyMap n f hf).comp (integralRelativeCohomologyMap n g hg) := by
  unfold integralRelativeCohomologyMap
  rw [integralRelativeCochainMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

def integralRelativeToAbsoluteCohomology (n : ℕ) (A : Set X) :
    integralRelativeCohomology n A →ₗ[ℤ] integralSingularCohomology n X :=
  (HomologicalComplex.homologyMap (integralRelativeCochainInclusion A) n).hom

theorem integralRelativeToAbsoluteCohomology_natural (n : ℕ) (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    (integralRelativeToAbsoluteCohomology n A).comp (integralRelativeCohomologyMap n f hf) =
      (integralSingularCohomologyMap n f).comp (integralRelativeToAbsoluteCohomology n B) := by
  have h := congrArg (fun k => HomologicalComplex.homologyMap k n)
    (integralRelativeCochainMap_inclusion f hf)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact congrArg ModuleCat.Hom.hom h

theorem integralRelativeCochainMap_apply (n : ℕ) (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B)
    (φ : (integralRelativeCochains B).X n) (c : (integralSingularChains X).X n) :
    DFunLike.coe (F := integralSingularCochain n X)
      ((integralRelativeCochainInclusion A).f n ((integralRelativeCochainMap f hf).f n φ)) c =
      DFunLike.coe (F := integralSingularCochain n Y) ((integralRelativeCochainInclusion B).f n φ)
        ((integralSingularChainMap f).f n c) := by
  have h := congrArg (fun k => k.f n) (integralRelativeCochainMap_inclusion f hf)
  exact congrArg (fun k => DFunLike.coe (F := integralSingularCochain n X) (k φ) c) h

section

open Set Module

private def integralSingularSubspaceChainRetraction
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X) :
    (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains A).X n := by
  classical
  exact (integralSingularChainBasis n X).constr ℕ (fun σ =>
    if hσ : range (integralSingularSimplexEquiv n X σ) ⊆ A then
      integralSimplexChain n (integralSingularSimplexRestriction n A σ hσ) else 0)

private theorem integralSingularSubspaceChainRetraction_simplex
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X)
    (σ : integralSingularSimplex n X)
    (hσ : range (integralSingularSimplexEquiv n X σ) ⊆ A) :
    integralSingularSubspaceChainRetraction n A (integralSimplexChain n σ) =
      integralSimplexChain n (integralSingularSimplexRestriction n A σ hσ) := by
  classical
  rw [← integralSingularChainBasis_apply, integralSingularSubspaceChainRetraction,
    Basis.constr_basis, dite_eq_left hσ]

private theorem integralSingularSubspaceChainRetraction_inclusion
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X) :
    (integralSingularSubspaceChainRetraction n A).comp
        ((integralSingularChainMap (singularSubspaceInclusion A)).f n).hom =
      LinearMap.id := by
  apply (integralSingularChainBasis n A).ext
  intro σ
  have hσ : range (integralSingularSimplexEquiv n X
      (integralSingularSimplexMap n (singularSubspaceInclusion A) σ)) ⊆ A := by
    rintro _ ⟨t, rfl⟩
    rw [integralSingularSimplexMap_apply]
    exact (integralSingularSimplexEquiv n A σ t).property
  simp only [LinearMap.comp_apply, LinearMap.id_apply, integralSingularChainBasis_apply,
    integralSimplexChain_map]
  rw [integralSingularSubspaceChainRetraction_simplex n A _ hσ]
  apply integralSingularChainInclusion_injective n A
  rw [integralSimplexChain_map, integralSingularSimplexRestriction_inclusion,
    integralSimplexChain_map]

theorem integralSingularCochainPullback_subspace_surjective
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X) :
    Function.Surjective (integralSingularCochainPullback n (singularSubspaceInclusion A)) := by
  intro φ
  refine ⟨φ.comp (integralSingularSubspaceChainRetraction n A), ?_⟩
  apply LinearMap.ext
  intro c
  change φ (integralSingularSubspaceChainRetraction n A
    ((integralSingularChainMap (singularSubspaceInclusion A)).f n c)) = φ c
  exact congrArg φ (LinearMap.congr_fun
    (integralSingularSubspaceChainRetraction_inclusion n A) c)

end

def integralRelativeCochainSequence (A : Set X) :
    ShortComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (integralRelativeCochainInclusion A)
    (integralSingularCochainMap (singularSubspaceInclusion A))
    (integralRelativeCochainInclusion_comp A)

theorem integralRelativeCochainSequence_shortExact (A : Set X) :
    (integralRelativeCochainSequence A).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let S := integralRelativeCochainSequence A
  let F := HomologicalComplex.eval (ModuleCat.{u} ℤ) (.up ℕ) n
  have hker : IsLimit (KernelFork.ofι S.f S.zero) := kernelIsKernel _
  refine
    { exact := (S.map F).exact_of_f_is_kernel (KernelFork.mapIsLimit _ hker F)
      mono_f := ?_
      epi_g := ?_ }
  · change Mono (F.map (kernel.ι
      (integralSingularCochainMap (singularSubspaceInclusion A))))
    infer_instance
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact integralSingularCochainPullback_subspace_surjective n A

theorem integralRelativeCochainInclusion_range (n : ℕ) (A : Set X) :
    LinearMap.range ((integralRelativeCochainInclusion A).f n).hom =
      LinearMap.ker (integralSingularCochainPullback n (singularSubspaceInclusion A)) := by
  have h := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (integralRelativeCochainSequence_shortExact A) n
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h.exact

def integralRelativeCochainSequenceMap (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeCochainSequence B ⟶ integralRelativeCochainSequence A where
  τ₁ := integralRelativeCochainMap f hf
  τ₂ := integralSingularCochainMap f
  τ₃ := integralSingularCochainMap (singularPairRestriction f hf)
  comm₁₂ := integralRelativeCochainMap_inclusion f hf
  comm₂₃ := (integralSingularCochainMap_pair_square f hf).symm

def integralRelativeCohomologyConnecting (n : ℕ) (A : Set X) :
    integralSingularCohomology n A →ₗ[ℤ] integralRelativeCohomology (n + 1) A :=
  ((integralRelativeCochainSequence_shortExact A).δ n (n + 1) (by simp)).hom

theorem integralRelativeCohomologyConnecting_natural (n : ℕ) (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    (integralRelativeCohomologyMap (n + 1) f hf).comp (integralRelativeCohomologyConnecting n B) =
      (integralRelativeCohomologyConnecting n A).comp
        (integralSingularCohomologyMap n (singularPairRestriction f hf)) := by
  exact congrArg ModuleCat.Hom.hom
    (HomologicalComplex.HomologySequence.δ_naturality (integralRelativeCochainSequenceMap f hf)
      (integralRelativeCochainSequence_shortExact B) (integralRelativeCochainSequence_shortExact A)
        n (n + 1) (by simp))

theorem integralRelativeCohomology_exact_absolute (n : ℕ) (A : Set X) :
    Function.Exact (integralRelativeToAbsoluteCohomology n A)
      (integralSingularCohomologyMap n (singularSubspaceInclusion A)) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeCochainSequence_shortExact A).homology_exact₂ n)

theorem integralRelativeCohomology_exact_subspace (n : ℕ) (A : Set X) :
    Function.Exact (integralSingularCohomologyMap n (singularSubspaceInclusion A))
      (integralRelativeCohomologyConnecting n A) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeCochainSequence_shortExact A).homology_exact₃ n (n + 1) (by simp))

theorem integralRelativeCohomology_exact_relative (n : ℕ) (A : Set X) :
    Function.Exact (integralRelativeCohomologyConnecting n A)
      (integralRelativeToAbsoluteCohomology (n + 1) A) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeCochainSequence_shortExact A).homology_exact₁ n (n + 1) (by simp))

end DifferentialGeometry.Topology

end
