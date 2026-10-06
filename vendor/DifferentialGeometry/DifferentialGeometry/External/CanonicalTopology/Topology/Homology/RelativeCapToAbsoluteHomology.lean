module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCapToAbsolute
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCapHomology
public import Mathlib.LinearAlgebra.Quotient.Bilinear

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

local instance RelativeCapToAbsoluteHomology.capIntegerComm (M : Type*) [AddCommGroup M] [h : Module ℤ M] :
    @SMulCommClass ℤ ℤ M h.toSMul h.toSMul :=
  @smulCommClass_self ℤ M inferInstance h.toMulAction

local instance RelativeCapToAbsoluteHomology.capIntegerLinearModule (M N : Type*)
    [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N] :
    Module ℤ (M →ₗ[ℤ] N) := LinearMap.module

local instance RelativeCapToAbsoluteHomology.integralRelativeCycle_module (A : Set X) (n : ℕ) :
    Module ℤ (LinearMap.ker ((integralRelativeChains A).sc n).g.hom) :=
  (LinearMap.ker ((integralRelativeChains A).sc n).g.hom).module

local instance RelativeCapToAbsoluteHomology.capCocycle_module (A : Set X) (n : ℕ) :
    Module ℤ (LinearMap.ker ((integralRelativeCochains A).sc n).g.hom) :=
  (LinearMap.ker ((integralRelativeCochains A).sc n).g.hom).module

local instance RelativeCapToAbsoluteHomology.capCycle_module (n : ℕ) :
    Module ℤ (LinearMap.ker ((integralSingularChains X).sc n).g.hom) :=
  (LinearMap.ker ((integralSingularChains X).sc n).g.hom).module

theorem RelativeCapToAbsoluteHomology.cap_cocycle_closed (A : Set X) (k : ℕ)
    (φ : LinearMap.ker ((integralRelativeCochains A).sc k).g.hom) :
    (integralRelativeCochains A).d k (k + 1) φ.val = 0 := by
  have h := φ.property
  change (integralRelativeCochains A).d k ((ComplexShape.up ℕ).next k) φ.val = 0 at h
  rwa [CochainComplex.next] at h

theorem RelativeCapToAbsoluteHomology.relative_cap_cycle (A : Set X) (k m : ℕ)
    (φ : LinearMap.ker ((integralRelativeCochains A).sc k).g.hom)
    (c : LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom) :
    integralRelativeCapProductToAbsolute A k m φ.val c.val ∈
      LinearMap.ker ((integralSingularChains X).sc m).g.hom := by
  change (integralSingularChains X).d m ((ComplexShape.down ℕ).next m)
    (integralRelativeCapProductToAbsolute A k m φ.val c.val) = 0
  cases m with
  | zero =>
    rw [ChainComplex.next_nat_zero, (integralSingularChains X).shape 0 0 (by simp)]
    rfl
  | succ m =>
    rw [ChainComplex.next_nat_succ]
    apply integralRelativeCapProductToAbsolute_boundary_eq_zero A k m φ.val (RelativeCapToAbsoluteHomology.cap_cocycle_closed A k φ)
    have hc := c.property
    change (integralRelativeChains A).d (k + m + 1)
      ((ComplexShape.down ℕ).next (k + m + 1)) c.val = 0 at hc
    rwa [ChainComplex.next_nat_succ] at hc

def integralRelativeCapToAbsoluteCycleMap (A : Set X) (k m : ℕ) :
    LinearMap.ker ((integralRelativeCochains A).sc k).g.hom →ₗ[ℤ]
      LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom →ₗ[ℤ]
        LinearMap.ker ((integralSingularChains X).sc m).g.hom := by
  let badd : ((integralRelativeCochains A).sc k).X₂ →+
      (((integralRelativeChains A).sc (k + m)).X₂ →ₗ[ℤ]
        ((integralSingularChains X).sc m).X₂) :=
    { toFun := fun φ => integralRelativeCapProductToAbsolute A k m φ
      map_zero' := (integralRelativeCapProductToAbsolute A k m).toAddMonoidHom.map_zero
      map_add' := (integralRelativeCapProductToAbsolute A k m).toAddMonoidHom.map_add }
  let β : ((integralRelativeCochains A).sc k).X₂ →ₗ[ℤ]
      ((integralRelativeChains A).sc (k + m)).X₂ →ₗ[ℤ]
        ((integralSingularChains X).sc m).X₂ :=
    { toFun := badd
      map_add' := badd.map_add
      map_smul' := fun z φ => by
        simpa only [Int.cast_id, RingHom.id_apply] using! map_intCast_smul badd ℤ ℤ z φ }
  exact (β.compl₁₂
    (LinearMap.ker ((integralRelativeCochains A).sc k).g.hom).subtype
    (LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom).subtype).codRestrict₂
      (LinearMap.ker ((integralSingularChains X).sc m).g.hom).subtype
      Subtype.val_injective (fun φ c => ⟨⟨_, RelativeCapToAbsoluteHomology.relative_cap_cycle A k m φ c⟩, rfl⟩)

theorem integralRelativeCapToAbsoluteCycleMap_apply (A : Set X) (k m : ℕ)
    (φ : LinearMap.ker ((integralRelativeCochains A).sc k).g.hom)
    (c : LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom) :
    (integralRelativeCapToAbsoluteCycleMap A k m φ c).val = integralRelativeCapProductToAbsolute A k m φ.val c.val := by
  unfold integralRelativeCapToAbsoluteCycleMap
  exact LinearMap.codRestrict₂_apply (R := ℤ) _
    (LinearMap.ker ((integralSingularChains X).sc m).g.hom).subtype _ _ φ c

def RelativeCapToAbsoluteHomology.relativeCapCycleClasses (A : Set X) (k m : ℕ) :
    LinearMap.ker ((integralRelativeCochains A).sc k).g.hom →ₗ[ℤ]
      LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom →ₗ[ℤ]
        integralSingularHomology m X :=
  (integralRelativeCapToAbsoluteCycleMap A k m).compr₂ₛₗ (moduleHomologyClass ((integralSingularChains X).sc m))

theorem RelativeCapToAbsoluteHomology.chain_homology_class_eq_zero_iff
    (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ)
    (c : LinearMap.ker (K.sc n).g.hom) :
    moduleHomologyClass (K.sc n) c = 0 ↔ ∃ b : K.X (n + 1), K.d (n + 1) n b = c.val := by
  have h := moduleHomologyClass_eq_zero_iff (K.sc n) c
  change (_ ↔ ∃ b : K.X ((ComplexShape.down ℕ).prev n),
    K.d ((ComplexShape.down ℕ).prev n) n b = c.val) at h
  exact h.trans (congrArg (fun i => ∃ b : K.X i, K.d i n b = c.val)
    (ChainComplex.prev ℕ n)).to_iff

theorem RelativeCapToAbsoluteHomology.relative_cap_boundary_is_boundary (A : Set X) (k m : ℕ)
    (φ : (integralRelativeCochains A).X k) (hφ : (integralRelativeCochains A).d k (k + 1) φ = 0)
    (c : (integralRelativeChains A).X (k + m + 1)) :
    ∃ b : (integralSingularChains X).X (m + 1),
      (integralSingularChains X).d (m + 1) m b =
        integralRelativeCapProductToAbsolute A k m φ
          ((integralRelativeChains A).d (k + m + 1) (k + m) c) := by
  refine ⟨(-1 : ℤ) ^ k • integralRelativeCapProductToAbsolute A k (m + 1) φ c, ?_⟩
  rw [map_zsmul, integralRelativeCapProductToAbsolute_boundary, hφ, map_zero,
    LinearMap.zero_apply, zero_add]

theorem RelativeCapToAbsoluteHomology.relative_cap_coboundary_is_boundary (A : Set X) (k m : ℕ)
    (φ : (integralRelativeCochains A).X k) (c : (integralRelativeChains A).X (k + m + 1))
    (hc : (integralRelativeChains A).d (k + m + 1) (k + m) c = 0) :
    ∃ b : (integralSingularChains X).X (m + 1),
      (integralSingularChains X).d (m + 1) m b =
        integralRelativeCapProductToAbsolute A (k + 1) m ((integralRelativeCochains A).d k (k + 1) φ)
          (((integralRelativeChains A).XIsoOfEq
            (show k + m + 1 = (k + 1) + m by omega)).hom c) := by
  have h := integralRelativeCapProductToAbsolute_boundary A k m φ c
  rw [hc, map_zero] at h
  refine ⟨-((-1 : ℤ) ^ k • integralRelativeCapProductToAbsolute A k (m + 1) φ c), ?_⟩
  rw [map_neg, map_zsmul]
  exact (eq_neg_iff_add_eq_zero.mpr h.symm).symm

theorem RelativeCapToAbsoluteHomology.relativeCapCycleClasses_boundary_right (A : Set X) (k m : ℕ)
    (b : ((integralRelativeChains A).sc (k + m)).X₁) :
    (RelativeCapToAbsoluteHomology.relativeCapCycleClasses A k m).flip
      (((integralRelativeChains A).sc (k + m)).moduleCatToCycles b) = 0 := by
  apply LinearMap.ext
  intro φ
  change moduleHomologyClass ((integralSingularChains X).sc m)
    (integralRelativeCapToAbsoluteCycleMap A k m φ (((integralRelativeChains A).sc (k + m)).moduleCatToCycles b)) = 0
  apply (RelativeCapToAbsoluteHomology.chain_homology_class_eq_zero_iff (integralSingularChains X) m _).2
  rw [integralRelativeCapToAbsoluteCycleMap_apply]
  let b' := ((integralRelativeChains A).xPrevIso
    (i := k + m + 1) (j := k + m) rfl).hom b
  have hb : (integralRelativeChains A).d (k + m + 1) (k + m) b' =
      (((integralRelativeChains A).sc (k + m)).moduleCatToCycles b).val := by
    change _ = (integralRelativeChains A).dTo (k + m) b
    rw [(integralRelativeChains A).dTo_eq (i := k + m + 1) rfl]
    rfl
  obtain ⟨a, ha⟩ := RelativeCapToAbsoluteHomology.relative_cap_boundary_is_boundary A k m φ.val
    (RelativeCapToAbsoluteHomology.cap_cocycle_closed A k φ) b'
  exact ⟨a, ha.trans (congrArg (integralRelativeCapProductToAbsolute A k m φ.val) hb)⟩

theorem RelativeCapToAbsoluteHomology.relativeCapCycleClasses_boundary_left (A : Set X) (k m : ℕ)
    (ψ : ((integralRelativeCochains A).sc k).X₁) :
    RelativeCapToAbsoluteHomology.relativeCapCycleClasses A k m
      (((integralRelativeCochains A).sc k).moduleCatToCycles ψ) = 0 := by
  cases k with
  | zero =>
    have hzero : ((integralRelativeCochains A).sc 0).moduleCatToCycles ψ = 0 := by
      apply Subtype.ext
      change (integralRelativeCochains A).dTo 0 ψ = 0
      rw [(integralRelativeCochains A).dTo_eq_zero (by
        rw [CochainComplex.prev_nat_zero]
        simp)]
      rfl
    rw [hzero, map_zero]
  | succ k =>
    apply LinearMap.ext
    intro c
    change moduleHomologyClass ((integralSingularChains X).sc m)
      (integralRelativeCapToAbsoluteCycleMap A (k + 1) m
        (((integralRelativeCochains A).sc (k + 1)).moduleCatToCycles ψ) c) = 0
    apply (RelativeCapToAbsoluteHomology.chain_homology_class_eq_zero_iff (integralSingularChains X) m _).2
    rw [integralRelativeCapToAbsoluteCycleMap_apply]
    let ψ' := ((integralRelativeCochains A).xPrevIso (i := k) (j := k + 1) rfl).hom ψ
    have hψ : (integralRelativeCochains A).d k (k + 1) ψ' =
        (((integralRelativeCochains A).sc (k + 1)).moduleCatToCycles ψ).val := by
      change (integralRelativeCochains A).d k (k + 1) ψ' =
        (integralRelativeCochains A).dTo (k + 1) ψ
      rw [(integralRelativeCochains A).dTo_eq (i := k) rfl]
      rfl
    let h : k + m + 1 = (k + 1) + m := by omega
    let ι := (integralRelativeChains A).XIsoOfEq h
    let c' := ι.inv c.val
    have hn : (ComplexShape.down ℕ).next ((k + 1) + m) = k + m := by
      rw [← h, ChainComplex.next_nat_succ]
    have hc := c.property
    change (integralRelativeChains A).d ((k + 1) + m)
      ((ComplexShape.down ℕ).next ((k + 1) + m)) c.val = 0 at hc
    rw [hn] at hc
    have hc' : (integralRelativeChains A).d (k + m + 1) (k + m) c' = 0 := by
      have heq := congrArg (fun f : (integralRelativeChains A).X ((k + 1) + m) ⟶
        (integralRelativeChains A).X (k + m) => f c.val)
        ((integralRelativeChains A).XIsoOfEq_inv_comp_d h (k + m))
      exact heq.trans hc
    have hback : ι.hom c' = c.val := by
      change (ι.inv ≫ ι.hom) c.val = c.val
      rw [Iso.inv_hom_id]
      rfl
    obtain ⟨b, hb⟩ := RelativeCapToAbsoluteHomology.relative_cap_coboundary_is_boundary A k m ψ' c' hc'
    refine ⟨b, hb.trans ?_⟩
    change integralRelativeCapProductToAbsolute A (k + 1) m
      ((integralRelativeCochains A).d k (k + 1) ψ') (ι.hom c') = _
    rw [hback, hψ]

local instance RelativeCapToAbsoluteHomology.relativeCapQuotientModule (M : Type*) [AddCommGroup M]
    [Module ℤ M] (S : Submodule ℤ M) : Module ℤ (M ⧸ S) :=
  Submodule.Quotient.module S

def RelativeCapToAbsoluteHomology.relativeCapQuotientPairing (A : Set X) (k m : ℕ) :
    (LinearMap.ker ((integralRelativeCochains A).sc k).g.hom ⧸
      LinearMap.range ((integralRelativeCochains A).sc k).moduleCatToCycles) →ₗ[ℤ]
        (LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom ⧸
          LinearMap.range ((integralRelativeChains A).sc (k + m)).moduleCatToCycles) →ₗ[ℤ]
            integralSingularHomology m X := by
  let S := (integralRelativeCochains A).sc k
  let T := (integralRelativeChains A).sc (k + m)
  let β := RelativeCapToAbsoluteHomology.relativeCapCycleClasses A k m
  have hS : LinearMap.range S.moduleCatToCycles ≤ β.ker := by
    rintro φ ⟨ψ, rfl⟩
    exact RelativeCapToAbsoluteHomology.relativeCapCycleClasses_boundary_left A k m ψ
  have hT : LinearMap.range T.moduleCatToCycles ≤ β.flip.ker := by
    rintro c ⟨b, rfl⟩
    exact RelativeCapToAbsoluteHomology.relativeCapCycleClasses_boundary_right A k m b
  exact β.liftQ₂ (LinearMap.range S.moduleCatToCycles)
    (LinearMap.range T.moduleCatToCycles) hS hT

def integralRelativeCohomologyCapToAbsolute (A : Set X) (k m : ℕ) :
    integralRelativeCohomology k A →ₗ[ℤ]
      integralRelativeHomology (k + m) A →ₗ[ℤ] integralSingularHomology m X :=
  ((RelativeCapToAbsoluteHomology.relativeCapQuotientPairing A k m).compl₂
    ((integralRelativeChains A).sc (k + m)).moduleCatHomologyIso.hom.hom).comp
      ((integralRelativeCochains A).sc k).moduleCatHomologyIso.hom.hom

theorem integralRelativeCohomologyCapToAbsolute_class (A : Set X) (k m : ℕ)
    (φ : LinearMap.ker ((integralRelativeCochains A).sc k).g.hom)
    (c : LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom) :
    integralRelativeCohomologyCapToAbsolute A k m
        (moduleHomologyClass ((integralRelativeCochains A).sc k) φ)
        (moduleHomologyClass ((integralRelativeChains A).sc (k + m)) c) =
      moduleHomologyClass ((integralSingularChains X).sc m) (integralRelativeCapToAbsoluteCycleMap A k m φ c) :=
  congrArg₂ (fun a b => RelativeCapToAbsoluteHomology.relativeCapQuotientPairing A k m a b)
    (moduleHomologyClass_quotient ((integralRelativeCochains A).sc k) φ)
    (moduleHomologyClass_quotient ((integralRelativeChains A).sc (k + m)) c)

variable {Y : Type u} [TopologicalSpace Y]

theorem integralRelativeCohomologyCapToAbsolute_natural (k m : ℕ)
    (f : ContinuousMap X Y) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B)
    (φ : integralRelativeCohomology k B) (c : integralRelativeHomology (k + m) A) :
    integralSingularHomologyMap m f
        (integralRelativeCohomologyCapToAbsolute A k m (integralRelativeCohomologyMap k f hf φ) c) =
      integralRelativeCohomologyCapToAbsolute B k m φ
        (integralRelativeHomologyMap (k + m) f hf c) := by
  obtain ⟨φ, rfl⟩ := moduleHomologyClass_surjective ((integralRelativeCochains B).sc k) φ
  obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective ((integralRelativeChains A).sc (k + m)) c
  let P := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) k).map
    (integralRelativeCochainMap f hf)
  let Q := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ)
    (k + m)).map (integralRelativeChainMap f hf)
  let R := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) m).map
    (integralSingularChainMap f)
  have hφ : integralRelativeCohomologyMap k f hf
      (moduleHomologyClass ((integralRelativeCochains B).sc k) φ) =
      moduleHomologyClass ((integralRelativeCochains A).sc k) (moduleCycleMap P φ) :=
    moduleHomologyClass_map P φ
  have hc : integralRelativeHomologyMap (k + m) f hf
      (moduleHomologyClass ((integralRelativeChains A).sc (k + m)) c) =
      moduleHomologyClass ((integralRelativeChains B).sc (k + m)) (moduleCycleMap Q c) :=
    moduleHomologyClass_map Q c
  rw [hφ, hc]
  erw [integralRelativeCohomologyCapToAbsolute_class, integralRelativeCohomologyCapToAbsolute_class]
  have hout := moduleHomologyClass_map R (integralRelativeCapToAbsoluteCycleMap A k m (moduleCycleMap P φ) c)
  change integralSingularHomologyMap m f _ = _ at hout
  erw [hout]
  congr 1
  apply Subtype.ext
  change (integralSingularChainMap f).f m (integralRelativeCapToAbsoluteCycleMap A k m (moduleCycleMap P φ) c).val = _
  rw [integralRelativeCapToAbsoluteCycleMap_apply, integralRelativeCapToAbsoluteCycleMap_apply]
  change (integralSingularChainMap f).f m
    (integralRelativeCapProductToAbsolute A k m ((integralRelativeCochainMap f hf).f k φ.val) c.val) =
      integralRelativeCapProductToAbsolute B k m φ.val ((integralRelativeChainMap f hf).f (k + m) c.val)
  exact congrArg (fun L : (integralRelativeChains A).X (k + m) →ₗ[ℤ]
    (integralSingularChains Y).X m => L c.val) (integralRelativeCapProductToAbsolute_natural k m f hf φ.val)

theorem integralRelativeCohomologyCapToAbsolute_bijective_map
    (k m : ℕ) (f : ContinuousMap X Y) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B)
    (habs : Function.Bijective (integralSingularHomologyMap m f))
    (hcoh : Function.Bijective (integralRelativeCohomologyMap k f hf))
    (c : integralRelativeHomology (k + m) A)
    (hc : Function.Bijective (fun α : integralRelativeCohomology k A =>
      integralRelativeCohomologyCapToAbsolute A k m α c)) :
    Function.Bijective (fun β : integralRelativeCohomology k B =>
      integralRelativeCohomologyCapToAbsolute B k m β
        (integralRelativeHomologyMap (k + m) f hf c)) := by
  have heq : (fun β : integralRelativeCohomology k B =>
      integralRelativeCohomologyCapToAbsolute B k m β
        (integralRelativeHomologyMap (k + m) f hf c)) =
      (integralSingularHomologyMap m f) ∘
        (fun α : integralRelativeCohomology k A =>
          integralRelativeCohomologyCapToAbsolute A k m α c) ∘
            (integralRelativeCohomologyMap k f hf) := by
    funext β
    exact (integralRelativeCohomologyCapToAbsolute_natural k m f hf β c).symm
  rw [heq]
  exact habs.comp (hc.comp hcoh)


local instance RelativeCapToAbsoluteHomology.absoluteCocycle_module (n : ℕ) :
    Module ℤ (LinearMap.ker ((integralSingularCochains X).sc n).g.hom) :=
  (LinearMap.ker ((integralSingularCochains X).sc n).g.hom).module

theorem integralRelativeCohomologyCapToAbsolute_project (A : Set X) (k m : ℕ)
    (φ : integralRelativeCohomology k A) (c : integralRelativeHomology (k + m) A) :
    integralAbsoluteToRelative m A (integralRelativeCohomologyCapToAbsolute A k m φ c) =
      integralRelativeCohomologyCapProduct A k m (integralRelativeToAbsoluteCohomology k A φ) c := by
  obtain ⟨φ, rfl⟩ := moduleHomologyClass_surjective ((integralRelativeCochains A).sc k) φ
  obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective ((integralRelativeChains A).sc (k + m)) c
  let P := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) k).map
    (integralRelativeCochainInclusion A)
  let R := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) m).map
    (integralRelativeChainSequence A).g
  have hφ : integralRelativeToAbsoluteCohomology k A
      (moduleHomologyClass ((integralRelativeCochains A).sc k) φ) =
      moduleHomologyClass ((integralSingularCochains X).sc k) (moduleCycleMap P φ) :=
    moduleHomologyClass_map P φ
  rw [hφ]
  erw [integralRelativeCohomologyCapToAbsolute_class, integralRelativeCohomologyCapProduct_class]
  have hout := moduleHomologyClass_map R (integralRelativeCapToAbsoluteCycleMap A k m φ c)
  change integralAbsoluteToRelative m A _ = _ at hout
  erw [hout]
  congr 1
  apply Subtype.ext
  change (integralRelativeChainSequence A).g.f m (integralRelativeCapToAbsoluteCycleMap A k m φ c).val = _
  rw [integralRelativeCapToAbsoluteCycleMap_apply, integralRelativeCapCycleMap_apply]
  exact integralRelativeCapProductToAbsolute_project A k m φ.val c.val

theorem integralRelativeCohomologyCapToAbsolute_absoluteToRelative (A : Set X) (k m : ℕ)
    (φ : integralRelativeCohomology k A) (c : integralSingularHomology (k + m) X) :
    integralRelativeCohomologyCapToAbsolute A k m φ (integralAbsoluteToRelative (k + m) A c) =
      integralSingularCohomologyCapProduct k m (integralRelativeToAbsoluteCohomology k A φ) c := by
  obtain ⟨φ, rfl⟩ := moduleHomologyClass_surjective ((integralRelativeCochains A).sc k) φ
  obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective ((integralSingularChains X).sc (k + m)) c
  let P := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) k).map
    (integralRelativeCochainInclusion A)
  let Q := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ)
    (k + m)).map (integralRelativeChainSequence A).g
  have hφ : integralRelativeToAbsoluteCohomology k A
      (moduleHomologyClass ((integralRelativeCochains A).sc k) φ) =
      moduleHomologyClass ((integralSingularCochains X).sc k) (moduleCycleMap P φ) :=
    moduleHomologyClass_map P φ
  have hc : integralAbsoluteToRelative (k + m) A
      (moduleHomologyClass ((integralSingularChains X).sc (k + m)) c) =
      moduleHomologyClass ((integralRelativeChains A).sc (k + m)) (moduleCycleMap Q c) :=
    moduleHomologyClass_map Q c
  rw [hφ, hc]
  erw [integralRelativeCohomologyCapToAbsolute_class, integralSingularCohomologyCapProduct_class]
  congr 1
  apply Subtype.ext
  erw [integralRelativeCapToAbsoluteCycleMap_apply]
  exact integralRelativeCapProductToAbsolute_π A k m φ.val c.val

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type u} [TopologicalSpace Y]

theorem integralRelativeCohomologyCapToAbsolute_bijective_map_iff
    (k m : ℕ) (f : ContinuousMap X Y) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B)
    (habs : Function.Bijective (integralSingularHomologyMap m f))
    (hcoh : Function.Bijective (integralRelativeCohomologyMap k f hf))
    (c : integralRelativeHomology (k + m) A) :
    Function.Bijective (fun β : integralRelativeCohomology k B =>
      integralRelativeCohomologyCapToAbsolute B k m β
        (integralRelativeHomologyMap (k + m) f hf c)) ↔
      Function.Bijective (fun α : integralRelativeCohomology k A =>
        integralRelativeCohomologyCapToAbsolute A k m α c) := by
  have heq : (fun β : integralRelativeCohomology k B =>
      integralRelativeCohomologyCapToAbsolute B k m β
        (integralRelativeHomologyMap (k + m) f hf c)) =
      ((integralSingularHomologyMap m f) ∘
        (fun α : integralRelativeCohomology k A =>
          integralRelativeCohomologyCapToAbsolute A k m α c)) ∘
            (integralRelativeCohomologyMap k f hf) := by
    funext β
    exact (integralRelativeCohomologyCapToAbsolute_natural k m f hf β c).symm
  rw [heq]
  exact (Function.Bijective.of_comp_iff _ hcoh).trans
    (Function.Bijective.of_comp_iff' habs _)

end DifferentialGeometry.Topology

end
