module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CapProduct
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

local instance CapHomology.integralSingularCycle_module (n : ℕ) :
    Module ℤ (LinearMap.ker ((integralSingularChains X).sc n).g.hom) :=
  (LinearMap.ker ((integralSingularChains X).sc n).g.hom).module

local instance CapHomology.integralSingularCocycle_module (n : ℕ) :
    Module ℤ (LinearMap.ker ((integralSingularCochains X).sc n).g.hom) :=
  (LinearMap.ker ((integralSingularCochains X).sc n).g.hom).module

theorem integralSingularCapProduct_boundary_apply (k m : ℕ)
    (φ : integralSingularCochain k X) (c : (integralSingularChains X).X (k + m + 1)) :
    integralSingularCapProduct k m φ ((integralSingularChains X).d (k + m + 1) (k + m) c) =
      integralSingularCapProduct (k + 1) m (integralSingularCoboundary X k (k + 1) φ)
        (((integralSingularChains X).XIsoOfEq
          (show k + m + 1 = (k + 1) + m by omega)).hom c) +
      (-1 : ℤ) ^ k • (integralSingularChains X).d (m + 1) m
        (integralSingularCapProduct k (m + 1) φ c) := by
  have h := congrArg (fun f : (integralSingularChains X).X (k + m + 1) →ₗ[ℤ]
    (integralSingularChains X).X m => f c) (integralSingularCapProduct_boundary k m φ)
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h
  have heval := map_zsmul
    (LinearMap.applyₗ (R := ℤ) (M₂ := (integralSingularChains X).X m) c)
    ((-1 : ℤ) ^ k) (((integralSingularChains X).d (m + 1) m).hom.comp
      (integralSingularCapProduct k (m + 1) φ))
  exact h.trans (congrArg (fun z =>
    integralSingularCapProduct (k + 1) m (integralSingularCoboundary X k (k + 1) φ)
      (((integralSingularChains X).XIsoOfEq
        (show k + m + 1 = (k + 1) + m by omega)).hom c) + z) heval)

theorem integralSingularCapProduct_boundary_is_boundary (k m : ℕ)
    (φ : integralSingularCochain k X) (hφ : integralSingularCoboundary X k (k + 1) φ = 0)
    (c : (integralSingularChains X).X (k + m + 1)) :
    ∃ b : (integralSingularChains X).X (m + 1),
      (integralSingularChains X).d (m + 1) m b =
        integralSingularCapProduct k m φ
          ((integralSingularChains X).d (k + m + 1) (k + m) c) := by
  refine ⟨(-1 : ℤ) ^ k • integralSingularCapProduct k (m + 1) φ c, ?_⟩
  rw [map_zsmul, integralSingularCapProduct_boundary_apply, hφ, map_zero,
    LinearMap.zero_apply, zero_add]

theorem integralSingularCapProduct_coboundary_is_boundary (k m : ℕ)
    (φ : integralSingularCochain k X) (c : (integralSingularChains X).X (k + m + 1))
    (hc : (integralSingularChains X).d (k + m + 1) (k + m) c = 0) :
    ∃ b : (integralSingularChains X).X (m + 1),
      (integralSingularChains X).d (m + 1) m b =
        integralSingularCapProduct (k + 1) m (integralSingularCoboundary X k (k + 1) φ)
          (((integralSingularChains X).XIsoOfEq
            (show k + m + 1 = (k + 1) + m by omega)).hom c) := by
  have h := integralSingularCapProduct_boundary_apply k m φ c
  rw [hc, map_zero] at h
  refine ⟨-((-1 : ℤ) ^ k • integralSingularCapProduct k (m + 1) φ c), ?_⟩
  rw [map_neg, map_zsmul]
  exact (eq_neg_iff_add_eq_zero.mpr h.symm).symm

def integralSingularCapCycleMap (k m : ℕ)
    (φ : integralSingularCochain k X) (hφ : integralSingularCoboundary X k (k + 1) φ = 0) :
    LinearMap.ker ((integralSingularChains X).sc (k + m)).g.hom →ₗ[ℤ]
      LinearMap.ker ((integralSingularChains X).sc m).g.hom :=
  ((integralSingularCapProduct k m φ).comp
    (LinearMap.ker ((integralSingularChains X).sc (k + m)).g.hom).subtype).codRestrict (LinearMap.ker ((integralSingularChains X).sc m).g.hom) (by
      intro c
      change (integralSingularChains X).d m ((ComplexShape.down ℕ).next m)
        (integralSingularCapProduct k m φ c.val) = 0
      cases m with
      | zero =>
        rw [ChainComplex.next_nat_zero, (integralSingularChains X).shape 0 0 (by simp)]
        rfl
      | succ m =>
        rw [ChainComplex.next_nat_succ]
        apply integralSingularCapProduct_boundary_eq_zero k m φ hφ
        have hc := c.property
        change (integralSingularChains X).d (k + m + 1)
          ((ComplexShape.down ℕ).next (k + m + 1)) c.val = 0 at hc
        rw [ChainComplex.next_nat_succ] at hc
        exact hc)

theorem integralSingularCapCycleMap_apply (k m : ℕ)
    (φ : integralSingularCochain k X) (hφ : integralSingularCoboundary X k (k + 1) φ = 0)
    (c : LinearMap.ker ((integralSingularChains X).sc (k + m)).g.hom) :
    (integralSingularCapCycleMap k m φ hφ c).val =
      integralSingularCapProduct k m φ c.val := rfl

theorem integralSingularHomologyClass_eq_zero_iff (n : ℕ)
    (c : LinearMap.ker ((integralSingularChains X).sc n).g.hom) :
    moduleHomologyClass ((integralSingularChains X).sc n) c = 0 ↔
      ∃ b : (integralSingularChains X).X (n + 1),
        (integralSingularChains X).d (n + 1) n b = c.val := by
  have h := moduleHomologyClass_eq_zero_iff ((integralSingularChains X).sc n) c
  change (_ ↔ ∃ b : (integralSingularChains X).X ((ComplexShape.down ℕ).prev n),
    (integralSingularChains X).d ((ComplexShape.down ℕ).prev n) n b = c.val) at h
  exact h.trans (congrArg (fun i => ∃ b : (integralSingularChains X).X i,
    (integralSingularChains X).d i n b = c.val) (ChainComplex.prev ℕ n)).to_iff

def integralSingularCapHomology (k m : ℕ)
    (φ : integralSingularCochain k X) (hφ : integralSingularCoboundary X k (k + 1) φ = 0) :
    integralSingularHomology (k + m) X →ₗ[ℤ] integralSingularHomology m X := by
  let S := (integralSingularChains X).sc (k + m)
  let T := (integralSingularChains X).sc m
  let f := (moduleHomologyClass T).comp (integralSingularCapCycleMap k m φ hφ)
  refine ((LinearMap.range S.moduleCatToCycles).liftQ f ?_).comp
    S.moduleCatHomologyIso.hom.hom
  rintro c ⟨b, rfl⟩
  change moduleHomologyClass T
    (integralSingularCapCycleMap k m φ hφ (S.moduleCatToCycles b)) = 0
  apply (integralSingularHomologyClass_eq_zero_iff m _).2
  let b' := ((integralSingularChains X).xPrevIso
    (i := k + m + 1) (j := k + m) rfl).hom b
  have hb : (integralSingularChains X).d (k + m + 1) (k + m) b' =
      (S.moduleCatToCycles b).val := by
    change _ = (integralSingularChains X).dTo (k + m) b
    rw [(integralSingularChains X).dTo_eq (i := k + m + 1) rfl]
    rfl
  obtain ⟨a, ha⟩ := integralSingularCapProduct_boundary_is_boundary k m φ hφ b'
  exact ⟨a, ha.trans (congrArg (integralSingularCapProduct k m φ) hb)⟩

theorem integralSingularCapHomology_class (k m : ℕ)
    (φ : integralSingularCochain k X) (hφ : integralSingularCoboundary X k (k + 1) φ = 0)
    (c : LinearMap.ker ((integralSingularChains X).sc (k + m)).g.hom) :
    integralSingularCapHomology k m φ hφ
        (moduleHomologyClass ((integralSingularChains X).sc (k + m)) c) =
      moduleHomologyClass ((integralSingularChains X).sc m)
        (integralSingularCapCycleMap k m φ hφ c) := by
  unfold integralSingularCapHomology
  erw [LinearMap.comp_apply, moduleHomologyClass_quotient]
  rfl

theorem integralSingularCocycle_closed (k : ℕ)
    (φ : LinearMap.ker ((integralSingularCochains X).sc k).g.hom) :
    integralSingularCoboundary X k (k + 1) φ.val = 0 := by
  have h := φ.property
  change integralSingularCoboundary X k ((ComplexShape.up ℕ).next k) φ.val = 0 at h
  rwa [CochainComplex.next] at h

def integralSingularCapCocycles (k m : ℕ) :
    LinearMap.ker ((integralSingularCochains X).sc k).g.hom →ₗ[ℤ]
      integralSingularHomology (k + m) X →ₗ[ℤ] integralSingularHomology m X := by
  let f : LinearMap.ker ((integralSingularCochains X).sc k).g.hom →+
      (integralSingularHomology (k + m) X →ₗ[ℤ] integralSingularHomology m X) :=
    { toFun := fun φ => integralSingularCapHomology k m φ.val
        (integralSingularCocycle_closed k φ)
      map_zero' := by
        apply LinearMap.ext
        intro a
        obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective
          ((integralSingularChains X).sc (k + m)) a
        erw [integralSingularCapHomology_class]
        change moduleHomologyClass ((integralSingularChains X).sc m)
          (integralSingularCapCycleMap k m 0 _ c) = 0
        have hzero : integralSingularCapCycleMap k m (0 : integralSingularCochain k X)
            (integralSingularCocycle_closed k 0) c = 0 := by
          apply Subtype.ext
          change integralSingularCapProduct k m 0 c.val = 0
          erw [map_zero, LinearMap.zero_apply]
        rw [hzero, map_zero]
      map_add' := fun φ ψ => by
        apply LinearMap.ext
        intro a
        obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective
          ((integralSingularChains X).sc (k + m)) a
        erw [LinearMap.add_apply, integralSingularCapHomology_class,
          integralSingularCapHomology_class, integralSingularCapHomology_class, ← map_add]
        congr 1
        apply Subtype.ext
        change integralSingularCapProduct k m (φ.val + ψ.val) c.val =
          integralSingularCapProduct k m φ.val c.val + integralSingularCapProduct k m ψ.val c.val
        erw [map_add, LinearMap.add_apply] }
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun z φ => by
        simpa only [Int.cast_id, RingHom.id_apply] using! map_intCast_smul f ℤ ℤ z φ }

theorem integralSingularCapCocycles_class (k m : ℕ)
    (φ : LinearMap.ker ((integralSingularCochains X).sc k).g.hom)
    (c : LinearMap.ker ((integralSingularChains X).sc (k + m)).g.hom) :
    integralSingularCapCocycles k m φ
        (moduleHomologyClass ((integralSingularChains X).sc (k + m)) c) =
      moduleHomologyClass ((integralSingularChains X).sc m)
        (integralSingularCapCycleMap k m φ.val (integralSingularCocycle_closed k φ) c) :=
  integralSingularCapHomology_class k m φ.val (integralSingularCocycle_closed k φ) c

theorem integralSingularCapCocycles_boundary (k m : ℕ)
    (ψ : ((integralSingularCochains X).sc k).X₁) :
    integralSingularCapCocycles k m
      (((integralSingularCochains X).sc k).moduleCatToCycles ψ) = 0 := by
  cases k with
  | zero =>
    have hzero : ((integralSingularCochains X).sc 0).moduleCatToCycles ψ = 0 := by
      apply Subtype.ext
      change (integralSingularCochains X).dTo 0 ψ = 0
      rw [(integralSingularCochains X).dTo_eq_zero (by
        rw [CochainComplex.prev_nat_zero]
        simp)]
      rfl
    rw [hzero, map_zero]
  | succ k =>
    apply LinearMap.ext
    intro a
    obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective
      ((integralSingularChains X).sc ((k + 1) + m)) a
    erw [integralSingularCapCocycles_class]
    apply (integralSingularHomologyClass_eq_zero_iff m _).2
    let ψ' := ((integralSingularCochains X).xPrevIso (i := k) (j := k + 1) rfl).hom ψ
    have hψ : integralSingularCoboundary X k (k + 1) ψ' =
        (((integralSingularCochains X).sc (k + 1)).moduleCatToCycles ψ).val := by
      change (integralSingularCochains X).d k (k + 1) ψ' =
        (integralSingularCochains X).dTo (k + 1) ψ
      rw [(integralSingularCochains X).dTo_eq (i := k) rfl]
      rfl
    let h : k + m + 1 = (k + 1) + m := by omega
    let ι := (integralSingularChains X).XIsoOfEq h
    let c' := ι.inv c.val
    have hn : (ComplexShape.down ℕ).next ((k + 1) + m) = k + m := by
      rw [← h, ChainComplex.next_nat_succ]
    have hc := c.property
    change (integralSingularChains X).d ((k + 1) + m)
      ((ComplexShape.down ℕ).next ((k + 1) + m)) c.val = 0 at hc
    rw [hn] at hc
    have hc' : (integralSingularChains X).d (k + m + 1) (k + m) c' = 0 := by
      have heq := congrArg (fun f : (integralSingularChains X).X ((k + 1) + m) ⟶
        (integralSingularChains X).X (k + m) => f c.val)
        ((integralSingularChains X).XIsoOfEq_inv_comp_d h (k + m))
      exact heq.trans hc
    have hback : ι.hom c' = c.val := by
      change (ι.inv ≫ ι.hom) c.val = c.val
      rw [Iso.inv_hom_id]
      rfl
    obtain ⟨b, hb⟩ := integralSingularCapProduct_coboundary_is_boundary k m ψ' c' hc'
    refine ⟨b, hb.trans ?_⟩
    change integralSingularCapProduct (k + 1) m
      (integralSingularCoboundary X k (k + 1) ψ') (ι.hom c') = _
    rw [hback, hψ]
    rfl

def integralSingularCohomologyCapProduct (k m : ℕ) :
    integralSingularCohomology k X →ₗ[ℤ]
      integralSingularHomology (k + m) X →ₗ[ℤ] integralSingularHomology m X := by
  let S := (integralSingularCochains X).sc k
  refine ((LinearMap.range S.moduleCatToCycles).liftQ (integralSingularCapCocycles k m) ?_).comp
    S.moduleCatHomologyIso.hom.hom
  rintro φ ⟨ψ, rfl⟩
  exact integralSingularCapCocycles_boundary k m ψ

private theorem integralSingularCohomologyCapProduct_cocycle (k m : ℕ)
    (φ : LinearMap.ker ((integralSingularCochains X).sc k).g.hom) :
    integralSingularCohomologyCapProduct k m
        (moduleHomologyClass ((integralSingularCochains X).sc k) φ) =
      integralSingularCapCocycles k m φ := by
  unfold integralSingularCohomologyCapProduct
  dsimp only
  erw [LinearMap.comp_apply, moduleHomologyClass_quotient]
  rfl

theorem integralSingularCohomologyCapProduct_class (k m : ℕ)
    (φ : LinearMap.ker ((integralSingularCochains X).sc k).g.hom)
    (c : LinearMap.ker ((integralSingularChains X).sc (k + m)).g.hom) :
    integralSingularCohomologyCapProduct k m
        (moduleHomologyClass ((integralSingularCochains X).sc k) φ)
        (moduleHomologyClass ((integralSingularChains X).sc (k + m)) c) =
      moduleHomologyClass ((integralSingularChains X).sc m)
        (integralSingularCapCycleMap k m φ.val (integralSingularCocycle_closed k φ) c) := by
  rw [integralSingularCohomologyCapProduct_cocycle]
  exact integralSingularCapCocycles_class k m φ c

theorem integralSingularCohomologyCapProduct_natural (k m : ℕ)
    (f : ContinuousMap X Y) (φ : integralSingularCohomology k Y)
    (c : integralSingularHomology (k + m) X) :
    integralSingularHomologyMap m f
        (integralSingularCohomologyCapProduct k m (integralSingularCohomologyMap k f φ) c) =
      integralSingularCohomologyCapProduct k m φ (integralSingularHomologyMap (k + m) f c) := by
  obtain ⟨φ, rfl⟩ := moduleHomologyClass_surjective ((integralSingularCochains Y).sc k) φ
  obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective ((integralSingularChains X).sc (k + m)) c
  let P := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) k).map
    (integralSingularCochainMap f)
  let Q := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ)
    (k + m)).map (integralSingularChainMap f)
  let R := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) m).map
    (integralSingularChainMap f)
  have hφ : integralSingularCohomologyMap k f
      (moduleHomologyClass ((integralSingularCochains Y).sc k) φ) =
      moduleHomologyClass ((integralSingularCochains X).sc k) (moduleCycleMap P φ) :=
    moduleHomologyClass_map P φ
  have hc : integralSingularHomologyMap (k + m) f
      (moduleHomologyClass ((integralSingularChains X).sc (k + m)) c) =
      moduleHomologyClass ((integralSingularChains Y).sc (k + m)) (moduleCycleMap Q c) :=
    moduleHomologyClass_map Q c
  rw [hφ, hc]
  erw [integralSingularCohomologyCapProduct_class, integralSingularCohomologyCapProduct_class]
  have hout := moduleHomologyClass_map R
    (integralSingularCapCycleMap k m (moduleCycleMap P φ).val
      (integralSingularCocycle_closed k (moduleCycleMap P φ)) c)
  change integralSingularHomologyMap m f _ = _ at hout
  rw [hout]
  congr 1
  apply Subtype.ext
  change (integralSingularChainMap f).f m
      (integralSingularCapProduct k m (integralSingularCochainPullback k f φ.val) c.val) =
    integralSingularCapProduct k m φ.val ((integralSingularChainMap f).f (k + m) c.val)
  exact congrArg (fun L : (integralSingularChains X).X (k + m) →ₗ[ℤ]
    (integralSingularChains Y).X m => L c.val) (integralSingularCapProduct_natural k m f φ.val)

def integralSingularUnitCocycle :
    LinearMap.ker ((integralSingularCochains X).sc 0).g.hom := by
  refine ⟨(ULift.moduleEquiv : integralSingularCoefficients ≃ₗ[ℤ] ℤ).symm.toLinearMap.comp
    integralSingularAugmentation, ?_⟩
  change integralSingularCoboundary X 0 ((ComplexShape.up ℕ).next 0) _ = 0
  rw [CochainComplex.next]
  apply LinearMap.ext
  intro c
  change ULift.up (integralSingularAugmentation ((integralSingularChains X).d 1 0 c)) = 0
  have h := congrArg (fun f : (integralSingularChains X).X 1 →ₗ[ℤ] ℤ => f c)
    (integralSingularAugmentation_boundary (X := X))
  change integralSingularAugmentation ((integralSingularChains X).d 1 0 c) = 0 at h
  rw [h]
  rfl

def integralSingularCohomologyUnit (X : Type u) [TopologicalSpace X] :
    integralSingularCohomology 0 X :=
  moduleHomologyClass ((integralSingularCochains X).sc 0) integralSingularUnitCocycle

private theorem integralSingularHomologyClass_transport {i j : ℕ} (h : i = j)
    (c : LinearMap.ker ((integralSingularChains X).sc i).g.hom) :
    (eqToHom (congrArg (fun n => integralSingularHomology n X) h))
        (moduleHomologyClass ((integralSingularChains X).sc i) c) =
      moduleHomologyClass ((integralSingularChains X).sc j)
        ⟨((integralSingularChains X).XIsoOfEq h).hom c.val, by subst j; exact c.property⟩ := by
  subst j
  rfl

theorem integralSingularCohomologyCapProduct_unit (m : ℕ)
    (c : integralSingularHomology (0 + m) X) :
    integralSingularCohomologyCapProduct 0 m (integralSingularCohomologyUnit X) c =
      (eqToHom (congrArg (fun n => integralSingularHomology n X) (Nat.zero_add m))) c := by
  obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective ((integralSingularChains X).sc (0 + m)) c
  unfold integralSingularCohomologyUnit
  rw [integralSingularCohomologyCapProduct_class,
    integralSingularHomologyClass_transport (Nat.zero_add m)]
  congr 1
  apply Subtype.ext
  change integralSingularCapProduct 0 m
    ((ULift.moduleEquiv : integralSingularCoefficients ≃ₗ[ℤ] ℤ).symm.toLinearMap.comp
      integralSingularAugmentation) c.val = _
  rw [integralSingularCapProduct_augmentation]

theorem integralSingularCohomologyMap_unit
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : ContinuousMap X Y) :
    integralSingularCohomologyMap 0 f (integralSingularCohomologyUnit Y) =
      integralSingularCohomologyUnit X := by
  let P := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ)
    (ComplexShape.up ℕ) 0).map (integralSingularCochainMap f)
  have h := moduleHomologyClass_map P (integralSingularUnitCocycle (X := Y))
  change integralSingularCohomologyMap 0 f (integralSingularCohomologyUnit Y) = _ at h
  rw [h]
  change moduleHomologyClass ((integralSingularCochains X).sc 0) _ =
    moduleHomologyClass ((integralSingularCochains X).sc 0) _
  congr 1
  apply Subtype.ext
  apply (integralSingularChainBasis 0 X).ext
  intro σ
  rw [integralSingularChainBasis_apply]
  change ULift.up (integralSingularAugmentation
    ((integralSingularChainMap f).f 0 (integralSimplexChain 0 σ))) =
      ULift.up (integralSingularAugmentation (integralSimplexChain 0 σ))
  rw [integralSimplexChain_map, integralSingularAugmentation_simplex,
    integralSingularAugmentation_simplex]

end DifferentialGeometry.Topology

end
