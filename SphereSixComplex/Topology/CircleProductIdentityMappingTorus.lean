module

public import SphereSixComplex.Topology.PaperAffineCyclicReducedFiberMappingTorus
public import SphereSixComplex.Topology.WangHomologyPresentationProof

/-!
# The product as the mapping torus of the identity

The real-line quotient model identifies `S¹ × X` with the mapping torus of the identity of `X`.
Transporting the constructed Mayer--Vietoris Wang sequence through this homeomorphism gives a
canonical product Wang boundary, with no arbitrary choice of an automorphism of `Hₖ(X)`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.CircleProductIdentityMappingTorus

open CyclicAngularFundamentalDomain
open StandardTorusHomology

variable {X : Type} [TopologicalSpace X]

/-- The standard real-line quotient map onto the product. -/
public def realToCircleProduct : C(ℝ × X, UnitAddCircle × X) where
  toFun p := ((p.1 : UnitAddCircle), p.2)
  continuous_toFun := by fun_prop

public theorem realToCircleProduct_surjective :
    Function.Surjective (realToCircleProduct (X := X)) := by
  rintro ⟨s, x⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective
    (s := AddSubgroup.zmultiples (1 : ℝ)) s
  exact ⟨(t, x), rfl⟩

public theorem realToCircleProduct_isQuotientMap :
    IsQuotientMap (realToCircleProduct (X := X)) := by
  have hopen : IsOpenMap (fun t : ℝ ↦ (t : UnitAddCircle)) :=
    (AddCircle.isLocalHomeomorph_coe (1 : ℝ)).isOpenMap
  exact IsOpenMap.isQuotientMap (hopen.prodMap IsOpenMap.id)
    (realToCircleProduct (X := X)).continuous realToCircleProduct_surjective

public theorem realToCircleProduct_eq_iff (p q : ℝ × X) :
    realToCircleProduct p = realToCircleProduct q ↔
      Quotient.mk (realMappingTorusSetoid (Homeomorph.refl X)) p =
        Quotient.mk (realMappingTorusSetoid (Homeomorph.refl X)) q := by
  rw [realMappingTorusMk_eq_iff]
  constructor
  · intro h
    have hcircle := congrArg Prod.fst h
    have hfibre := congrArg Prod.snd h
    obtain ⟨k, hk⟩ := (unitAddCircle_eq_iff p.1 q.1).mp hcircle
    refine ⟨k, ?_⟩
    rw [mappingTorusShift_apply]
    apply Prod.ext
    · push_cast at hk ⊢
      linarith
    · have hrefl : Homeomorph.refl X = 1 := rfl
      rw [hrefl, one_zpow]
      exact hfibre.symm
  · rintro ⟨k, hk⟩
    rw [mappingTorusShift_apply] at hk
    have hreal := congrArg Prod.fst hk
    have hfibre := congrArg Prod.snd hk
    apply Prod.ext
    · apply (unitAddCircle_eq_iff p.1 q.1).mpr
      refine ⟨k, ?_⟩
      push_cast at hreal ⊢
      linarith
    · have hrefl : Homeomorph.refl X = 1 := rfl
      rw [hrefl, one_zpow] at hfibre
      exact hfibre.symm

/-- The product is the real mapping torus of the identity. -/
public noncomputable def circleProductRealMappingTorusHomeomorph :
    UnitAddCircle × X ≃ₜ RealMappingTorus (Homeomorph.refl X) :=
  homeomorphOfQuotientMaps realToCircleProduct_isQuotientMap
    ((isOpenMap_realMappingTorusMk (Homeomorph.refl X)).isQuotientMap
      continuous_quot_mk Quotient.mk_surjective)
    realToCircleProduct_eq_iff

public theorem circleProductRealMappingTorusHomeomorph_real
    (p : ℝ × X) :
    circleProductRealMappingTorusHomeomorph (realToCircleProduct p) =
      Quotient.mk (realMappingTorusSetoid (Homeomorph.refl X)) p := by
  unfold circleProductRealMappingTorusHomeomorph homeomorphOfQuotientMaps
  dsimp only
  apply (realToCircleProduct_eq_iff _ _).mp
  exact Function.surjInv_eq realToCircleProduct_surjective _

/-- The canonical homeomorphism from the product to the identity mapping torus. -/
public noncomputable def circleProductIdentityMappingTorusHomeomorph :
    UnitAddCircle × X ≃ₜ CircleMappingTorus (Homeomorph.refl X) :=
  circleProductRealMappingTorusHomeomorph.trans
    (realMappingTorusHomeomorph (Homeomorph.refl X))

private theorem realMappingTorusHomeomorph_mk_zero (x : X) :
    realMappingTorusHomeomorph (Homeomorph.refl X)
        (Quotient.mk (realMappingTorusSetoid (Homeomorph.refl X)) ((0 : ℝ), x)) =
      finiteBouquetMappingTorusFiberInclusion
        (fun _ : Unit ↦ Homeomorph.refl X) x := by
  let D := realMappingTorusClutchingData (Homeomorph.refl X)
  change D.totalHomeomorphCircleMappingTorus (D.projection ((0 : unitInterval), x)) = _
  let e : CircleMappingTorus (Homeomorph.refl X) ≃
      RealMappingTorus (Homeomorph.refl X) :=
    Equiv.ofBijective D.circleToTotal D.circleToTotal_bijective
  apply e.injective
  change D.circleToTotal
      (D.totalHomeomorphCircleMappingTorus (D.projection ((0 : unitInterval), x))) =
    D.circleToTotal
      (finiteBouquetMappingTorusFiberInclusion
        (fun _ : Unit ↦ Homeomorph.refl X) x)
  rw [show D.circleToTotal (D.totalHomeomorphCircleMappingTorus
      (D.projection ((0 : unitInterval), x))) = D.projection ((0 : unitInterval), x) by
    exact D.totalHomeomorphCircleMappingTorus.symm_apply_apply _]
  rfl

public theorem circleProductIdentityMappingTorusHomeomorph_fiber (x : X) :
    circleProductIdentityMappingTorusHomeomorph (0, x) =
      finiteBouquetMappingTorusFiberInclusion
        (fun _ : Unit ↦ Homeomorph.refl X) x := by
  rw [circleProductIdentityMappingTorusHomeomorph, Homeomorph.trans_apply]
  have h := circleProductRealMappingTorusHomeomorph_real (X := X) ((0 : ℝ), x)
  change circleProductRealMappingTorusHomeomorph (0, x) = _ at h
  rw [h]
  exact realMappingTorusHomeomorph_mk_zero x

public theorem circleProductIdentityMappingTorusHomeomorph_comp_fiberInclusion :
    (⟨circleProductIdentityMappingTorusHomeomorph,
        circleProductIdentityMappingTorusHomeomorph.continuous⟩ :
        C(UnitAddCircle × X, CircleMappingTorus (Homeomorph.refl X))).comp
      ({ toFun := fun x ↦ (0, x)
         continuous_toFun := continuous_const.prodMk continuous_id } : C(X, UnitAddCircle × X)) =
    finiteBouquetMappingTorusFiberInclusion
      (fun _ : Unit ↦ Homeomorph.refl X) := by
  ext x
  exact circleProductIdentityMappingTorusHomeomorph_fiber x

/-- Inclusion of the fibre over the positively oriented circle origin. -/
public def productFiberInclusion : C(X, UnitAddCircle × X) where
  toFun x := (0, x)
  continuous_toFun := continuous_const.prodMk continuous_id

public theorem circleProductIdentityMappingTorusHomeomorph_comp_productFiberInclusion :
    (⟨circleProductIdentityMappingTorusHomeomorph,
        circleProductIdentityMappingTorusHomeomorph.continuous⟩ :
        C(UnitAddCircle × X, CircleMappingTorus (Homeomorph.refl X))).comp
      productFiberInclusion =
    finiteBouquetMappingTorusFiberInclusion
      (fun _ : Unit ↦ Homeomorph.refl X) :=
  circleProductIdentityMappingTorusHomeomorph_comp_fiberInclusion

/-- The canonical product Wang boundary, transported from the constructed Mayer--Vietoris
boundary for the mapping torus of the identity. -/
public noncomputable def canonicalProductWangBoundary (k : ℕ) :
    IntegralSingularHomology (k + 1) (UnitAddCircle × X) →+
    IntegralSingularHomology k X :=
  (circleMappingTorusWangPresentationOfCover (Homeomorph.refl X) k).boundary.comp
    (integralSingularHomologyMap (k + 1)
      (circleProductIdentityMappingTorusHomeomorph (X := X) :
        C(UnitAddCircle × X, CircleMappingTorus (Homeomorph.refl X))))

private theorem canonical_inclusion_naturality (k : ℕ)
    (x : IntegralSingularHomology (k + 1) X) :
    integralSingularHomologyMap (k + 1)
        (circleProductIdentityMappingTorusHomeomorph (X := X) :
          C(UnitAddCircle × X, CircleMappingTorus (Homeomorph.refl X)))
        (integralSingularHomologyMap (k + 1) (productFiberInclusion (X := X)) x) =
      (circleMappingTorusWangPresentationOfCover
        (Homeomorph.refl X) k).inclusion x := by
  rw [integralSingularHomologyMap_comp_wang,
    circleProductIdentityMappingTorusHomeomorph_comp_productFiberInclusion]
  rfl

public theorem canonicalProductFiberInclusion_injective (k : ℕ) :
    Function.Injective
      (integralSingularHomologyMap (k + 1) (productFiberInclusion (X := X))) := by
  let P := circleMappingTorusWangPresentationOfCover (Homeomorph.refl X) k
  have hhigh : P.highDifference = 0 :=
    circleMonodromyDifference_refl (F := X) (k + 1)
  have hPinclusion : Function.Injective P.inclusion := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy⟩ := (P.exact_highDifference_inclusion x).mp hx
    rw [hhigh] at hy
    simpa using hy.symm
  intro x y hxy
  apply hPinclusion
  rw [← canonical_inclusion_naturality k, ← canonical_inclusion_naturality k, hxy]

public theorem canonicalProductWangBoundary_surjective (k : ℕ) :
    Function.Surjective (canonicalProductWangBoundary (X := X) k) := by
  let P := circleMappingTorusWangPresentationOfCover (Homeomorph.refl X) k
  have hlow : P.lowDifference = 0 := circleMonodromyDifference_refl (F := X) k
  have hboundary : Function.Surjective P.boundary := by
    intro y
    exact (P.exact_boundary_lowDifference y).mp (by rw [hlow]; rfl)
  intro y
  obtain ⟨z, hz⟩ := hboundary y
  let eH := integralSingularHomologyEquiv (k + 1)
    (circleProductIdentityMappingTorusHomeomorph (X := X))
  refine ⟨eH.symm z, ?_⟩
  simp only [canonicalProductWangBoundary, AddMonoidHom.comp_apply]
  change P.boundary (eH (eH.symm z)) = y
  rw [eH.apply_symm_apply, hz]

public theorem canonicalProductWang_exact (k : ℕ) :
    Function.Exact
      (integralSingularHomologyMap (k + 1) (productFiberInclusion (X := X)))
      (canonicalProductWangBoundary (X := X) k) := by
  let P := circleMappingTorusWangPresentationOfCover (Homeomorph.refl X) k
  let eH := integralSingularHomologyEquiv (k + 1)
    (circleProductIdentityMappingTorusHomeomorph (X := X))
  intro z
  simp only [canonicalProductWangBoundary, AddMonoidHom.comp_apply]
  change P.boundary (eH z) = 0 ↔ _
  rw [P.exact_inclusion_boundary (eH z)]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, eH.injective ?_⟩
    calc
      eH (integralSingularHomologyMap (k + 1) productFiberInclusion x) =
          P.inclusion x := canonical_inclusion_naturality k x
      _ = eH z := hx
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    calc
      P.inclusion x =
          eH (integralSingularHomologyMap (k + 1) productFiberInclusion x) :=
        (canonical_inclusion_naturality k x).symm
      _ = eH z := congrArg eH hx

/-- All exactness data of the canonical product Wang presentation. -/
public theorem canonicalProductWangData (k : ℕ) :
    Function.Injective
        (integralSingularHomologyMap (k + 1) (productFiberInclusion (X := X))) ∧
      Function.Exact
        (integralSingularHomologyMap (k + 1) (productFiberInclusion (X := X)))
        (canonicalProductWangBoundary (X := X) k) ∧
      Function.Surjective (canonicalProductWangBoundary (X := X) k) :=
  ⟨canonicalProductFiberInclusion_injective k,
    canonicalProductWang_exact k,
    canonicalProductWangBoundary_surjective k⟩

end SphereSixComplex.Topology.CircleProductIdentityMappingTorus

end

end
