module

public import SphereSixComplex.Prerequisites.Topology.CyclicPuncturedProductMappingTorus

@[expose] public section
noncomputable section
open AlgebraicTopology Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.StandardTorusHomology

public theorem unitAddCircle_eq_iff (t t' : ℝ) :
    ((t : UnitAddCircle)) = (t' : UnitAddCircle) ↔ ∃ k : ℤ, t - t' = k := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk]; simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by simp [hk]⟩

end SphereSixComplex.StandardTorusHomology

namespace SphereSixComplex.Topology.CircleProductIdentityMappingTorus
open CyclicAngularFundamentalDomain StandardTorusHomology
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

public theorem realMappingTorusHomeomorph_intervalProjection
    {X : Type} [TopologicalSpace X] (phi : X ≃ₜ X) (p : unitInterval × X) :
    realMappingTorusHomeomorph phi (realMappingTorusIntervalProjection phi p) =
      circleMappingTorusCylinderProjection phi p := by
  let D := realMappingTorusClutchingData phi
  let e : CircleMappingTorus phi ≃ RealMappingTorus phi :=
    Equiv.ofBijective D.circleToTotal D.circleToTotal_bijective
  apply e.injective
  change D.circleToTotal
      (D.totalHomeomorphCircleMappingTorus (D.projection p)) =
    D.circleToTotal (circleMappingTorusCylinderProjection phi p)
  rw [show D.circleToTotal
      (D.totalHomeomorphCircleMappingTorus (D.projection p)) = D.projection p by
    exact D.totalHomeomorphCircleMappingTorus.symm_apply_apply _]
  exact D.circleToTotal_mk p

public theorem circleProductIdentityMappingTorusHomeomorph_interval
    (t : unitInterval) (x : X) :
    circleProductIdentityMappingTorusHomeomorph (((t : ℝ) : UnitAddCircle), x) =
      circleMappingTorusCylinderProjection (Homeomorph.refl X) (t, x) := by
  rw [circleProductIdentityMappingTorusHomeomorph, Homeomorph.trans_apply]
  have h := circleProductRealMappingTorusHomeomorph_real (X := X) ((t : ℝ), x)
  change circleProductRealMappingTorusHomeomorph (((t : ℝ) : UnitAddCircle), x) = _ at h
  rw [h]
  exact realMappingTorusHomeomorph_intervalProjection (Homeomorph.refl X) (t, x)

public theorem circleProductIdentityMappingTorusHomeomorph_fiber (x : X) :
    circleProductIdentityMappingTorusHomeomorph (0, x) =
      finiteBouquetMappingTorusFiberInclusion
        (fun _ : Unit ↦ Homeomorph.refl X) x :=
  circleProductIdentityMappingTorusHomeomorph_interval 0 x

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


end SphereSixComplex.Topology.CircleProductIdentityMappingTorus
