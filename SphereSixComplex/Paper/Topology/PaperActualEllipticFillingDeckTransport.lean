module

public import SphereSixComplex.Paper.Topology.PaperEllipticFillingDeckSignAudit
public import SphereSixComplex.Paper.Topology.PaperEllipticFillingRealPeriodCoverTransport

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods
open SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.AffineCyclicQuotientHomology
open _root_.SphereSixComplex.AffineCyclicQuotientHomology
open SphereSixComplex.EllipticFilling

variable (A : AnalyticData)

@[simp]
public theorem orderThreeCentralFiberPresentationData_affine_eq :
    (orderThreeCentralFiberPresentationData A.periods).affine =
      orderThreeDescendedAffineTorusAutomorphism A.periods := rfl

@[simp]
public theorem orderFourCentralFiberPresentationData_affine_eq :
    (orderFourCentralFiberPresentationData A.periods).affine =
      orderFourDescendedAffineTorusAutomorphism A.periods := rfl

public theorem affineDeckIntegerMonodromy_eq_integerAffineMonodromy
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p) :
    affineDeckIntegerMonodromy D.latticeMap.toAddEquiv =
      integerAffineMonodromy D.latticeMap.toAddEquiv := by
  apply MonoidHom.ext
  intro k
  apply DFunLike.ext _ _
  intro n
  apply Multiplicative.toAdd.injective
  rw [affineDeckIntegerMonodromy_apply]
  symm
  change (k.toAdd • D.latticeMap.toAddEquiv) n.toAdd = _
  induction k.toAdd using Int.induction_on generalizing n with
  | zero => simp
  | succ i ih =>
      rw [add_zsmul, one_zsmul, AddAut.add_apply]
      have hih := ih (Multiplicative.ofAdd (D.latticeMap n.toAdd))
      change ((i : ℤ) • D.latticeMap.toAddEquiv) (D.latticeMap n.toAdd) =
        (D.latticeMap.toEquiv ^ (i : ℤ)) (D.latticeMap n.toAdd) at hih
      change ((i : ℤ) • D.latticeMap.toAddEquiv) (D.latticeMap n.toAdd) = _
      rw [hih]
      rw [show D.latticeMap.toEquiv ^ ((i : ℤ) + 1) =
          D.latticeMap.toEquiv ^ (i : ℤ) * D.latticeMap.toEquiv by rw [zpow_add_one],
        Equiv.Perm.mul_apply]
      rfl
  | pred i ih =>
      rw [sub_eq_add_neg, add_zsmul, neg_one_zsmul, AddAut.add_apply]
      have hih := ih (Multiplicative.ofAdd ((-D.latticeMap.toAddEquiv) n.toAdd))
      change ((- (i : ℤ)) • D.latticeMap.toAddEquiv)
          ((-D.latticeMap.toAddEquiv) n.toAdd) =
        (D.latticeMap.toEquiv ^ (- (i : ℤ)))
          ((-D.latticeMap.toAddEquiv) n.toAdd) at hih
      rw [hih]
      change (D.latticeMap.toEquiv ^ (- (i : ℤ))) (D.latticeMap.symm n.toAdd) = _
      rw [show D.latticeMap.toEquiv ^ (- (i : ℤ) + -1) =
          D.latticeMap.toEquiv ^ (- (i : ℤ)) * D.latticeMap.toEquiv⁻¹ by
        rw [zpow_add]
        simp,
        Equiv.Perm.mul_apply]
      apply congrArg (D.latticeMap.toEquiv ^ (- (i : ℤ)))
      rfl





private theorem inverse_meridian_negative_twist_relation
    {G : Type*} [Group G] (g t : G) (m : ℕ) (h : Commute g t) :
    g⁻¹ ^ m * (t⁻¹)⁻¹ = (g ^ m * t⁻¹)⁻¹ := by
  rw [inv_inv, mul_inv_rev, inv_pow]
  simpa using (h.pow_left m).inv_left.eq

public theorem normalClosure_singleton_inv {G : Type*} [Group G] (g : G) :
    Subgroup.normalClosure {g⁻¹} = Subgroup.normalClosure {g} := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    exact Subgroup.inv_mem _
      (Subgroup.subset_normalClosure (Set.mem_singleton g))
  · apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    have hg : g⁻¹ ∈ Subgroup.normalClosure {g⁻¹} :=
      Subgroup.subset_normalClosure (Set.mem_singleton g⁻¹)
    simpa using Subgroup.inv_mem (Subgroup.normalClosure {g⁻¹}) hg



/-- The actual order-three boundary deck group identified directly with the central
presentation's deck group. -/
public noncomputable def ellipticThreeToCentralBoundaryDeckEquiv :
    OrderThreeAffineMappingTorusDeck A.periods ≃*
      CanonicalCyclicAffineBoundaryDeck
        (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv where
  toFun d := ⟨d.left, d.right⟩
  invFun d := ⟨d.left, d.right⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' d e := by
    apply SemidirectProduct.ext
    · change d.left * affineDeckIntegerMonodromy
          (orderThreeDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv
          d.right e.left =
        d.left * integerAffineMonodromy
          (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv
          d.right e.left
      congr 1
      have hlinear :
          (orderThreeDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv =
            (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv :=
        congrArg (fun D ↦ D.latticeMap.toAddEquiv)
          A.orderThreeCentralFiberPresentationData_affine_eq.symm
      exact congrArg (fun f ↦ f d.right e.left)
        ((affineDeckIntegerMonodromy_eq_integerAffineMonodromy
          (orderThreeDescendedAffineTorusAutomorphism A.periods)).trans
            (congrArg integerAffineMonodromy hlinear))
    · rfl

@[simp]
public theorem ellipticThreeToCentralBoundaryDeckEquiv_translation (a : Lattice) :
    A.ellipticThreeToCentralBoundaryDeckEquiv
        (Additive.toMul (affineTorusMappingTorusDeckTranslation
          (orderThreeDescendedAffineTorusAutomorphism A.periods) a)) =
      Additive.toMul (canonicalCyclicAffineTranslation
        (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv a) := rfl

@[simp]
public theorem ellipticThreeToCentralBoundaryDeckEquiv_meridian :
    A.ellipticThreeToCentralBoundaryDeckEquiv
        (affineTorusMappingTorusDeckMeridian
          (orderThreeDescendedAffineTorusAutomorphism A.periods)) =
      canonicalCyclicAffineMeridian
        (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv := rfl

public theorem ellipticThreeFillingRelation_map_eq_central_inv :
    A.ellipticThreeToCentralBoundaryDeckEquiv
        A.ellipticThreeBoundaryDeckData.fillingRelation =
      (affineCyclicBoundaryDeckData
        (orderThreeCentralFiberPresentationData A.periods)).fillingRelation⁻¹ := by
  let D := affineCyclicBoundaryDeckData
    (orderThreeCentralFiberPresentationData A.periods)
  let g := D.meridian
  let t := Additive.toMul (D.translation D.twist)
  have hgt : Commute g t := by
    have h := D.conjugate D.twist
    rw [D.twist_fixed] at h
    rw [commute_iff_eq]
    exact mul_inv_eq_iff_eq_mul.mp h
  simp only [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation,
    ellipticThreeBoundaryDeckData, map_mul, map_pow, map_inv,
    ellipticThreeToCentralBoundaryDeckEquiv_translation,
    ellipticThreeToCentralBoundaryDeckEquiv_meridian]
  change g⁻¹ ^ 3 * (Additive.toMul (D.translation (-epsilon)))⁻¹ =
    (g ^ 3 * t⁻¹)⁻¹
  rw [map_neg, toMul_neg]
  exact inverse_meridian_negative_twist_relation g t 3 hgt

/-- The actual order-four boundary deck group identified directly with the central
presentation's deck group. -/
public noncomputable def ellipticFourToCentralBoundaryDeckEquiv :
    OrderFourAffineMappingTorusDeck A.periods ≃*
      CanonicalCyclicAffineBoundaryDeck
        (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv where
  toFun d := ⟨d.left, d.right⟩
  invFun d := ⟨d.left, d.right⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' d e := by
    apply SemidirectProduct.ext
    · change d.left * affineDeckIntegerMonodromy
          (orderFourDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv
          d.right e.left =
        d.left * integerAffineMonodromy
          (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv
          d.right e.left
      congr 1
      have hlinear :
          (orderFourDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv =
            (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv :=
        congrArg (fun D ↦ D.latticeMap.toAddEquiv)
          A.orderFourCentralFiberPresentationData_affine_eq.symm
      exact congrArg (fun f ↦ f d.right e.left)
        ((affineDeckIntegerMonodromy_eq_integerAffineMonodromy
          (orderFourDescendedAffineTorusAutomorphism A.periods)).trans
            (congrArg integerAffineMonodromy hlinear))
    · rfl

@[simp]
public theorem ellipticFourToCentralBoundaryDeckEquiv_translation (a : Lattice) :
    A.ellipticFourToCentralBoundaryDeckEquiv
        (Additive.toMul (affineTorusMappingTorusDeckTranslation
          (orderFourDescendedAffineTorusAutomorphism A.periods) a)) =
      Additive.toMul (canonicalCyclicAffineTranslation
        (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv a) := rfl

@[simp]
public theorem ellipticFourToCentralBoundaryDeckEquiv_meridian :
    A.ellipticFourToCentralBoundaryDeckEquiv
        (affineTorusMappingTorusDeckMeridian
          (orderFourDescendedAffineTorusAutomorphism A.periods)) =
      canonicalCyclicAffineMeridian
        (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv := rfl

public theorem ellipticFourFillingRelation_map_eq_central_inv :
    A.ellipticFourToCentralBoundaryDeckEquiv
        A.ellipticFourBoundaryDeckData.fillingRelation =
      (affineCyclicBoundaryDeckData
        (orderFourCentralFiberPresentationData A.periods)).fillingRelation⁻¹ := by
  let D := affineCyclicBoundaryDeckData
    (orderFourCentralFiberPresentationData A.periods)
  let g := D.meridian
  let t := Additive.toMul (D.translation D.twist)
  have hgt : Commute g t := by
    have h := D.conjugate D.twist
    rw [D.twist_fixed] at h
    rw [commute_iff_eq]
    exact mul_inv_eq_iff_eq_mul.mp h
  simp only [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation,
    ellipticFourBoundaryDeckData, map_mul, map_pow, map_inv,
    ellipticFourToCentralBoundaryDeckEquiv_translation,
    ellipticFourToCentralBoundaryDeckEquiv_meridian]
  change g⁻¹ ^ 4 * (Additive.toMul (D.translation epsilon'))⁻¹ =
    (g ^ 4 * t⁻¹)⁻¹
  rw [show epsilon' = -(-epsilon') by simp, map_neg, toMul_neg]
  exact inverse_meridian_negative_twist_relation g t 4 hgt

public theorem ellipticThreeFillingKernel_map_eq_central :
    Subgroup.map A.ellipticThreeToCentralBoundaryDeckEquiv.toMonoidHom
        A.ellipticThreeBoundaryDeckData.fillingKernel =
      (affineCyclicBoundaryDeckData
        (orderThreeCentralFiberPresentationData A.periods)).fillingKernel := by
  let e := A.ellipticThreeToCentralBoundaryDeckEquiv
  rw [UnwrappedCyclicAffineBoundaryDeckData.fillingKernel,
    UnwrappedCyclicAffineBoundaryDeckData.fillingKernel]
  calc
    Subgroup.map e.toMonoidHom
        (Subgroup.normalClosure {A.ellipticThreeBoundaryDeckData.fillingRelation}) =
      Subgroup.normalClosure
        (e '' {A.ellipticThreeBoundaryDeckData.fillingRelation}) :=
          Subgroup.map_normalClosure _ e.toMonoidHom e.surjective
    _ = Subgroup.normalClosure
        {(affineCyclicBoundaryDeckData
          (orderThreeCentralFiberPresentationData A.periods)).fillingRelation⁻¹} := by
      rw [Set.image_singleton, A.ellipticThreeFillingRelation_map_eq_central_inv]
    _ = _ := normalClosure_singleton_inv _

/-- The corrected actual order-three filling quotient is canonically the established central
filling quotient. -/
public noncomputable def ellipticThreeToCanonicalFillingDeckEquiv :
    A.ellipticThreeBoundaryDeckData.FillingDeck ≃*
      (affineCyclicBoundaryDeckData
        (orderThreeCentralFiberPresentationData A.periods)).FillingDeck := by
  letI : A.ellipticThreeBoundaryDeckData.fillingKernel.Normal :=
    A.ellipticThreeBoundaryDeckData.fillingKernel_normal
  letI : (affineCyclicBoundaryDeckData
      (orderThreeCentralFiberPresentationData A.periods)).fillingKernel.Normal :=
    (affineCyclicBoundaryDeckData
      (orderThreeCentralFiberPresentationData A.periods)).fillingKernel_normal
  exact QuotientGroup.congr
    A.ellipticThreeBoundaryDeckData.fillingKernel
    (affineCyclicBoundaryDeckData
      (orderThreeCentralFiberPresentationData A.periods)).fillingKernel
    A.ellipticThreeToCentralBoundaryDeckEquiv
    A.ellipticThreeFillingKernel_map_eq_central

@[simp]
public theorem ellipticThreeToCanonicalFillingDeckEquiv_fillingDeckMap
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    A.ellipticThreeToCanonicalFillingDeckEquiv
        (A.ellipticThreeBoundaryDeckData.fillingDeckMap g) =
      (affineCyclicBoundaryDeckData
        (orderThreeCentralFiberPresentationData A.periods)).fillingDeckMap
        (A.ellipticThreeToCentralBoundaryDeckEquiv g) := by
  exact QuotientGroup.congr_mk'
    A.ellipticThreeBoundaryDeckData.fillingKernel
    (affineCyclicBoundaryDeckData
      (orderThreeCentralFiberPresentationData A.periods)).fillingKernel
    A.ellipticThreeToCentralBoundaryDeckEquiv
    A.ellipticThreeFillingKernel_map_eq_central g

public theorem ellipticFourFillingKernel_map_eq_central :
    Subgroup.map A.ellipticFourToCentralBoundaryDeckEquiv.toMonoidHom
        A.ellipticFourBoundaryDeckData.fillingKernel =
      (affineCyclicBoundaryDeckData
        (orderFourCentralFiberPresentationData A.periods)).fillingKernel := by
  let e := A.ellipticFourToCentralBoundaryDeckEquiv
  rw [UnwrappedCyclicAffineBoundaryDeckData.fillingKernel,
    UnwrappedCyclicAffineBoundaryDeckData.fillingKernel]
  calc
    Subgroup.map e.toMonoidHom
        (Subgroup.normalClosure {A.ellipticFourBoundaryDeckData.fillingRelation}) =
      Subgroup.normalClosure
        (e '' {A.ellipticFourBoundaryDeckData.fillingRelation}) :=
          Subgroup.map_normalClosure _ e.toMonoidHom e.surjective
    _ = Subgroup.normalClosure
        {(affineCyclicBoundaryDeckData
          (orderFourCentralFiberPresentationData A.periods)).fillingRelation⁻¹} := by
      rw [Set.image_singleton, A.ellipticFourFillingRelation_map_eq_central_inv]
    _ = _ := normalClosure_singleton_inv _

/-- The corrected actual order-four filling quotient is canonically the established central
filling quotient. -/
public noncomputable def ellipticFourToCanonicalFillingDeckEquiv :
    A.ellipticFourBoundaryDeckData.FillingDeck ≃*
      (affineCyclicBoundaryDeckData
        (orderFourCentralFiberPresentationData A.periods)).FillingDeck := by
  letI : A.ellipticFourBoundaryDeckData.fillingKernel.Normal :=
    A.ellipticFourBoundaryDeckData.fillingKernel_normal
  letI : (affineCyclicBoundaryDeckData
      (orderFourCentralFiberPresentationData A.periods)).fillingKernel.Normal :=
    (affineCyclicBoundaryDeckData
      (orderFourCentralFiberPresentationData A.periods)).fillingKernel_normal
  exact QuotientGroup.congr
    A.ellipticFourBoundaryDeckData.fillingKernel
    (affineCyclicBoundaryDeckData
      (orderFourCentralFiberPresentationData A.periods)).fillingKernel
    A.ellipticFourToCentralBoundaryDeckEquiv
    A.ellipticFourFillingKernel_map_eq_central

@[simp]
public theorem ellipticFourToCanonicalFillingDeckEquiv_fillingDeckMap
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    A.ellipticFourToCanonicalFillingDeckEquiv
        (A.ellipticFourBoundaryDeckData.fillingDeckMap g) =
      (affineCyclicBoundaryDeckData
        (orderFourCentralFiberPresentationData A.periods)).fillingDeckMap
        (A.ellipticFourToCentralBoundaryDeckEquiv g) := by
  exact QuotientGroup.congr_mk'
    A.ellipticFourBoundaryDeckData.fillingKernel
    (affineCyclicBoundaryDeckData
      (orderFourCentralFiberPresentationData A.periods)).fillingKernel
    A.ellipticFourToCentralBoundaryDeckEquiv
    A.ellipticFourFillingKernel_map_eq_central g

end SphereSixComplex.Geometry.AnalyticData
