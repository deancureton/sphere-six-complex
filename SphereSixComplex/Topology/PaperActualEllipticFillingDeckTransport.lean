module

public import SphereSixComplex.Topology.PaperEllipticFillingDeckSignAudit
public import SphereSixComplex.Topology.PaperEllipticFillingRealPeriodCoverTransport
public import SphereSixComplex.Topology.PaperAffineCyclicQuotientCovering
public import SphereSixComplex.Topology.PaperMultipleFiberAffineDeckAction

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods
open SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
open SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.EstablishedAffineCyclicQuotientHomology
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction

variable (A : PaperAnalyticData)

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

/-- The mapping-torus deck presentation and the canonical cyclic-affine presentation use the
same semidirect product, up to their separately packaged integer-power actions. -/
public noncomputable def actualToCanonicalBoundaryDeckEquiv
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p) :
    AffineTorusMappingTorusDeck D ≃*
      CanonicalCyclicAffineBoundaryDeck D.latticeMap.toAddEquiv where
  toFun d := ⟨d.left, d.right⟩
  invFun d := ⟨d.left, d.right⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' d e := by
    apply SemidirectProduct.ext
    · change d.left *
        affineDeckIntegerMonodromy D.latticeMap.toAddEquiv d.right e.left =
          d.left * integerAffineMonodromy D.latticeMap.toAddEquiv d.right e.left
      congr 1
      exact congrArg (fun f ↦ f d.right e.left)
        (affineDeckIntegerMonodromy_eq_integerAffineMonodromy D)
    · rfl

public noncomputable def actualToCanonicalBoundaryDeckEquivOfEq
    {p : Parameters} (D E : DescendedAffineTorusAutomorphism p) (h : D = E) :
    AffineTorusMappingTorusDeck D ≃*
      CanonicalCyclicAffineBoundaryDeck E.latticeMap.toAddEquiv := by
  subst E
  exact actualToCanonicalBoundaryDeckEquiv D

@[simp]
public theorem actualToCanonicalBoundaryDeckEquiv_translation
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p) (a : Lattice) :
    actualToCanonicalBoundaryDeckEquiv D
        (Additive.toMul (affineTorusMappingTorusDeckTranslation D a)) =
      Additive.toMul (canonicalCyclicAffineTranslation D.latticeMap.toAddEquiv a) := rfl

@[simp]
public theorem actualToCanonicalBoundaryDeckEquiv_meridian
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p) :
    actualToCanonicalBoundaryDeckEquiv D
        (affineTorusMappingTorusDeckMeridian D) =
      canonicalCyclicAffineMeridian D.latticeMap.toAddEquiv := rfl

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

/-- Under the canonical deck-group identification, the corrected actual order-three filling
relation is the inverse of the positive-meridian canonical filling relation. -/
public theorem orderThreeActualFillingRelation_map_eq_canonical_inv :
    actualToCanonicalBoundaryDeckEquiv
        (orderThreeDescendedAffineTorusAutomorphism A.periods)
        A.orderThreeActualEllipticBoundaryDeckData.fillingRelation =
      (affineCyclicBoundaryDeckData
        (orderThreeCentralFiberPresentationData A.periods)).fillingRelation⁻¹ := by
  let g := canonicalCyclicAffineMeridian
    (orderThreeDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv
  let t := Additive.toMul (canonicalCyclicAffineTranslation
    (orderThreeDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv epsilon)
  have hgt : Commute g t := by
    have hfix : (orderThreeDescendedAffineTorusAutomorphism A.periods).latticeMap epsilon =
        epsilon := by
      exact affineLatticeMap_twist (orderThreeCentralFiberPresentationData A.periods)
    have h := canonicalCyclicAffine_conjugate
      (orderThreeDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv epsilon
    change g * t * g⁻¹ = Additive.toMul
      (canonicalCyclicAffineTranslation
        (orderThreeDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv
        ((orderThreeDescendedAffineTorusAutomorphism A.periods).latticeMap epsilon)) at h
    rw [hfix] at h
    rw [commute_iff_eq]
    exact mul_inv_eq_iff_eq_mul.mp h
  simp only [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation,
    orderThreeActualEllipticBoundaryDeckData, affineCyclicBoundaryDeckData,
    orderThreeCentralFiberPresentationData, map_mul, map_pow, map_inv,
    actualToCanonicalBoundaryDeckEquiv_translation,
    actualToCanonicalBoundaryDeckEquiv_meridian]
  change g⁻¹ ^ 3 *
      (Additive.toMul (canonicalCyclicAffineTranslation
        (orderThreeDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv
        (-epsilon)))⁻¹ =
    (g ^ 3 * t⁻¹)⁻¹
  rw [map_neg, toMul_neg]
  exact inverse_meridian_negative_twist_relation g t 3 hgt

/-- Under the canonical deck-group identification, the corrected actual order-four filling
relation is the inverse of the positive-meridian canonical filling relation. -/
public theorem orderFourActualFillingRelation_map_eq_canonical_inv :
    actualToCanonicalBoundaryDeckEquiv
        (orderFourDescendedAffineTorusAutomorphism A.periods)
        A.orderFourActualEllipticBoundaryDeckData.fillingRelation =
      (affineCyclicBoundaryDeckData
        (orderFourCentralFiberPresentationData A.periods)).fillingRelation⁻¹ := by
  let g := canonicalCyclicAffineMeridian
    (orderFourDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv
  let t := Additive.toMul (canonicalCyclicAffineTranslation
    (orderFourDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv (-epsilon'))
  have hgt : Commute g t := by
    have hfix : (orderFourDescendedAffineTorusAutomorphism A.periods).latticeMap (-epsilon') =
        -epsilon' := by
      exact affineLatticeMap_twist (orderFourCentralFiberPresentationData A.periods)
    have h := canonicalCyclicAffine_conjugate
      (orderFourDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv (-epsilon')
    change g * t * g⁻¹ = Additive.toMul
      (canonicalCyclicAffineTranslation
        (orderFourDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv
        ((orderFourDescendedAffineTorusAutomorphism A.periods).latticeMap (-epsilon'))) at h
    rw [hfix] at h
    rw [commute_iff_eq]
    exact mul_inv_eq_iff_eq_mul.mp h
  simp only [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation,
    orderFourActualEllipticBoundaryDeckData, affineCyclicBoundaryDeckData,
    orderFourCentralFiberPresentationData, map_mul, map_pow, map_inv,
    actualToCanonicalBoundaryDeckEquiv_translation,
    actualToCanonicalBoundaryDeckEquiv_meridian]
  change g⁻¹ ^ 4 *
      (Additive.toMul (canonicalCyclicAffineTranslation
        (orderFourDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv
        epsilon'))⁻¹ =
    (g ^ 4 * t⁻¹)⁻¹
  rw [show epsilon' = -(-epsilon') by simp, map_neg, toMul_neg]
  exact inverse_meridian_negative_twist_relation g t 4 hgt

/-- The actual order-three boundary deck group identified directly with the central
presentation's deck group. -/
public noncomputable def orderThreeActualToCentralBoundaryDeckEquiv :
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
public theorem orderThreeActualToCentralBoundaryDeckEquiv_translation (a : Lattice) :
    A.orderThreeActualToCentralBoundaryDeckEquiv
        (Additive.toMul (affineTorusMappingTorusDeckTranslation
          (orderThreeDescendedAffineTorusAutomorphism A.periods) a)) =
      Additive.toMul (canonicalCyclicAffineTranslation
        (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv a) := rfl

@[simp]
public theorem orderThreeActualToCentralBoundaryDeckEquiv_meridian :
    A.orderThreeActualToCentralBoundaryDeckEquiv
        (affineTorusMappingTorusDeckMeridian
          (orderThreeDescendedAffineTorusAutomorphism A.periods)) =
      canonicalCyclicAffineMeridian
        (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv := rfl

public theorem orderThreeActualFillingRelation_map_eq_central_inv :
    A.orderThreeActualToCentralBoundaryDeckEquiv
        A.orderThreeActualEllipticBoundaryDeckData.fillingRelation =
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
    orderThreeActualEllipticBoundaryDeckData, map_mul, map_pow, map_inv,
    orderThreeActualToCentralBoundaryDeckEquiv_translation,
    orderThreeActualToCentralBoundaryDeckEquiv_meridian]
  change g⁻¹ ^ 3 * (Additive.toMul (D.translation (-epsilon)))⁻¹ =
    (g ^ 3 * t⁻¹)⁻¹
  rw [map_neg, toMul_neg]
  exact inverse_meridian_negative_twist_relation g t 3 hgt

/-- The actual order-four boundary deck group identified directly with the central
presentation's deck group. -/
public noncomputable def orderFourActualToCentralBoundaryDeckEquiv :
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
public theorem orderFourActualToCentralBoundaryDeckEquiv_translation (a : Lattice) :
    A.orderFourActualToCentralBoundaryDeckEquiv
        (Additive.toMul (affineTorusMappingTorusDeckTranslation
          (orderFourDescendedAffineTorusAutomorphism A.periods) a)) =
      Additive.toMul (canonicalCyclicAffineTranslation
        (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv a) := rfl

@[simp]
public theorem orderFourActualToCentralBoundaryDeckEquiv_meridian :
    A.orderFourActualToCentralBoundaryDeckEquiv
        (affineTorusMappingTorusDeckMeridian
          (orderFourDescendedAffineTorusAutomorphism A.periods)) =
      canonicalCyclicAffineMeridian
        (orderFourCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv := rfl

public theorem orderFourActualFillingRelation_map_eq_central_inv :
    A.orderFourActualToCentralBoundaryDeckEquiv
        A.orderFourActualEllipticBoundaryDeckData.fillingRelation =
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
    orderFourActualEllipticBoundaryDeckData, map_mul, map_pow, map_inv,
    orderFourActualToCentralBoundaryDeckEquiv_translation,
    orderFourActualToCentralBoundaryDeckEquiv_meridian]
  change g⁻¹ ^ 4 * (Additive.toMul (D.translation epsilon'))⁻¹ =
    (g ^ 4 * t⁻¹)⁻¹
  rw [show epsilon' = -(-epsilon') by simp, map_neg, toMul_neg]
  exact inverse_meridian_negative_twist_relation g t 4 hgt

public theorem orderThreeActualFillingKernel_map_eq_central :
    Subgroup.map A.orderThreeActualToCentralBoundaryDeckEquiv.toMonoidHom
        A.orderThreeActualEllipticBoundaryDeckData.fillingKernel =
      (affineCyclicBoundaryDeckData
        (orderThreeCentralFiberPresentationData A.periods)).fillingKernel := by
  let e := A.orderThreeActualToCentralBoundaryDeckEquiv
  rw [UnwrappedCyclicAffineBoundaryDeckData.fillingKernel,
    UnwrappedCyclicAffineBoundaryDeckData.fillingKernel]
  calc
    Subgroup.map e.toMonoidHom
        (Subgroup.normalClosure {A.orderThreeActualEllipticBoundaryDeckData.fillingRelation}) =
      Subgroup.normalClosure
        (e '' {A.orderThreeActualEllipticBoundaryDeckData.fillingRelation}) :=
          Subgroup.map_normalClosure _ e.toMonoidHom e.surjective
    _ = Subgroup.normalClosure
        {(affineCyclicBoundaryDeckData
          (orderThreeCentralFiberPresentationData A.periods)).fillingRelation⁻¹} := by
      rw [Set.image_singleton, A.orderThreeActualFillingRelation_map_eq_central_inv]
    _ = _ := normalClosure_singleton_inv _

/-- The corrected actual order-three filling quotient is canonically the established central
filling quotient. -/
public noncomputable def orderThreeActualToCanonicalFillingDeckEquiv :
    A.orderThreeActualEllipticBoundaryDeckData.FillingDeck ≃*
      (affineCyclicBoundaryDeckData
        (orderThreeCentralFiberPresentationData A.periods)).FillingDeck := by
  letI : A.orderThreeActualEllipticBoundaryDeckData.fillingKernel.Normal :=
    A.orderThreeActualEllipticBoundaryDeckData.fillingKernel_normal
  letI : (affineCyclicBoundaryDeckData
      (orderThreeCentralFiberPresentationData A.periods)).fillingKernel.Normal :=
    (affineCyclicBoundaryDeckData
      (orderThreeCentralFiberPresentationData A.periods)).fillingKernel_normal
  exact QuotientGroup.congr
    A.orderThreeActualEllipticBoundaryDeckData.fillingKernel
    (affineCyclicBoundaryDeckData
      (orderThreeCentralFiberPresentationData A.periods)).fillingKernel
    A.orderThreeActualToCentralBoundaryDeckEquiv
    A.orderThreeActualFillingKernel_map_eq_central

@[simp]
public theorem orderThreeActualToCanonicalFillingDeckEquiv_fillingDeckMap
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    A.orderThreeActualToCanonicalFillingDeckEquiv
        (A.orderThreeActualEllipticBoundaryDeckData.fillingDeckMap g) =
      (affineCyclicBoundaryDeckData
        (orderThreeCentralFiberPresentationData A.periods)).fillingDeckMap
        (A.orderThreeActualToCentralBoundaryDeckEquiv g) := by
  exact QuotientGroup.congr_mk'
    A.orderThreeActualEllipticBoundaryDeckData.fillingKernel
    (affineCyclicBoundaryDeckData
      (orderThreeCentralFiberPresentationData A.periods)).fillingKernel
    A.orderThreeActualToCentralBoundaryDeckEquiv
    A.orderThreeActualFillingKernel_map_eq_central g

public theorem orderFourActualFillingKernel_map_eq_central :
    Subgroup.map A.orderFourActualToCentralBoundaryDeckEquiv.toMonoidHom
        A.orderFourActualEllipticBoundaryDeckData.fillingKernel =
      (affineCyclicBoundaryDeckData
        (orderFourCentralFiberPresentationData A.periods)).fillingKernel := by
  let e := A.orderFourActualToCentralBoundaryDeckEquiv
  rw [UnwrappedCyclicAffineBoundaryDeckData.fillingKernel,
    UnwrappedCyclicAffineBoundaryDeckData.fillingKernel]
  calc
    Subgroup.map e.toMonoidHom
        (Subgroup.normalClosure {A.orderFourActualEllipticBoundaryDeckData.fillingRelation}) =
      Subgroup.normalClosure
        (e '' {A.orderFourActualEllipticBoundaryDeckData.fillingRelation}) :=
          Subgroup.map_normalClosure _ e.toMonoidHom e.surjective
    _ = Subgroup.normalClosure
        {(affineCyclicBoundaryDeckData
          (orderFourCentralFiberPresentationData A.periods)).fillingRelation⁻¹} := by
      rw [Set.image_singleton, A.orderFourActualFillingRelation_map_eq_central_inv]
    _ = _ := normalClosure_singleton_inv _

/-- The corrected actual order-four filling quotient is canonically the established central
filling quotient. -/
public noncomputable def orderFourActualToCanonicalFillingDeckEquiv :
    A.orderFourActualEllipticBoundaryDeckData.FillingDeck ≃*
      (affineCyclicBoundaryDeckData
        (orderFourCentralFiberPresentationData A.periods)).FillingDeck := by
  letI : A.orderFourActualEllipticBoundaryDeckData.fillingKernel.Normal :=
    A.orderFourActualEllipticBoundaryDeckData.fillingKernel_normal
  letI : (affineCyclicBoundaryDeckData
      (orderFourCentralFiberPresentationData A.periods)).fillingKernel.Normal :=
    (affineCyclicBoundaryDeckData
      (orderFourCentralFiberPresentationData A.periods)).fillingKernel_normal
  exact QuotientGroup.congr
    A.orderFourActualEllipticBoundaryDeckData.fillingKernel
    (affineCyclicBoundaryDeckData
      (orderFourCentralFiberPresentationData A.periods)).fillingKernel
    A.orderFourActualToCentralBoundaryDeckEquiv
    A.orderFourActualFillingKernel_map_eq_central

@[simp]
public theorem orderFourActualToCanonicalFillingDeckEquiv_fillingDeckMap
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    A.orderFourActualToCanonicalFillingDeckEquiv
        (A.orderFourActualEllipticBoundaryDeckData.fillingDeckMap g) =
      (affineCyclicBoundaryDeckData
        (orderFourCentralFiberPresentationData A.periods)).fillingDeckMap
        (A.orderFourActualToCentralBoundaryDeckEquiv g) := by
  exact QuotientGroup.congr_mk'
    A.orderFourActualEllipticBoundaryDeckData.fillingKernel
    (affineCyclicBoundaryDeckData
      (orderFourCentralFiberPresentationData A.periods)).fillingKernel
    A.orderFourActualToCentralBoundaryDeckEquiv
    A.orderFourActualFillingKernel_map_eq_central g

end SphereSixComplex.Geometry.PaperAnalyticData
