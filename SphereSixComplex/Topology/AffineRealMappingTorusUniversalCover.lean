module

public import SphereSixComplex.Geometry.QuotientTopology
public import SphereSixComplex.Topology.PaperEllipticCollarFundamentalDomainProof
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The real-line cover of a mapping torus

The mapping torus of a homeomorphism `φ` is the orbit quotient of `ℝ × T` by the deck
transformation `(t, x) ↦ (t - k, φ ^ k x)`.  The real coordinate makes this action free and
properly discontinuous independently of the dynamics of `φ`.  Consequently the real mapping
torus quotient map is a covering map.
-/

open Set

namespace SphereSixComplex.CyclicAngularFundamentalDomain

noncomputable section

open Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open Geometry.AnalyticTorusFamily Geometry.GlobalTorusFamily
open SphereSixComplex.LatticeData
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods

variable {T : Type} [TopologicalSpace T]

/-- The integer deck action whose orbit quotient is `RealMappingTorus φ`. -/
@[expose, instance_reducible] public noncomputable def realMappingTorusDeckAction
    (φ : T ≃ₜ T) : MulAction (Multiplicative ℤ) (ℝ × T) where
  smul k p := mappingTorusShift φ (Multiplicative.toAdd k) p
  one_smul p := mappingTorusShift_zero φ p
  mul_smul k l p := by
    change mappingTorusShift φ (Multiplicative.toAdd k + Multiplicative.toAdd l) p =
      mappingTorusShift φ (Multiplicative.toAdd k)
        (mappingTorusShift φ (Multiplicative.toAdd l) p)
    exact mappingTorusShift_add φ (Multiplicative.toAdd k) (Multiplicative.toAdd l) p

public theorem realMappingTorusDeckAction_smul
    (φ : T ≃ₜ T) (k : Multiplicative ℤ) (p : ℝ × T) :
    letI := realMappingTorusDeckAction φ
    k • p = mappingTorusShift φ (Multiplicative.toAdd k) p :=
  rfl

/-- The mapping-torus deck action is free because it translates the real coordinate by an
integer. -/
public theorem realMappingTorusDeckAction_free (φ : T ≃ₜ T) :
    letI := realMappingTorusDeckAction φ
    IsCancelSMul (Multiplicative ℤ) (ℝ × T) := by
  let _ := realMappingTorusDeckAction φ
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro k p hp
  have hfst := congrArg Prod.fst hp
  change p.1 - ((Multiplicative.toAdd k : ℤ) : ℝ) = p.1 at hfst
  have hk : Multiplicative.toAdd k = 0 := by
    exact_mod_cast (sub_eq_self.mp hfst)
  exact Multiplicative.toAdd.injective (by simpa using hk)

/-- Every mapping-torus deck transformation is continuous. -/
public theorem realMappingTorusDeckAction_continuous (φ : T ≃ₜ T) :
    letI := realMappingTorusDeckAction φ
    ContinuousConstSMul (Multiplicative ℤ) (ℝ × T) := by
  let _ := realMappingTorusDeckAction φ
  refine ⟨fun k ↦ ?_⟩
  exact (mappingTorusShift φ (Multiplicative.toAdd k)).continuous

/-- Proper discontinuity follows solely from boundedness of the real-coordinate projections of
compact sets. -/
public theorem realMappingTorusDeckAction_properlyDiscontinuous (φ : T ≃ₜ T) :
    letI := realMappingTorusDeckAction φ
    ProperlyDiscontinuousSMul (Multiplicative ℤ) (ℝ × T) := by
  let _ := realMappingTorusDeckAction φ
  refine ⟨?_⟩
  intro K L hK hL
  have hKreal : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hLreal : IsCompact (Prod.fst '' L) := hL.image continuous_fst
  obtain ⟨aK, haK⟩ := hKreal.bddBelow
  obtain ⟨bK, hbK⟩ := hKreal.bddAbove
  obtain ⟨aL, haL⟩ := hLreal.bddBelow
  obtain ⟨bL, hbL⟩ := hLreal.bddAbove
  have hfinite :
      {k : Multiplicative ℤ |
        Multiplicative.toAdd k ∈ Set.Icc (Int.ceil (aK - bL)) (Int.floor (bK - aL))}.Finite :=
    (Set.finite_Icc (Int.ceil (aK - bL)) (Int.floor (bK - aL))).preimage
      Multiplicative.toAdd.injective.injOn
  apply hfinite.subset
  intro k hk
  rcases hk with ⟨q, ⟨p, hpK, hpq⟩, hqL⟩
  have hpLower : aK ≤ p.1 := haK ⟨p, hpK, rfl⟩
  have hpUpper : p.1 ≤ bK := hbK ⟨p, hpK, rfl⟩
  have hqLower : aL ≤ q.1 := haL ⟨q, hqL, rfl⟩
  have hqUpper : q.1 ≤ bL := hbL ⟨q, hqL, rfl⟩
  have hpqReal := congrArg Prod.fst hpq
  change p.1 - ((Multiplicative.toAdd k : ℤ) : ℝ) = q.1 at hpqReal
  constructor
  · rw [Int.ceil_le]
    linarith
  · rw [Int.le_floor]
    linarith

/-- The explicit real mapping-torus relation is the orbit relation of the deck action. -/
public theorem realMappingTorusSetoid_eq_orbitRel (φ : T ≃ₜ T) :
    letI := realMappingTorusDeckAction φ
    realMappingTorusSetoid φ = MulAction.orbitRel (Multiplicative ℤ) (ℝ × T) := by
  let _ := realMappingTorusDeckAction φ
  apply Setoid.ext
  intro p q
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨Multiplicative.ofAdd (-k), ?_⟩
    change mappingTorusShift φ (-k) (mappingTorusShift φ k p) = p
    rw [← mappingTorusShift_add, neg_add_cancel, mappingTorusShift_zero]
  · rintro ⟨k, hk⟩
    refine ⟨-(Multiplicative.toAdd k), ?_⟩
    change mappingTorusShift φ (Multiplicative.toAdd k) q = p at hk
    rw [← hk, ← mappingTorusShift_add, neg_add_cancel, mappingTorusShift_zero]

/-- The quotient map `ℝ × T → RealMappingTorus φ` is a regular covering with deck group `ℤ`. -/
public theorem realMappingTorusMk_isQuotientCoveringMap
    [T2Space T] [LocallyCompactSpace T] (φ : T ≃ₜ T) :
    letI := realMappingTorusDeckAction φ
    IsQuotientCoveringMap (Quotient.mk (realMappingTorusSetoid φ)) (Multiplicative ℤ) := by
  let _ := realMappingTorusDeckAction φ
  let _ : IsCancelSMul (Multiplicative ℤ) (ℝ × T) :=
    realMappingTorusDeckAction_free φ
  let _ : ContinuousConstSMul (Multiplicative ℤ) (ℝ × T) :=
    realMappingTorusDeckAction_continuous φ
  let _ : ProperlyDiscontinuousSMul (Multiplicative ℤ) (ℝ × T) :=
    realMappingTorusDeckAction_properlyDiscontinuous φ
  rw [realMappingTorusSetoid_eq_orbitRel φ]
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- The real mapping-torus quotient map, viewed only as a covering map. -/
public theorem realMappingTorusMk_isCoveringMap
    [T2Space T] [LocallyCompactSpace T] (φ : T ≃ₜ T) :
    IsCoveringMap (Quotient.mk (realMappingTorusSetoid φ)) := by
  let _ := realMappingTorusDeckAction φ
  exact (realMappingTorusMk_isQuotientCoveringMap φ).isCoveringMap

/-- The same real-line cover, transported to the cylinder presentation `CircleMappingTorus`. -/
@[expose] public def circleMappingTorusRealCoverProjection (φ : T ≃ₜ T) :
    C(ℝ × T, CircleMappingTorus φ) where
  toFun p := realMappingTorusHomeomorph φ
    (Quotient.mk (realMappingTorusSetoid φ) p)
  continuous_toFun :=
    (realMappingTorusHomeomorph φ).continuous.comp continuous_quot_mk

/-- The transported real-line projection is a regular integer covering. -/
public theorem circleMappingTorusRealCoverProjection_isQuotientCoveringMap
    [T2Space T] [LocallyCompactSpace T] (φ : T ≃ₜ T) :
    letI := realMappingTorusDeckAction φ
    IsQuotientCoveringMap (circleMappingTorusRealCoverProjection φ) (Multiplicative ℤ) := by
  let _ := realMappingTorusDeckAction φ
  change IsQuotientCoveringMap
    ((realMappingTorusHomeomorph φ) ∘ Quotient.mk (realMappingTorusSetoid φ))
      (Multiplicative ℤ)
  exact (realMappingTorusMk_isQuotientCoveringMap φ).homeomorph_comp
    (realMappingTorusHomeomorph φ)

/-- The transported real-line projection is a covering map. -/
public theorem circleMappingTorusRealCoverProjection_isCoveringMap
    [T2Space T] [LocallyCompactSpace T] (φ : T ≃ₜ T) :
    IsCoveringMap (circleMappingTorusRealCoverProjection φ) := by
  let _ := realMappingTorusDeckAction φ
  exact (circleMappingTorusRealCoverProjection_isQuotientCoveringMap φ).isCoveringMap

/-- Before dividing the fibre by its period lattice, the natural candidate universal-cover map
to an affine torus mapping torus. -/
@[expose] public def affineTorusMappingTorusLiftProjection
    (p : Parameters) (φ : AdditiveTorus p ≃ₜ AdditiveTorus p) :
    C(ℝ × ComplexTwoSpace, CircleMappingTorus φ) where
  toFun w := circleMappingTorusRealCoverProjection φ
    (w.1, Quotient.mk _ w.2)
  continuous_toFun := (circleMappingTorusRealCoverProjection φ).continuous.comp
    (continuous_fst.prodMk (continuous_quot_mk.comp continuous_snd))

/-- The candidate affine-torus mapping-torus lift is onto. -/
public theorem affineTorusMappingTorusLiftProjection_surjective
  (p : Parameters) (φ : AdditiveTorus p ≃ₜ AdditiveTorus p) :
    Function.Surjective (affineTorusMappingTorusLiftProjection p φ) := by
  intro y
  obtain ⟨w, rfl⟩ := (realMappingTorusHomeomorph φ).surjective y
  induction w using Quotient.inductionOn with
  | _ w =>
    rcases w with ⟨t, x⟩
    induction x using Quotient.inductionOn with
    | _ z => exact ⟨(t, z), rfl⟩

/-- Exact fibre criterion before choosing affine representatives: equality is an integral angular
shift together with equality in the period torus after the corresponding clutching power. -/
public theorem affineTorusMappingTorusLiftProjection_eq_iff
    (p : Parameters) (φ : AdditiveTorus p ≃ₜ AdditiveTorus p)
    (w w' : ℝ × ComplexTwoSpace) :
    affineTorusMappingTorusLiftProjection p φ w =
        affineTorusMappingTorusLiftProjection p φ w' ↔
      ∃ k : ℤ, w'.1 = w.1 - k ∧
        (Quotient.mk _ w'.2 : AdditiveTorus p) =
          (φ ^ k) (Quotient.mk _ w.2) := by
  change realMappingTorusHomeomorph φ
      (Quotient.mk _ (w.1, (Quotient.mk _ w.2 : AdditiveTorus p))) =
    realMappingTorusHomeomorph φ
      (Quotient.mk _ (w'.1, (Quotient.mk _ w'.2 : AdditiveTorus p))) ↔ _
  rw [(realMappingTorusHomeomorph φ).injective.eq_iff,
    realMappingTorusMk_eq_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, congrArg Prod.fst hk, congrArg Prod.snd hk⟩
  · rintro ⟨k, hfst, hsnd⟩
    exact ⟨k, Prod.ext hfst hsnd⟩

/-- Period-lattice translations are deck transformations of the candidate lifted projection. -/
public theorem affineTorusMappingTorusLiftProjection_period
    (p : Parameters) (φ : AdditiveTorus p ≃ₜ AdditiveTorus p)
    (t : ℝ) (z : ComplexTwoSpace) (n : IntegerPeriods) :
  affineTorusMappingTorusLiftProjection p φ (t, periodVector p n + z) =
      affineTorusMappingTorusLiftProjection p φ (t, z) := by
  apply congrArg (realMappingTorusHomeomorph φ)
  symm
  apply Quotient.sound
  refine ⟨0, ?_⟩
  rw [mappingTorusShift_zero]
  apply Prod.ext
  · rfl
  apply Quotient.sound
  change MulAction.orbitRel (PeriodGroup p) ComplexTwoSpace
    (periodVector p n + z) z
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨Multiplicative.ofAdd
    ⟨periodVector p n, ⟨n, rfl⟩⟩, rfl⟩

/-- Any affine lift of the clutching homeomorphism gives the angular deck transformation on the
candidate universal cover. -/
public theorem affineTorusMappingTorusLiftProjection_generator
    (p : Parameters) (φ : AdditiveTorus p ≃ₜ AdditiveTorus p)
    (lift : ComplexTwoSpace ≃+ ComplexTwoSpace) (b : ComplexTwoSpace)
    (hlift : ∀ z, φ (Quotient.mk _ z) = Quotient.mk _ (lift z + b))
    (t : ℝ) (z : ComplexTwoSpace) :
    affineTorusMappingTorusLiftProjection p φ (t - 1, lift z + b) =
      affineTorusMappingTorusLiftProjection p φ (t, z) := by
  apply congrArg (realMappingTorusHomeomorph φ)
  symm
  apply (realMappingTorusMk_eq_iff φ _ _).mpr
  refine ⟨1, ?_⟩
  rw [mappingTorusShift_apply]
  apply Prod.ext
  · norm_num
  · simpa using (hlift z).symm

/-- The affine lift intertwines every integral power of the clutching homeomorphism. -/
public theorem affineTorusClutching_zpow_mk
    (p : Parameters) (φ : AdditiveTorus p ≃ₜ AdditiveTorus p)
    (lift : ComplexTwoSpace ≃+ ComplexTwoSpace) (b : ComplexTwoSpace)
    (hlift : ∀ z, φ (Quotient.mk _ z) = Quotient.mk _ (lift z + b))
    (k : ℤ) (z : ComplexTwoSpace) :
    (φ ^ k) (Quotient.mk _ z) =
      Quotient.mk _ ((Geometry.affineEquiv lift b ^ k) z) := by
  let a := Geometry.affineEquiv lift b
  have hinv (z : ComplexTwoSpace) :
      φ.symm (Quotient.mk _ z) = Quotient.mk _ (a.symm z) := by
    apply φ.injective
    rw [φ.apply_symm_apply, hlift]
    exact congrArg (Quotient.mk _) (a.apply_symm_apply z).symm
  induction k using Int.induction_on generalizing z with
  | zero => simp
  | succ i ih =>
      change (φ ^ (i : ℤ)) (φ (Quotient.mk _ z)) =
        Quotient.mk _ ((a ^ (i : ℤ)) (a z))
      rw [hlift, ih]
      rfl
  | pred i ih =>
      rw [show φ ^ (- (i : ℤ) - 1) = φ ^ (- (i : ℤ)) * φ⁻¹ by
        rw [zpow_sub, zpow_one],
        Homeomorph.mul_apply]
      change (φ ^ (- (i : ℤ))) (φ.symm (Quotient.mk _ z)) = _
      rw [hinv, ih]
      change Quotient.mk _ ((a ^ (- (i : ℤ))) (a.symm z)) =
        Quotient.mk _ ((a ^ (- (i : ℤ) - 1)) z)
      rw [zpow_sub, zpow_one]
      rfl

/-- Two lifted points have the same image exactly when one is obtained from the other by an
integral affine clutching power followed by a period-lattice translation. -/
public theorem affineTorusMappingTorusLiftProjection_eq_iff_affine_period
    (p : Parameters) (φ : AdditiveTorus p ≃ₜ AdditiveTorus p)
    (lift : ComplexTwoSpace ≃+ ComplexTwoSpace) (b : ComplexTwoSpace)
    (hlift : ∀ z, φ (Quotient.mk _ z) = Quotient.mk _ (lift z + b))
    (w w' : ℝ × ComplexTwoSpace) :
    affineTorusMappingTorusLiftProjection p φ w =
        affineTorusMappingTorusLiftProjection p φ w' ↔
      ∃ k : ℤ, ∃ n : IntegerPeriods,
        w'.1 = w.1 - k ∧
          w'.2 = periodVector p n + (Geometry.affineEquiv lift b ^ k) w.2 := by
  rw [affineTorusMappingTorusLiftProjection_eq_iff]
  constructor
  · rintro ⟨k, htime, htorus⟩
    have hquot :
        (Quotient.mk _ w'.2 : AdditiveTorus p) =
          Quotient.mk _ ((Geometry.affineEquiv lift b ^ k) w.2) := by
      rw [← affineTorusClutching_zpow_mk p φ lift b hlift k w.2]
      exact htorus
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hquot
    obtain ⟨g, hg⟩ := hquot
    obtain ⟨n, hn⟩ := g.toAdd.property
    refine ⟨k, n, htime, ?_⟩
    change (g.toAdd : ComplexTwoSpace) +
      (Geometry.affineEquiv lift b ^ k) w.2 = w'.2 at hg
    rw [show periodVector p n = (g.toAdd : ComplexTwoSpace) from hn]
    exact hg.symm
  · rintro ⟨k, n, htime, hspace⟩
    refine ⟨k, htime, ?_⟩
    rw [affineTorusClutching_zpow_mk p φ lift b hlift]
    apply Quotient.sound
    change MulAction.orbitRel (PeriodGroup p) ComplexTwoSpace w'.2
      ((Geometry.affineEquiv lift b ^ k) w.2)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨Multiplicative.ofAdd
      ⟨periodVector p n, ⟨n, rfl⟩⟩, ?_⟩
    exact hspace.symm

/-- Every integral power of the linear lift carries a period vector by the corresponding
integral lattice automorphism. -/
public theorem descendedAffineTorusLift_zpow_period
    (p : Parameters) (D : DescendedAffineTorusAutomorphism p)
    (k : ℤ) (n : IntegerPeriods) :
    (D.lift.toEquiv ^ k) (periodVector p n) =
      periodVector p ((D.latticeMap.toEquiv ^ k) n) := by
  have hinv (n : IntegerPeriods) :
      D.lift.symm (periodVector p n) = periodVector p (D.latticeMap.symm n) := by
    apply D.lift.injective
    rw [D.lift.apply_symm_apply, D.lift_period, D.latticeMap.apply_symm_apply]
  induction k using Int.induction_on generalizing n with
  | zero => simp
  | succ i ih =>
      change (D.lift.toEquiv ^ (i : ℤ)) (D.lift (periodVector p n)) =
        periodVector p ((D.latticeMap.toEquiv ^ (i : ℤ)) (D.latticeMap n))
      rw [D.lift_period, ih]
  | pred i ih =>
      rw [show D.lift.toEquiv ^ (- (i : ℤ) - 1) =
          D.lift.toEquiv ^ (- (i : ℤ)) * D.lift.toEquiv⁻¹ by
        rw [zpow_sub, zpow_one],
        Equiv.Perm.mul_apply]
      change (D.lift.toEquiv ^ (- (i : ℤ))) (D.lift.symm (periodVector p n)) = _
      rw [hinv, ih]
      rw [zpow_sub, zpow_one]
      rfl

/-- Integral powers of an affine equivalence transport a translate by applying the same power of
the linear part to the translating vector. -/
public theorem affineEquiv_zpow_add
    {A : Type*} [AddCommGroup A] (L : A ≃+ A) (b : A)
    (k : ℤ) (x y : A) :
    (Geometry.affineEquiv L b ^ k) (x + y) =
      (L.toEquiv ^ k) x + (Geometry.affineEquiv L b ^ k) y := by
  let a := Geometry.affineEquiv L b
  have hstep (x y : A) : a (x + y) = L x + a y := by
    simp only [a, Geometry.affineEquiv_apply, map_add]
    abel
  have hinv (x y : A) : a.symm (x + y) = L.symm x + a.symm y := by
    change L.symm (x + y - b) = L.symm x + L.symm (y - b)
    rw [map_sub, map_add, map_sub]
    abel
  induction k using Int.induction_on generalizing x y with
  | zero => simp
  | succ i ih =>
      change (a ^ (i : ℤ)) (a (x + y)) =
        (L.toEquiv ^ (i : ℤ)) (L x) + (a ^ (i : ℤ)) (a y)
      rw [hstep, ih]
  | pred i ih =>
      rw [show a ^ (- (i : ℤ) - 1) = a ^ (- (i : ℤ)) * a⁻¹ by
        rw [zpow_sub, zpow_one],
        Equiv.Perm.mul_apply,
        show L.toEquiv ^ (- (i : ℤ) - 1) =
            L.toEquiv ^ (- (i : ℤ)) * L.toEquiv⁻¹ by
          rw [zpow_sub, zpow_one],
        Equiv.Perm.mul_apply]
      change (a ^ (- (i : ℤ))) (a.symm (x + y)) =
        (L.toEquiv ^ (- (i : ℤ))) (L.symm x) +
          (a ^ (- (i : ℤ))) (a.symm y)
      rw [hinv, ih]

/-- Integral powers of a lattice automorphism, packaged as an additive homomorphism into its
automorphism group. -/
public def affineDeckIntegerPowersAddAut
    {Λ : Type*} [AddCommGroup Λ] (A : AddAut Λ) : ℤ →+ AddAut Λ where
  toFun n := n • A
  map_zero' := zero_zsmul A
  map_add' n k := add_zsmul A n k

/-- The angular action on multiplicative lattice translations. -/
public def affineDeckIntegerMonodromy
    {Λ : Type*} [AddCommGroup Λ] (A : AddAut Λ) :
    Multiplicative ℤ →* MulAut (Multiplicative Λ) :=
  (MulAutMultiplicative Λ).symm.toMonoidHom.comp
    (affineDeckIntegerPowersAddAut A).toMultiplicative

/-- The semidirect deck group of an affine torus mapping torus. -/
public abbrev AffineTorusMappingTorusDeck
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p) :=
  Multiplicative IntegerPeriods ⋊[
    affineDeckIntegerMonodromy D.latticeMap.toAddEquiv] Multiplicative ℤ

/-- The lattice-translation embedding in the affine mapping-torus deck group. -/
public def affineTorusMappingTorusDeckTranslation
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p) :
    IntegerPeriods →+ Additive (AffineTorusMappingTorusDeck D) where
  toFun n := Additive.ofMul
    (SemidirectProduct.inl
      (φ := affineDeckIntegerMonodromy D.latticeMap.toAddEquiv)
      (Multiplicative.ofAdd n))
  map_zero' := by
    apply Additive.toMul.injective
    exact (SemidirectProduct.inl
      (φ := affineDeckIntegerMonodromy D.latticeMap.toAddEquiv)).map_one
  map_add' n m := by
    apply Additive.toMul.injective
    exact (SemidirectProduct.inl
      (φ := affineDeckIntegerMonodromy D.latticeMap.toAddEquiv)).map_mul
      (Multiplicative.ofAdd n) (Multiplicative.ofAdd m)

/-- The positive angular meridian in the affine mapping-torus deck group. -/
public def affineTorusMappingTorusDeckMeridian
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p) :
    AffineTorusMappingTorusDeck D :=
  SemidirectProduct.inr (Multiplicative.ofAdd 1)

public theorem affineDeckIntegerMonodromy_apply
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p)
    (k : Multiplicative ℤ) (n : Multiplicative IntegerPeriods) :
    (affineDeckIntegerMonodromy D.latticeMap.toAddEquiv k n).toAdd =
      (D.latticeMap.toEquiv ^ k.toAdd) n.toAdd := by
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
          D.latticeMap.toEquiv ^ (i : ℤ) * D.latticeMap.toEquiv by
        rw [zpow_add_one],
        Equiv.Perm.mul_apply]
      rfl
  | pred i ih =>
      rw [sub_eq_add_neg, add_zsmul, neg_one_zsmul, AddAut.add_apply]
      have hih := ih
        (Multiplicative.ofAdd ((-D.latticeMap.toAddEquiv) n.toAdd))
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

/-- The explicit action of a combined lattice/angular deck element on the affine universal-cover
coordinates. -/
@[expose] public def affineTorusMappingTorusDeckTransform
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p) (b : ComplexTwoSpace)
    (d : AffineTorusMappingTorusDeck D) (w : ℝ × ComplexTwoSpace) :
    ℝ × ComplexTwoSpace :=
  (w.1 - d.right.toAdd,
    periodVector p d.left.toAdd +
      (Geometry.affineEquiv D.lift b ^ d.right.toAdd) w.2)

public theorem affineTorusMappingTorusDeckTransform_one
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p) (b : ComplexTwoSpace)
    (w : ℝ × ComplexTwoSpace) :
    affineTorusMappingTorusDeckTransform D b 1 w = w := by
  apply Prod.ext
  · simp [affineTorusMappingTorusDeckTransform]
  · simp [affineTorusMappingTorusDeckTransform, periodVector_zero]

public theorem affineTorusMappingTorusDeckTransform_mul
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p) (b : ComplexTwoSpace)
    (d e : AffineTorusMappingTorusDeck D) (w : ℝ × ComplexTwoSpace) :
    affineTorusMappingTorusDeckTransform D b (d * e) w =
      affineTorusMappingTorusDeckTransform D b d
        (affineTorusMappingTorusDeckTransform D b e w) := by
  apply Prod.ext
  · change w.1 - ((d.right.toAdd + e.right.toAdd : ℤ) : ℝ) =
      (w.1 - e.right.toAdd) - d.right.toAdd
    push_cast
    ring
  · change periodVector p
          (d.left.toAdd +
            (affineDeckIntegerMonodromy D.latticeMap.toAddEquiv d.right e.left).toAdd) +
        (Geometry.affineEquiv D.lift b ^ (d.right.toAdd + e.right.toAdd)) w.2 =
      periodVector p d.left.toAdd +
        (Geometry.affineEquiv D.lift b ^ d.right.toAdd)
          (periodVector p e.left.toAdd +
            (Geometry.affineEquiv D.lift b ^ e.right.toAdd) w.2)
    rw [periodVector_add, affineDeckIntegerMonodromy_apply,
      affineEquiv_zpow_add,
      descendedAffineTorusLift_zpow_period,
      zpow_add, Equiv.Perm.mul_apply]
    rw [add_assoc]

/-- The combined semidirect deck action on the explicit affine universal-cover coordinates. -/
@[expose, instance_reducible] public noncomputable def affineTorusMappingTorusDeckAction
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p) (b : ComplexTwoSpace) :
    MulAction (AffineTorusMappingTorusDeck D) (ℝ × ComplexTwoSpace) where
  smul d w := affineTorusMappingTorusDeckTransform D b d w
  one_smul := affineTorusMappingTorusDeckTransform_one D b
  mul_smul := affineTorusMappingTorusDeckTransform_mul D b

/-- The embedded lattice generator acts by the corresponding period translation. -/
public theorem affineTorusMappingTorusDeckTranslation_smul
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p) (b : ComplexTwoSpace)
    (n : IntegerPeriods) (w : ℝ × ComplexTwoSpace) :
    letI := affineTorusMappingTorusDeckAction D b
    Additive.toMul (affineTorusMappingTorusDeckTranslation D n) • w =
      (w.1, periodVector p n + w.2) := by
  change affineTorusMappingTorusDeckTransform D b
    (SemidirectProduct.inl
      (φ := affineDeckIntegerMonodromy D.latticeMap.toAddEquiv)
      (Multiplicative.ofAdd n)) w = _
  simp [affineTorusMappingTorusDeckTransform]

/-- The angular meridian acts by one negative real turn and one affine clutching transform. -/
public theorem affineTorusMappingTorusDeckMeridian_smul
    {p : Parameters} (D : DescendedAffineTorusAutomorphism p) (b : ComplexTwoSpace)
    (w : ℝ × ComplexTwoSpace) :
    letI := affineTorusMappingTorusDeckAction D b
    affineTorusMappingTorusDeckMeridian D • w =
      (w.1 - 1, D.lift w.2 + b) := by
  change affineTorusMappingTorusDeckTransform D b
    (SemidirectProduct.inr (Multiplicative.ofAdd 1)) w = _
  simp [affineTorusMappingTorusDeckTransform,
    Geometry.affineEquiv_apply]

/-- Full rank makes the combined lattice/angular action free: the real coordinate detects the
angular exponent, and injectivity of the period map then detects the lattice translation. -/
public theorem affineTorusMappingTorusDeckAction_free
    {p : Parameters} (hfull : FullRank p)
    (D : DescendedAffineTorusAutomorphism p) (b : ComplexTwoSpace) :
    letI := affineTorusMappingTorusDeckAction D b
    IsCancelSMul (AffineTorusMappingTorusDeck D) (ℝ × ComplexTwoSpace) := by
  let _ := affineTorusMappingTorusDeckAction D b
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro d w hd
  have htime := congrArg Prod.fst hd
  change w.1 - ((d.right.toAdd : ℤ) : ℝ) = w.1 at htime
  have hk : d.right.toAdd = 0 := by
    exact_mod_cast (sub_eq_self.mp htime)
  have hright : d.right = 1 := by
    apply Multiplicative.toAdd.injective
    simpa using hk
  have hspace := congrArg Prod.snd hd
  change periodVector p d.left.toAdd +
      (Geometry.affineEquiv D.lift b ^ d.right.toAdd) w.2 = w.2 at hspace
  rw [hk] at hspace
  simp at hspace
  have hp : periodVector p d.left.toAdd = 0 := by
    have hsub := congrArg (fun z ↦ z - w.2) hspace
    simpa using hsub
  have hn : d.left.toAdd = 0 := by
    apply periodHom_injective hfull
    change periodVector p d.left.toAdd = periodVector p 0
    simpa using hp
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    simpa using hn
  · exact hright

/-- The affine mapping-torus projection is invariant under every combined semidirect deck
transformation. -/
public theorem affineTorusMappingTorusLiftProjection_deckTransform
    (p : Parameters) (φ : AdditiveTorus p ≃ₜ AdditiveTorus p)
    (D : DescendedAffineTorusAutomorphism p) (b : ComplexTwoSpace)
    (hlift : ∀ z, φ (Quotient.mk _ z) = Quotient.mk _ (D.lift z + b))
    (d : AffineTorusMappingTorusDeck D) (w : ℝ × ComplexTwoSpace) :
    affineTorusMappingTorusLiftProjection p φ
        (affineTorusMappingTorusDeckTransform D b d w) =
      affineTorusMappingTorusLiftProjection p φ w := by
  symm
  apply (affineTorusMappingTorusLiftProjection_eq_iff_affine_period
    p φ D.lift b hlift w (affineTorusMappingTorusDeckTransform D b d w)).mpr
  exact ⟨d.right.toAdd, d.left.toAdd, rfl, rfl⟩

/-- The exact fibres of the affine projection are precisely the orbits of the combined
semidirect deck transformations. -/
public theorem affineTorusMappingTorusLiftProjection_eq_iff_exists_deckTransform
    (p : Parameters) (φ : AdditiveTorus p ≃ₜ AdditiveTorus p)
    (D : DescendedAffineTorusAutomorphism p) (b : ComplexTwoSpace)
    (hlift : ∀ z, φ (Quotient.mk _ z) = Quotient.mk _ (D.lift z + b))
    (w w' : ℝ × ComplexTwoSpace) :
    affineTorusMappingTorusLiftProjection p φ w =
        affineTorusMappingTorusLiftProjection p φ w' ↔
      ∃ d : AffineTorusMappingTorusDeck D,
        affineTorusMappingTorusDeckTransform D b d w = w' := by
  rw [affineTorusMappingTorusLiftProjection_eq_iff_affine_period
    p φ D.lift b hlift]
  constructor
  · rintro ⟨k, n, htime, hspace⟩
    refine ⟨⟨Multiplicative.ofAdd n, Multiplicative.ofAdd k⟩, ?_⟩
    exact Prod.ext htime.symm hspace.symm
  · rintro ⟨d, hd⟩
    exact ⟨d.right.toAdd, d.left.toAdd,
      (congrArg Prod.fst hd).symm, (congrArg Prod.snd hd).symm⟩

/-- Reformulation of the exact fibre criterion as the orbit relation of the combined action. -/
public theorem affineTorusMappingTorusLiftProjection_eq_iff_orbitRel
    (p : Parameters) (φ : AdditiveTorus p ≃ₜ AdditiveTorus p)
    (D : DescendedAffineTorusAutomorphism p) (b : ComplexTwoSpace)
    (hlift : ∀ z, φ (Quotient.mk _ z) = Quotient.mk _ (D.lift z + b))
    (w w' : ℝ × ComplexTwoSpace) :
    letI := affineTorusMappingTorusDeckAction D b
    affineTorusMappingTorusLiftProjection p φ w =
        affineTorusMappingTorusLiftProjection p φ w' ↔
      MulAction.orbitRel (AffineTorusMappingTorusDeck D)
        (ℝ × ComplexTwoSpace) w w' := by
  let _ := affineTorusMappingTorusDeckAction D b
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · intro h
    obtain ⟨d, hd⟩ :=
      (affineTorusMappingTorusLiftProjection_eq_iff_exists_deckTransform
        p φ D b hlift w' w).mp h.symm
    exact ⟨d, hd⟩
  · rintro ⟨d, hd⟩
    rw [← hd]
    exact affineTorusMappingTorusLiftProjection_deckTransform
      p φ D b hlift d w'

section EllipticSpecializations

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- The explicit simply connected source map for the order-three affine mapping torus. -/
@[expose] public def orderThreeAffineMappingTorusLiftProjection :
    C(ℝ × ComplexTwoSpace,
      CircleMappingTorus (Geometry.orderThreeAffineClutchingHomeomorph F)) :=
  affineTorusMappingTorusLiftProjection (parameterMap F U.zOne).1
    (Geometry.orderThreeAffineClutchingHomeomorph F)

/-- The explicit simply connected source map for the order-four affine mapping torus. -/
@[expose] public def orderFourAffineMappingTorusLiftProjection :
    C(ℝ × ComplexTwoSpace,
      CircleMappingTorus (Geometry.orderFourAffineClutchingHomeomorph F)) :=
  affineTorusMappingTorusLiftProjection (parameterMap F U.zTwo).1
    (Geometry.orderFourAffineClutchingHomeomorph F)

public theorem orderThreeAffineClutching_lift (z : ComplexTwoSpace) :
    Geometry.orderThreeAffineClutchingHomeomorph F (Quotient.mk _ z) =
      Quotient.mk _
        ((orderThreeDescendedAffineTorusAutomorphism F).lift z +
          (3 : ℂ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon) := by
  rw [Geometry.orderThreeAffineClutchingHomeomorph_apply,
    (orderThreeDescendedAffineTorusAutomorphism F).map_mk]
  rw [show (orderThreeDescendedAffineTorusAutomorphism F).translation =
      (Quotient.mk _ ((3 : ℂ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon) :
        AdditiveTorus (parameterMap F U.zOne).1) by
      change orderThreeTranslation (parameterMap F U.zOne).1 = _
      rw [orderThreeTranslation.eq_def, additiveTorusProjection.eq_def]]
  rw [← additiveTorus_mk_add]

public theorem orderFourAffineClutching_lift (z : ComplexTwoSpace) :
    Geometry.orderFourAffineClutchingHomeomorph F (Quotient.mk _ z) =
      Quotient.mk _
        ((orderFourDescendedAffineTorusAutomorphism F).lift z +
          (4 : ℂ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')) := by
  rw [Geometry.orderFourAffineClutchingHomeomorph_apply,
    (orderFourDescendedAffineTorusAutomorphism F).map_mk]
  rw [show (orderFourDescendedAffineTorusAutomorphism F).translation =
      (Quotient.mk _ ((4 : ℂ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')) :
        AdditiveTorus (parameterMap F U.zTwo).1) by
      change orderFourTranslation (parameterMap F U.zTwo).1 = _
      rw [orderFourTranslation.eq_def, additiveTorusProjection.eq_def]]
  rw [← additiveTorus_mk_add]

/-- The explicit combined lattice/angular deck group for the order-three affine mapping torus. -/
public abbrev OrderThreeAffineMappingTorusDeck :=
  AffineTorusMappingTorusDeck (orderThreeDescendedAffineTorusAutomorphism F)

/-- The explicit combined lattice/angular deck group for the order-four affine mapping torus. -/
public abbrev OrderFourAffineMappingTorusDeck :=
  AffineTorusMappingTorusDeck (orderFourDescendedAffineTorusAutomorphism F)

/-- The order-three semidirect deck action on `ℝ × ℂ²`. -/
@[expose, instance_reducible] public noncomputable def orderThreeAffineMappingTorusDeckAction :
    MulAction (OrderThreeAffineMappingTorusDeck F) (ℝ × ComplexTwoSpace) :=
  affineTorusMappingTorusDeckAction
    (orderThreeDescendedAffineTorusAutomorphism F)
    ((3 : ℂ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon)

/-- The order-four semidirect deck action on `ℝ × ℂ²`. -/
@[expose, instance_reducible] public noncomputable def orderFourAffineMappingTorusDeckAction :
    MulAction (OrderFourAffineMappingTorusDeck F) (ℝ × ComplexTwoSpace) :=
  affineTorusMappingTorusDeckAction
    (orderFourDescendedAffineTorusAutomorphism F)
    ((4 : ℂ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon'))

/-- Exact fibres of the order-three affine mapping-torus projection. -/
public theorem orderThreeAffineMappingTorusLiftProjection_eq_iff
    (w w' : ℝ × ComplexTwoSpace) :
    orderThreeAffineMappingTorusLiftProjection F w =
        orderThreeAffineMappingTorusLiftProjection F w' ↔
      ∃ k : ℤ, ∃ n : IntegerPeriods,
        w'.1 = w.1 - k ∧
          w'.2 = periodVector (parameterMap F U.zOne).1 n +
            (Geometry.affineEquiv
                (orderThreeDescendedAffineTorusAutomorphism F).lift
                ((3 : ℂ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon) ^ k) w.2 :=
  affineTorusMappingTorusLiftProjection_eq_iff_affine_period _ _ _ _
    (orderThreeAffineClutching_lift F) w w'

/-- Exact fibres of the order-four affine mapping-torus projection. -/
public theorem orderFourAffineMappingTorusLiftProjection_eq_iff
    (w w' : ℝ × ComplexTwoSpace) :
    orderFourAffineMappingTorusLiftProjection F w =
        orderFourAffineMappingTorusLiftProjection F w' ↔
      ∃ k : ℤ, ∃ n : IntegerPeriods,
        w'.1 = w.1 - k ∧
          w'.2 = periodVector (parameterMap F U.zTwo).1 n +
            (Geometry.affineEquiv
                (orderFourDescendedAffineTorusAutomorphism F).lift
                ((4 : ℂ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')) ^ k) w.2 :=
  affineTorusMappingTorusLiftProjection_eq_iff_affine_period _ _ _ _
    (orderFourAffineClutching_lift F) w w'

/-- The fibres of the order-three universal-cover candidate are exactly the combined semidirect
deck orbits. -/
public theorem orderThreeAffineMappingTorusLiftProjection_eq_iff_orbitRel
    (w w' : ℝ × ComplexTwoSpace) :
    letI := orderThreeAffineMappingTorusDeckAction F
    orderThreeAffineMappingTorusLiftProjection F w =
        orderThreeAffineMappingTorusLiftProjection F w' ↔
      MulAction.orbitRel (OrderThreeAffineMappingTorusDeck F)
        (ℝ × ComplexTwoSpace) w w' :=
  affineTorusMappingTorusLiftProjection_eq_iff_orbitRel _ _ _ _
    (orderThreeAffineClutching_lift F) w w'

/-- The fibres of the order-four universal-cover candidate are exactly the combined semidirect
deck orbits. -/
public theorem orderFourAffineMappingTorusLiftProjection_eq_iff_orbitRel
    (w w' : ℝ × ComplexTwoSpace) :
    letI := orderFourAffineMappingTorusDeckAction F
    orderFourAffineMappingTorusLiftProjection F w =
        orderFourAffineMappingTorusLiftProjection F w' ↔
      MulAction.orbitRel (OrderFourAffineMappingTorusDeck F)
        (ℝ × ComplexTwoSpace) w w' :=
  affineTorusMappingTorusLiftProjection_eq_iff_orbitRel _ _ _ _
    (orderFourAffineClutching_lift F) w w'

/-- The lifted order-three affine generator is a deck transformation of the explicit source
map. -/
public theorem orderThreeAffineMappingTorusLiftProjection_generator
    (t : ℝ) (z : ComplexTwoSpace) :
    orderThreeAffineMappingTorusLiftProjection F
        (t - 1, (orderThreeDescendedAffineTorusAutomorphism F).lift z +
          (3 : ℂ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon) =
      orderThreeAffineMappingTorusLiftProjection F (t, z) :=
  affineTorusMappingTorusLiftProjection_generator _ _ _ _
    (orderThreeAffineClutching_lift F) t z

/-- The lifted order-four affine generator is a deck transformation of the explicit source map. -/
public theorem orderFourAffineMappingTorusLiftProjection_generator
    (t : ℝ) (z : ComplexTwoSpace) :
    orderFourAffineMappingTorusLiftProjection F
        (t - 1, (orderFourDescendedAffineTorusAutomorphism F).lift z +
          (4 : ℂ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')) =
      orderFourAffineMappingTorusLiftProjection F (t, z) :=
  affineTorusMappingTorusLiftProjection_generator _ _ _ _
    (orderFourAffineClutching_lift F) t z

end EllipticSpecializations

/-- The source of the candidate affine-torus mapping-torus universal cover is simply connected. -/
public theorem affineTorusMappingTorusLiftSource_simplyConnected :
    SimplyConnectedSpace (ℝ × ComplexTwoSpace) := by
  infer_instance

/-- For a contractible fibre, the explicit total space of the real mapping-torus cover is simply
connected. -/
public theorem realMappingTorusCoverSource_simplyConnected [ContractibleSpace T] :
    SimplyConnectedSpace (ℝ × T) := by
  infer_instance

/-- Adding the open radial collar coordinate preserves simple connectedness of the explicit
covering space. -/
public theorem radialRealMappingTorusCoverSource_simplyConnected
    [ContractibleSpace T] {r : ℝ} (hr : 0 < r) :
    SimplyConnectedSpace (RadialInterval r × ℝ × T) := by
  let _ : ContractibleSpace (RadialInterval r) :=
    (convex_Ioo (0 : ℝ) r).contractibleSpace (Set.nonempty_Ioo.mpr hr)
  infer_instance

end

end SphereSixComplex.CyclicAngularFundamentalDomain
