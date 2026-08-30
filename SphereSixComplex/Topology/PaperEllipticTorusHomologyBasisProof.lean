module

public import SphereSixComplex.Topology.WangHomologyPresentationProof
public import SphereSixComplex.Topology.ConnectedMayerVietorisDegreeZero
public import SphereSixComplex.Topology.StandardCircleHomologyLiftDegree
public import SphereSixComplex.Geometry.EllipticFamilySpecialization
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# The standard integral homology bases of a full-rank period torus

This file computes the integral singular homology of a real four-torus in degrees one and two,
and identifies a full-rank complex two-torus with the standard four-torus.
-/

@[expose] public section

noncomputable section

-- The two transport naturality statements below are defs because they are propositions whose
-- proofs unfold the transported coordinate definitions.
set_option linter.defProp false

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex

namespace StandardTorusHomology

/-! ## Splitting a short exact sequence with free quotient -/

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- A right inverse to a surjection onto a finite free group, built from chosen lifts of the
standard basis vectors. -/
public def freeSection {m : ℕ} (q : B →+ (Fin m → ℤ)) (hq : Function.Surjective q) :
    (Fin m → ℤ) →+ B where
  toFun c := ∑ i, c i • (hq (Pi.single i 1)).choose
  map_zero' := by simp
  map_add' c d := by
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib

public theorem freeSection_spec {m : ℕ} (q : B →+ (Fin m → ℤ)) (hq : Function.Surjective q)
    (c : Fin m → ℤ) : q (freeSection q hq c) = c := by
  show q (∑ i, c i • (hq (Pi.single i 1)).choose) = c
  rw [map_sum]
  funext j
  rw [Finset.sum_apply]
  have hstep : ∀ i : Fin m, (q (c i • (hq (Pi.single i 1)).choose)) j =
      if i = j then c j else 0 := by
    intro i
    rw [map_zsmul, (hq (Pi.single i 1)).choose_spec]
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  rw [Finset.sum_congr rfl fun i _ ↦ hstep i]
  simp

/-- A short exact sequence of abelian groups with finite free quotient splits. -/
public def splitOfFreeQuotient {m : ℕ} (i : A →+ B) (q : B →+ (Fin m → ℤ))
    (hi : Function.Injective i) (hq : Function.Surjective q) (hex : Function.Exact i q) :
    B ≃+ A × (Fin m → ℤ) := by
  classical
  let s := freeSection q hq
  let f : A × (Fin m → ℤ) →+ B :=
    { toFun := fun p ↦ i p.1 + s p.2
      map_zero' := by simp
      map_add' := fun p₁ p₂ ↦ by
        show i (p₁.1 + p₂.1) + s (p₁.2 + p₂.2) =
          (i p₁.1 + s p₁.2) + (i p₂.1 + s p₂.2)
        rw [map_add, map_add]
        abel }
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, c⟩ h
    have hqf : q (i a + s c) = 0 := by rw [show i a + s c = f (a, c) from rfl, h, map_zero]
    rw [map_add, hex.apply_apply_eq_zero, zero_add, freeSection_spec] at hqf
    subst hqf
    have h' : i a + s 0 = 0 := h
    rw [map_zero, add_zero] at h'
    have ha : a = 0 := hi (by rw [h', map_zero])
    subst ha
    rfl
  have hfsurj : Function.Surjective f := by
    intro b
    have hz : q (b - s (q b)) = 0 := by rw [map_sub, freeSection_spec, sub_self]
    obtain ⟨a, ha⟩ := (hex (b - s (q b))).mp hz
    refine ⟨(a, q b), ?_⟩
    show i a + s (q b) = b
    rw [ha]
    abel
  exact (AddEquiv.ofBijective f ⟨hfinj, hfsurj⟩).symm

/-- Concatenation of finite free coordinates. -/
public def finArrowProdAddEquiv (a m : ℕ) :
    ((Fin a → ℤ) × (Fin m → ℤ)) ≃+ (Fin (a + m) → ℤ) where
  toFun p i := Sum.elim p.1 p.2 (finSumFinEquiv.symm i)
  invFun f := (fun i ↦ f (finSumFinEquiv (Sum.inl i)), fun i ↦ f (finSumFinEquiv (Sum.inr i)))
  left_inv p := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> simp
  right_inv f := by
    funext i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    rcases j with j | j <;> simp
  map_add' p q := by
    funext i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    rcases j with j | j <;> simp

/-! ## The mapping torus of the identity -/

section MappingTorus

variable {F : Type} [TopologicalSpace F]

public theorem homologyMap_refl (k : ℕ) (z : IntegralSingularHomology k F) :
    integralSingularHomologyMap k ((Homeomorph.refl F : F ≃ₜ F) : C(F, F)) z = z := by
  have h : ((Homeomorph.refl F : F ≃ₜ F) : C(F, F)) = ContinuousMap.id F := rfl
  rw [h, integralSingularHomologyMap_id_wang]

public theorem circleMonodromyDifference_refl (k : ℕ) :
    circleMonodromyDifference (Homeomorph.refl F) k = 0 := by
  ext z
  show integralSingularHomologyMap k _ z - z = 0
  rw [homologyMap_refl, sub_self]

/-- The Wang splitting of the mapping torus of the identity: its homology in degree `k + 1` is
the sum of the degree `k + 1` and degree `k` homology of the fibre. -/
public def reflMappingTorusHomologySplit (k a m : ℕ)
    (e1 : IntegralSingularHomology (k + 1) F ≃+ (Fin a → ℤ))
    (e0 : IntegralSingularHomology k F ≃+ (Fin m → ℤ)) :
    IntegralSingularHomology (k + 1) (CircleMappingTorus (Homeomorph.refl F)) ≃+
      (Fin (a + m) → ℤ) := by
  classical
  set P := circleMappingTorusWangPresentationOfCover (Homeomorph.refl F) k with hP
  have hhigh : P.highDifference = 0 := circleMonodromyDifference_refl (F := F) (k + 1)
  have hlow : P.lowDifference = 0 := circleMonodromyDifference_refl (F := F) k
  have hi : Function.Injective P.inclusion := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨c, hc⟩ := (P.exact_highDifference_inclusion b).mp hb
    rw [hhigh] at hc
    simpa using hc.symm
  have hbsurj : Function.Surjective P.boundary := by
    intro y
    exact (P.exact_boundary_lowDifference y).mp (by rw [hlow]; rfl)
  let q : IntegralSingularHomology (k + 1) (CircleMappingTorus (Homeomorph.refl F)) →+
      (Fin m → ℤ) := e0.toAddMonoidHom.comp P.boundary
  have hq : Function.Surjective q := e0.surjective.comp hbsurj
  have hex : Function.Exact P.inclusion q := by
    intro b
    rw [← P.exact_inclusion_boundary b]
    constructor
    · intro h
      have h' : e0 (P.boundary b) = 0 := h
      exact e0.injective (by rw [h', map_zero])
    · intro h
      show e0 (P.boundary b) = 0
      rw [h, map_zero]
  exact ((splitOfFreeQuotient P.inclusion q hi hq hex).trans
    (e1.prodCongr (AddEquiv.refl _))).trans (finArrowProdAddEquiv a m)

end MappingTorus

/-! ## The standard real torus as an iterated mapping torus -/

section StandardTorus

public theorem unitAddCircle_eq_iff (t t' : ℝ) :
    ((t : UnitAddCircle)) = (t' : UnitAddCircle) ↔ ∃ k : ℤ, t - t' = k := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk]; simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by simp [hk]⟩

public theorem unitAddCircle_zero_eq_one :
    ((0 : ℝ) : UnitAddCircle) = ((1 : ℝ) : UnitAddCircle) :=
  (unitAddCircle_eq_iff 0 1).mpr ⟨-1, by norm_num⟩

/-- The cylinder parametrization of the standard torus one dimension up. -/
public def stdTorusCylinderMap (n : ℕ) (p : Unit × unitInterval × StdTorus n) :
    StdTorus (n + 1) :=
  Fin.cons ((p.2.1 : ℝ) : UnitAddCircle) p.2.2

public theorem continuous_stdTorusCylinderMap (n : ℕ) :
    Continuous (stdTorusCylinderMap n) := by
  refine continuous_pi fun i ↦ ?_
  induction i using Fin.cases with
  | zero =>
    simp only [stdTorusCylinderMap, Fin.cons_zero]
    exact (AddCircle.continuous_mk' 1).comp
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  | succ j =>
    simp only [stdTorusCylinderMap, Fin.cons_succ]
    exact (continuous_apply j).comp (continuous_snd.comp continuous_snd)

/-- The identity clutching, packaged as a one-loop bouquet monodromy. -/
public abbrev stdTorusClutching (n : ℕ) : Unit → StdTorus n ≃ₜ StdTorus n :=
  fun _ ↦ Homeomorph.refl (StdTorus n)

public theorem bouquetKey_std_end (n : ℕ) (r : Unit × unitInterval × StdTorus n)
    (h : r.2.1 = 0 ∨ r.2.1 = 1) :
    bouquetKey (stdTorusClutching n) r = Sum.inl r.2.2 := by
  obtain ⟨u, t, x⟩ := r
  rcases h with h | h
  · subst h
    exact bouquetKey_zero _ u x
  · subst h
    exact bouquetKey_one _ u x

public theorem bouquetKey_std_interior (n : ℕ) (r : Unit × unitInterval × StdTorus n)
    (h0 : r.2.1 ≠ 0) (h1 : r.2.1 ≠ 1) :
    bouquetKey (stdTorusClutching n) r = Sum.inr r :=
  bouquetKey_of_ne _ h0 h1

public theorem stdTorusCylinderMap_of_key (n : ℕ) (p q : Unit × unitInterval × StdTorus n)
    (h : bouquetKey (stdTorusClutching n) p = bouquetKey (stdTorusClutching n) q) :
    stdTorusCylinderMap n p = stdTorusCylinderMap n q := by
  by_cases hp : p.2.1 = 0 ∨ p.2.1 = 1
  · by_cases hq : q.2.1 = 0 ∨ q.2.1 = 1
    · rw [bouquetKey_std_end n p hp, bouquetKey_std_end n q hq, Sum.inl.injEq] at h
      have hcoe : ((p.2.1 : ℝ) : UnitAddCircle) = ((q.2.1 : ℝ) : UnitAddCircle) := by
        rcases hp with hp | hp <;> rcases hq with hq | hq <;> rw [hp, hq]
        · exact unitAddCircle_zero_eq_one
        · exact unitAddCircle_zero_eq_one.symm
      rw [stdTorusCylinderMap, stdTorusCylinderMap, hcoe, h]
    · rw [bouquetKey_std_end n p hp,
        bouquetKey_std_interior n q (fun hx ↦ hq (Or.inl hx)) (fun hx ↦ hq (Or.inr hx))] at h
      exact absurd h (by simp)
  · by_cases hq : q.2.1 = 0 ∨ q.2.1 = 1
    · rw [bouquetKey_std_interior n p (fun hx ↦ hp (Or.inl hx)) (fun hx ↦ hp (Or.inr hx)),
        bouquetKey_std_end n q hq] at h
      exact absurd h (by simp)
    · rw [bouquetKey_std_interior n p (fun hx ↦ hp (Or.inl hx)) (fun hx ↦ hp (Or.inr hx)),
        bouquetKey_std_interior n q (fun hx ↦ hq (Or.inl hx)) (fun hx ↦ hq (Or.inr hx)),
        Sum.inr.injEq] at h
      rw [h]

/-- The standard torus, as a quotient of the cylinder over the torus one dimension down. -/
public def stdTorusOfMappingTorus (n : ℕ) :
    CircleMappingTorus (Homeomorph.refl (StdTorus n)) → StdTorus (n + 1) :=
  Quotient.lift (stdTorusCylinderMap n) fun p q h ↦
    stdTorusCylinderMap_of_key n p q ((eqvGen_iff_bouquetKey _ p q).mp h)

public theorem continuous_stdTorusOfMappingTorus (n : ℕ) :
    Continuous (stdTorusOfMappingTorus n) :=
  continuous_quot_lift _ (continuous_stdTorusCylinderMap n)

public theorem stdTorusOfMappingTorus_surjective (n : ℕ) :
    Function.Surjective (stdTorusOfMappingTorus n) := by
  intro z
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ)) (z 0)
  have ht : Int.fract r ∈ unitInterval :=
    ⟨Int.fract_nonneg r, (Int.fract_lt_one r).le⟩
  have hcoe : ((Int.fract r : ℝ) : UnitAddCircle) = z 0 := by
    rw [← hr, unitAddCircle_eq_iff]
    refine ⟨-⌊r⌋, ?_⟩
    have hfr : Int.fract r = r - ⌊r⌋ := rfl
    rw [hfr]
    push_cast
    ring
  refine ⟨Quotient.mk _ ((), ⟨Int.fract r, ht⟩, Fin.tail z), ?_⟩
  show Fin.cons ((Int.fract r : ℝ) : UnitAddCircle) (Fin.tail z) = z
  rw [hcoe, Fin.cons_self_tail]

public theorem stdTorusOfMappingTorus_injective (n : ℕ) :
    Function.Injective (stdTorusOfMappingTorus n) := by
  refine fun a b ↦ Quotient.inductionOn₂ a b fun p q hab ↦ ?_
  have hab' : stdTorusCylinderMap n p = stdTorusCylinderMap n q := hab
  have hy : p.2.2 = q.2.2 := by
    funext j
    have h2 := congrFun hab' j.succ
    simpa [stdTorusCylinderMap] using h2
  have hc : ((p.2.1 : ℝ) : UnitAddCircle) = ((q.2.1 : ℝ) : UnitAddCircle) := by
    have h2 := congrFun hab' 0
    simpa [stdTorusCylinderMap] using h2
  obtain ⟨k, hk⟩ := (unitAddCircle_eq_iff _ _).mp hc
  have hp0 : (0 : ℝ) ≤ (p.2.1 : ℝ) := unitInterval.nonneg p.2.1
  have hp1 : ((p.2.1 : ℝ)) ≤ 1 := unitInterval.le_one p.2.1
  have hq0 : (0 : ℝ) ≤ (q.2.1 : ℝ) := unitInterval.nonneg q.2.1
  have hq1 : ((q.2.1 : ℝ)) ≤ 1 := unitInterval.le_one q.2.1
  have hkle : (k : ℝ) ≤ 1 := by rw [← hk]; linarith
  have hkge : (-1 : ℝ) ≤ (k : ℝ) := by rw [← hk]; linarith
  have hk1 : k ≤ 1 := by exact_mod_cast hkle
  have hk2 : -1 ≤ k := by exact_mod_cast hkge
  refine (bouquetMk_eq_iff (stdTorusClutching n) p q).mpr ?_
  interval_cases k
  · have hpv : (p.2.1 : ℝ) = 0 := by push_cast at hk; linarith
    have hqv : (q.2.1 : ℝ) = 1 := by push_cast at hk; linarith
    rw [bouquetKey_std_end n p (Or.inl (Subtype.ext hpv)),
      bouquetKey_std_end n q (Or.inr (Subtype.ext hqv)), hy]
  · have hpq : p.2.1 = q.2.1 := by
      refine Subtype.ext ?_
      push_cast at hk
      linarith
    have hpq2 : p = q := by
      refine Prod.ext (Subsingleton.elim _ _) (Prod.ext hpq hy)
    rw [hpq2]
  · have hpv : (p.2.1 : ℝ) = 1 := by push_cast at hk; linarith
    have hqv : (q.2.1 : ℝ) = 0 := by push_cast at hk; linarith
    rw [bouquetKey_std_end n p (Or.inr (Subtype.ext hpv)),
      bouquetKey_std_end n q (Or.inl (Subtype.ext hqv)), hy]

/-- The standard `(n + 1)`-torus is the mapping torus of the identity of the `n`-torus. -/
public def stdTorusMappingTorusHomeomorph (n : ℕ) :
    CircleMappingTorus (Homeomorph.refl (StdTorus n)) ≃ₜ StdTorus (n + 1) := by
  haveI : CompactSpace (CircleMappingTorus (Homeomorph.refl (StdTorus n))) :=
    inferInstanceAs (CompactSpace
      (Quotient (finiteBouquetMappingTorusSetoid (stdTorusClutching n))))
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (stdTorusOfMappingTorus n)
      ⟨stdTorusOfMappingTorus_injective n, stdTorusOfMappingTorus_surjective n⟩)
    (continuous_stdTorusOfMappingTorus n)

end StandardTorus

/-! ## Integral homology of the standard torus -/

section StandardTorusHomologyGroups

open CategoryTheory CategoryTheory.Limits

/-- Any two subsingleton abelian groups are additively equivalent. -/
public def addEquivOfSubsingleton {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Subsingleton G] [Subsingleton H] : G ≃+ H where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _

public instance : TotallyDisconnectedSpace (StdTorus 0) :=
  ⟨fun _ _ _ a _ b _ ↦ Subsingleton.elim a b⟩

public theorem subsingleton_homology_stdTorusZero (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (IntegralSingularHomology k (StdTorus 0)) :=
  AddCommGrpCat.subsingleton_of_isZero
    (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (C := AddCommGrpCat) (n := k) (AddCommGrpCat.of ℤ) (TopCat.of (StdTorus 0)) hk)

/-- Integer coordinates on a single generator. -/
public def intEquivFinOne : ℤ ≃+ (Fin 1 → ℤ) where
  toFun a _ := a
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := by
    funext i
    fin_cases i
    rfl
  map_add' _ _ := rfl

public def stdTorusHomologyZero (n : ℕ) :
    IntegralSingularHomology 0 (StdTorus n) ≃+ (Fin 1 → ℤ) :=
  (pathConnectedIntegralHomologyZeroEquivInteger (StdTorus n)).trans intEquivFinOne

/-- The rank of the second homology of the standard `n`-torus. -/
public def stdTorusTwoRank : ℕ → ℕ
  | 0 => 0
  | n + 1 => stdTorusTwoRank n + n

public def stdTorusHomologyOne : ∀ n : ℕ,
    IntegralSingularHomology 1 (StdTorus n) ≃+ (Fin n → ℤ)
  | 0 => by
      haveI := subsingleton_homology_stdTorusZero 1 one_ne_zero
      exact addEquivOfSubsingleton
  | n + 1 =>
      (integralSingularHomologyEquiv 1 (stdTorusMappingTorusHomeomorph n)).symm.trans
        (reflMappingTorusHomologySplit 0 n 1 (stdTorusHomologyOne n) (stdTorusHomologyZero n))

public def stdTorusHomologyTwo : ∀ n : ℕ,
    IntegralSingularHomology 2 (StdTorus n) ≃+ (Fin (stdTorusTwoRank n) → ℤ)
  | 0 => by
      haveI := subsingleton_homology_stdTorusZero 2 two_ne_zero
      show IntegralSingularHomology 2 (StdTorus 0) ≃+ (Fin 0 → ℤ)
      exact addEquivOfSubsingleton
  | n + 1 =>
      (integralSingularHomologyEquiv 2 (stdTorusMappingTorusHomeomorph n)).symm.trans
        (reflMappingTorusHomologySplit 1 (stdTorusTwoRank n) n (stdTorusHomologyTwo n)
          (stdTorusHomologyOne n))

/-! ## Natural recalibration of the four-torus coordinates -/

open Geometry.ComplexTorus

/-- First coordinate in the ordered list `(01, 02, 03, 12, 13, 23)`. -/
public def standardPeriodPairFirst : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

/-- Second coordinate in the ordered list `(01, 02, 03, 12, 13, 23)`. -/
public def standardPeriodPairSecond : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

/-- The second compound of a four-by-four integer matrix. -/
public def standardSecondCompoundMatrix
    (M : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 6) (Fin 6) ℤ :=
  fun ij ab ↦
    M (standardPeriodPairFirst ij) (standardPeriodPairFirst ab) *
        M (standardPeriodPairSecond ij) (standardPeriodPairSecond ab) -
      M (standardPeriodPairFirst ij) (standardPeriodPairSecond ab) *
        M (standardPeriodPairSecond ij) (standardPeriodPairFirst ab)

/-- The exterior-square map in increasing-pair coordinates. -/
public def standardExteriorSquareMap
    (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) : (Fin 6 → ℤ) →+ (Fin 6 → ℤ) :=
  (Matrix.toLin' (standardSecondCompoundMatrix (LinearMap.toMatrix' e.toLinearMap))).toAddHom

/-- The universal-cover projection from real coordinates to the standard four-torus. -/
public def standardFourTorusProjection (r : RealPeriods) : StdTorus 4 :=
  fun i ↦ ((r i : ℝ) : UnitAddCircle)

/-- A continuous standard-torus map together with an additive lift having a prescribed lattice
action. -/
public structure StandardFourTorusEquivariantLift
    (f : C(StdTorus 4, StdTorus 4)) (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) where
  lift : RealPeriods ≃+ RealPeriods
  map_projection (r : RealPeriods) :
    f (standardFourTorusProjection r) = standardFourTorusProjection (lift r)
  map_integer (n : IntegerPeriods) : lift (integerToReal n) = integerToReal (e n)

/-! ## Canonical degree-one classes -/

/-- Include the `i`-th coordinate circle into the standard four-torus. -/
public def standardFourTorusCoordinateCircle (i : Fin 4) : C(StdTorus 1, StdTorus 4) where
  toFun z j := if j = i then z 0 else 0
  continuous_toFun := by
    apply continuous_pi
    intro j
    by_cases h : j = i
    · simp only [h, ↓reduceIte]
      fun_prop
    · simp only [h, ↓reduceIte]
      fun_prop

/-- Project the standard four-torus onto its `i`-th coordinate circle. -/
public def standardFourTorusCoordinateProjection (i : Fin 4) : C(StdTorus 4, StdTorus 1) where
  toFun z _ := z i
  continuous_toFun := by
    fun_prop

private def standardCircleToPoint : C(StdTorus 1, StdTorus 0) where
  toFun _ i := Fin.elim0 i
  continuous_toFun := by
    fun_prop

private def pointToStandardCircle : C(StdTorus 0, StdTorus 1) where
  toFun _ _ := 0
  continuous_toFun := by
    fun_prop

private theorem coordinateProjection_comp_coordinateCircle_self (i : Fin 4) :
    (standardFourTorusCoordinateProjection i).comp (standardFourTorusCoordinateCircle i) =
      ContinuousMap.id _ := by
  ext z k
  fin_cases k
  simp [standardFourTorusCoordinateProjection, standardFourTorusCoordinateCircle]

private theorem coordinateProjection_comp_coordinateCircle_of_ne
    {i j : Fin 4} (h : i ≠ j) :
    (standardFourTorusCoordinateProjection i).comp (standardFourTorusCoordinateCircle j) =
      pointToStandardCircle.comp standardCircleToPoint := by
  ext z k
  fin_cases k
  simp [standardFourTorusCoordinateProjection, standardFourTorusCoordinateCircle,
    pointToStandardCircle, standardCircleToPoint, h]

private theorem homologyMap_standardCircle_pointFactor_zero
    (x : IntegralSingularHomology 1 (StdTorus 1)) :
    integralSingularHomologyMap 1 (pointToStandardCircle.comp standardCircleToPoint) x = 0 := by
  rw [← integralSingularHomologyMap_comp_wang]
  let _ := subsingleton_homology_stdTorusZero 1 one_ne_zero
  have hzero : integralSingularHomologyMap 1 standardCircleToPoint x = 0 :=
    Subsingleton.elim _ _
  rw [hzero, map_zero]

/-- The positive geometric loop in the standard one-torus. -/
public def standardCirclePositiveLoop : Path (0 : StdTorus 1) 0 :=
  ((StandardCircleHomologyLiftDegree.unitCircleIntegerLoop 1).map
    StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph.symm.continuous).cast rfl rfl

/-- The positively oriented geometric generator of the standard circle. -/
public def standardCircleHomologyGenerator :
    IntegralSingularHomology 1 (StdTorus 1) :=
  StandardCircleHomologyLiftDegree.loopHomologyClass standardCirclePositiveLoop

public theorem standardCircleHomologyGenerator_winding :
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph :
            C(StdTorus 1, UnitAddCircle))
          standardCircleHomologyGenerator) = 1 := by
  rw [standardCircleHomologyGenerator,
    StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass]
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (StandardCircleHomologyLiftDegree.loopHomologyClass
        (StandardCircleHomologyLiftDegree.unitCircleIntegerLoop 1)) = 1
  exact StandardCircleHomologyLiftDegree.unitCircleHomologyWinding_positive

private def finOneFunctionAddEquiv : (Fin 1 → ℤ) ≃+ ℤ where
  toFun f := f 0
  invFun z := fun _ ↦ z
  left_inv f := by
    funext i
    fin_cases i
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private def unitCircleHomologyEquivInt :
    IntegralSingularHomology 1 UnitAddCircle ≃+ ℤ :=
  (integralSingularHomologyEquiv 1
      StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph.symm).trans
    ((stdTorusHomologyOne 1).trans finOneFunctionAddEquiv)

private theorem unitCircleHomologyWinding_injective :
    Function.Injective StandardCircleHomologyLiftDegree.unitCircleHomologyWinding := by
  open StandardCircleHomologyLiftDegree in
  let φ : ℤ →+ ℤ := unitCircleHomologyWinding.comp
    unitCircleHomologyEquivInt.symm.toAddMonoidHom
  have hφsurj : Function.Surjective φ := by
    intro n
    obtain ⟨x, hx⟩ := unitCircleHomologyWinding_surjective n
    exact ⟨unitCircleHomologyEquivInt x, by simpa [φ] using hx⟩
  have hφone : φ 1 ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := hφsurj 1
    rw [φ.apply_int, h, smul_zero] at hm
    exact one_ne_zero hm.symm
  have hφinj : Function.Injective φ := by
    intro m n hmn
    have hz : φ (m - n) = 0 := by rw [map_sub, hmn, sub_self]
    rw [φ.apply_int] at hz
    have hmul : (m - n) * φ 1 = 0 := by simpa [smul_eq_mul] using hz
    exact sub_eq_zero.mp ((Int.mul_eq_zero.mp hmul).resolve_right hφone)
  intro x y hxy
  apply unitCircleHomologyEquivInt.injective
  apply hφinj
  simpa [φ] using hxy

private theorem unitCirclePowerMap_homology (n : ℤ)
    (x : IntegralSingularHomology 1 UnitAddCircle) :
    integralSingularHomologyMap 1
        (StandardCircleHomologyLiftDegree.unitCirclePowerMap n) x = n • x := by
  open StandardCircleHomologyLiftDegree in
  have hx : x = unitCircleHomologyWinding x • unitCirclePositiveHomologyClass := by
    apply unitCircleHomologyWinding_injective
    simp [unitCircleHomologyWinding_positive]
  rw [hx, map_zsmul, unitCirclePowerMap_positiveHomologyClass]
  apply unitCircleHomologyWinding_injective
  simp [map_zsmul, unitCircleHomologyWinding_integerLoop,
    unitCircleHomologyWinding_positive, mul_comm]

private theorem stdTorusOnePowerMap_homology (n : ℤ)
    (x : IntegralSingularHomology 1 (StdTorus 1)) :
    integralSingularHomologyMap 1
        (StandardCircleHomologyLiftDegree.stdTorusOnePowerMap n) x = n • x := by
  open StandardCircleHomologyLiftDegree in
  apply (integralSingularHomologyEquiv 1 stdTorusOneHomeomorph).injective
  change integralSingularHomologyMap 1
      (stdTorusOneHomeomorph : C(StdTorus 1, UnitAddCircle))
        (integralSingularHomologyMap 1 (stdTorusOnePowerMap n) x) =
    integralSingularHomologyMap 1
      (stdTorusOneHomeomorph : C(StdTorus 1, UnitAddCircle)) (n • x)
  rw [integralSingularHomologyMap_comp_wang, stdTorusOneHomeomorph_comp_power,
    ← integralSingularHomologyMap_comp_wang, unitCirclePowerMap_homology, map_zsmul]

/-- A continuous circle map with an additive real lift of integer degree `n` sends the selected
circle generator to `n` times itself. -/
public theorem standardCircleHomologyGenerator_map_of_additiveLift
    (f : C(StdTorus 1, StdTorus 1)) (L : ℝ →+ ℝ) (n : ℤ)
    (map_projection : ∀ r : ℝ,
      f (StandardCircleHomologyLiftDegree.stdTorusOneProjection r) =
        StandardCircleHomologyLiftDegree.stdTorusOneProjection (L r))
    (map_one : L 1 = (n : ℝ)) :
    integralSingularHomologyMap 1 f standardCircleHomologyGenerator =
      n • standardCircleHomologyGenerator := by
  rw [StandardCircleHomologyLiftDegree.stdTorusOneMap_eq_power_of_additiveLift
    f L n map_projection map_one]
  exact stdTorusOnePowerMap_homology n _

/-- The homology class of the `i`-th coordinate circle. -/
public def standardFourTorusCoordinateHomologyClass (i : Fin 4) :
    IntegralSingularHomology 1 (StdTorus 4) :=
  integralSingularHomologyMap 1 (standardFourTorusCoordinateCircle i)
    standardCircleHomologyGenerator

/-- Detect a degree-one class by projecting it onto the four coordinate circles. -/
public noncomputable def standardFourTorusCoordinateHom :
    IntegralSingularHomology 1 (StdTorus 4) →+ (Fin 4 → ℤ) where
  toFun x i :=
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1
        (StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph :
          C(StdTorus 1, UnitAddCircle))
        (integralSingularHomologyMap 1 (standardFourTorusCoordinateProjection i) x))
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp

/-- Coordinate projections evaluate on coordinate-circle classes as the standard basis. -/
public theorem standardFourTorusCoordinateHom_coordinateHomologyClass (j : Fin 4) :
    standardFourTorusCoordinateHom (standardFourTorusCoordinateHomologyClass j) =
      Pi.single j 1 := by
  funext i
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1
        (StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph :
          C(StdTorus 1, UnitAddCircle))
        (integralSingularHomologyMap 1 (standardFourTorusCoordinateProjection i)
          (integralSingularHomologyMap 1 (standardFourTorusCoordinateCircle j)
            standardCircleHomologyGenerator))) = (Pi.single j 1 : Fin 4 → ℤ) i
  have hinner :
      integralSingularHomologyMap 1 (standardFourTorusCoordinateProjection i)
          (integralSingularHomologyMap 1 (standardFourTorusCoordinateCircle j)
            standardCircleHomologyGenerator) =
        integralSingularHomologyMap 1
          ((standardFourTorusCoordinateProjection i).comp
            (standardFourTorusCoordinateCircle j)) standardCircleHomologyGenerator :=
    integralSingularHomologyMap_comp_wang _ _ _ _
  rw [hinner]
  by_cases h : i = j
  · subst i
    rw [coordinateProjection_comp_coordinateCircle_self,
      integralSingularHomologyMap_id_wang]
    rw [standardCircleHomologyGenerator_winding]
    simp
  · rw [coordinateProjection_comp_coordinateCircle_of_ne h,
      homologyMap_standardCircle_pointFactor_zero]
    simp [h]

public theorem standardFourTorusCoordinateHom_surjective :
    Function.Surjective standardFourTorusCoordinateHom := by
  intro v
  refine ⟨∑ i, v i • standardFourTorusCoordinateHomologyClass i, ?_⟩
  rw [map_sum]
  simp only [map_zsmul, standardFourTorusCoordinateHom_coordinateHomologyClass]
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

public theorem standardFourTorusCoordinateHom_injective :
    Function.Injective standardFourTorusCoordinateHom := by
  let F : (Fin 4 → ℤ) →+ (Fin 4 → ℤ) :=
    standardFourTorusCoordinateHom.comp (stdTorusHomologyOne 4).symm.toAddMonoidHom
  have hsurj : Function.Surjective F :=
    standardFourTorusCoordinateHom_surjective.comp (stdTorusHomologyOne 4).symm.surjective
  have hinj : Function.Injective F :=
    Module.End.injective_of_surjective ℤ (Fin 4 → ℤ) (f := F.toIntLinearMap) hsurj
  intro x y hxy
  apply (stdTorusHomologyOne 4).injective
  apply hinj
  change standardFourTorusCoordinateHom
      ((stdTorusHomologyOne 4).symm (stdTorusHomologyOne 4 x)) =
    standardFourTorusCoordinateHom
      ((stdTorusHomologyOne 4).symm (stdTorusHomologyOne 4 y))
  simpa using hxy

/-- The four coordinate-circle classes are an integral basis of degree-one homology. -/
public noncomputable def standardFourTorusCanonicalHomologyOne :
    IntegralSingularHomology 1 (StdTorus 4) ≃+ (Fin 4 → ℤ) :=
  AddEquiv.ofBijective standardFourTorusCoordinateHom
    ⟨standardFourTorusCoordinateHom_injective, standardFourTorusCoordinateHom_surjective⟩

/-- Recalibrate the choice-based Wang basis to the coordinate-circle basis. -/
public noncomputable def standardFourTorusCanonicalDegreeOneRecalibration :
    (Fin 4 → ℤ) ≃+ (Fin 4 → ℤ) :=
  (stdTorusHomologyOne 4).symm.trans standardFourTorusCanonicalHomologyOne

public theorem standardFourTorusCanonicalDegreeOneRecalibration_apply
    (x : IntegralSingularHomology 1 (StdTorus 4)) :
    standardFourTorusCanonicalDegreeOneRecalibration (stdTorusHomologyOne 4 x) =
      standardFourTorusCanonicalHomologyOne x := by
  simp [standardFourTorusCanonicalDegreeOneRecalibration]

private def standardRealCoordinateLine (j : Fin 4) : ℝ →+ RealPeriods where
  toFun r := Pi.single j r
  map_zero' := by
    funext k
    simp [Pi.single_apply]
  map_add' r s := by
    funext k
    by_cases h : j = k <;> simp [h]

private def standardFourTorusCoordinateLift
    {f : C(StdTorus 4, StdTorus 4)} {e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods}
    (L : StandardFourTorusEquivariantLift f e) (i j : Fin 4) : ℝ →+ ℝ where
  toFun r := L.lift (standardRealCoordinateLine j r) i
  map_zero' := by simp
  map_add' r s := by simp

private def standardFourTorusCoordinateCircleMap
    (f : C(StdTorus 4, StdTorus 4)) (i j : Fin 4) : C(StdTorus 1, StdTorus 1) :=
  ((standardFourTorusCoordinateProjection i).comp f).comp
    (standardFourTorusCoordinateCircle j)

private theorem standardFourTorusProjection_coordinateLine (j : Fin 4) (r : ℝ) :
    standardFourTorusProjection (standardRealCoordinateLine j r) =
      standardFourTorusCoordinateCircle j
        (StandardCircleHomologyLiftDegree.stdTorusOneProjection r) := by
  funext k
  by_cases h : k = j
  · subst k
    simp [standardFourTorusProjection, standardRealCoordinateLine,
      standardFourTorusCoordinateCircle,
      StandardCircleHomologyLiftDegree.stdTorusOneProjection]
  · simp [standardFourTorusProjection, standardRealCoordinateLine,
      standardFourTorusCoordinateCircle, h]

private theorem standardFourTorusCoordinateCircleMap_projection
    {f : C(StdTorus 4, StdTorus 4)} {e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods}
    (L : StandardFourTorusEquivariantLift f e) (i j : Fin 4) (r : ℝ) :
    standardFourTorusCoordinateCircleMap f i j
        (StandardCircleHomologyLiftDegree.stdTorusOneProjection r) =
      StandardCircleHomologyLiftDegree.stdTorusOneProjection
        (standardFourTorusCoordinateLift L i j r) := by
  funext k
  fin_cases k
  change f (standardFourTorusCoordinateCircle j
      (StandardCircleHomologyLiftDegree.stdTorusOneProjection r)) i =
    ((L.lift (standardRealCoordinateLine j r) i : ℝ) : UnitAddCircle)
  rw [← standardFourTorusProjection_coordinateLine]
  exact congrFun (L.map_projection (standardRealCoordinateLine j r)) i

private theorem standardFourTorusCoordinateLift_one
    {f : C(StdTorus 4, StdTorus 4)} {e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods}
    (L : StandardFourTorusEquivariantLift f e) (i j : Fin 4) :
    standardFourTorusCoordinateLift L i j 1 =
      ((e (Pi.single j 1)) i : ℝ) := by
  change L.lift (standardRealCoordinateLine j 1) i = _
  have hline : standardRealCoordinateLine j 1 = integerToReal (Pi.single j 1) := by
    funext k
    simp [standardRealCoordinateLine, integerToReal, Pi.single_apply]
  rw [hline]
  exact congrFun (L.map_integer (Pi.single j 1)) i

private theorem standardFourTorusCanonicalHomologyOne_coordinate_naturality
    (f : C(StdTorus 4, StdTorus 4)) (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods)
    (L : StandardFourTorusEquivariantLift f e) (j : Fin 4) :
    standardFourTorusCanonicalHomologyOne
        (integralSingularHomologyMap 1 f (standardFourTorusCoordinateHomologyClass j)) =
      e (Pi.single j 1) := by
  funext i
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1
        (StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph :
          C(StdTorus 1, UnitAddCircle))
        (integralSingularHomologyMap 1 (standardFourTorusCoordinateProjection i)
          (integralSingularHomologyMap 1 f
            (integralSingularHomologyMap 1 (standardFourTorusCoordinateCircle j)
              standardCircleHomologyGenerator)))) = _
  have hinner :
      integralSingularHomologyMap 1 (standardFourTorusCoordinateProjection i)
          (integralSingularHomologyMap 1 f
            (integralSingularHomologyMap 1 (standardFourTorusCoordinateCircle j)
              standardCircleHomologyGenerator)) =
        integralSingularHomologyMap 1 (standardFourTorusCoordinateCircleMap f i j)
          standardCircleHomologyGenerator := by
    rw [integralSingularHomologyMap_comp_wang, integralSingularHomologyMap_comp_wang]
    rfl
  rw [hinner]
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1
        (StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph :
          C(StdTorus 1, UnitAddCircle))
        (integralSingularHomologyMap 1 (standardFourTorusCoordinateCircleMap f i j)
          standardCircleHomologyGenerator)) = _
  rw [standardCircleHomologyGenerator_map_of_additiveLift
      (standardFourTorusCoordinateCircleMap f i j)
      (standardFourTorusCoordinateLift L i j) ((e (Pi.single j 1)) i)
      (standardFourTorusCoordinateCircleMap_projection L i j)
      (standardFourTorusCoordinateLift_one L i j)]
  rw [map_zsmul, map_zsmul, standardCircleHomologyGenerator_winding]
  simp

private theorem sum_zsmul_pi_single (v : Fin 4 → ℤ) :
    ∑ j, v j • (Pi.single j 1 : Fin 4 → ℤ) = v := by
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

private theorem standardFourTorusCanonicalHomologyOne_coordinateHomologyClass (j : Fin 4) :
    standardFourTorusCanonicalHomologyOne (standardFourTorusCoordinateHomologyClass j) =
      Pi.single j 1 := by
  change standardFourTorusCoordinateHom (standardFourTorusCoordinateHomologyClass j) = _
  exact standardFourTorusCoordinateHom_coordinateHomologyClass j

/-- The canonical degree-one coordinate basis is natural for every equivariant real lift. -/
public theorem standardFourTorusCanonicalHomologyOne_naturality
    (f : C(StdTorus 4, StdTorus 4)) (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods)
    (L : StandardFourTorusEquivariantLift f e)
    (x : IntegralSingularHomology 1 (StdTorus 4)) :
    standardFourTorusCanonicalHomologyOne (integralSingularHomologyMap 1 f x) =
      e (standardFourTorusCanonicalHomologyOne x) := by
  let v := standardFourTorusCanonicalHomologyOne x
  have hx : x = ∑ j, v j • standardFourTorusCoordinateHomologyClass j := by
    apply standardFourTorusCanonicalHomologyOne.injective
    rw [map_sum]
    simp only [map_zsmul]
    rw [show ∑ j, v j • standardFourTorusCanonicalHomologyOne
        (standardFourTorusCoordinateHomologyClass j) =
      ∑ j, v j • (Pi.single j 1 : Fin 4 → ℤ) by
        apply Finset.sum_congr rfl
        intro j _
        rw [standardFourTorusCanonicalHomologyOne_coordinateHomologyClass]]
    exact (sum_zsmul_pi_single v).symm
  calc
    standardFourTorusCanonicalHomologyOne (integralSingularHomologyMap 1 f x) =
        ∑ j, v j • standardFourTorusCanonicalHomologyOne
          (integralSingularHomologyMap 1 f
            (standardFourTorusCoordinateHomologyClass j)) := by
      rw [hx, map_sum, map_sum]
      simp only [map_zsmul]
    _ = ∑ j, v j • e (Pi.single j 1) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [standardFourTorusCanonicalHomologyOne_coordinate_naturality f e L j]
    _ = e (∑ j, v j • (Pi.single j 1 : Fin 4 → ℤ)) := by
      rw [map_sum]
      simp only [map_zsmul]
    _ = e v := by rw [sum_zsmul_pi_single]
    _ = e (standardFourTorusCanonicalHomologyOne x) := rfl

/-! ## Canonical degree-two classes -/

/-- Include the coordinate two-torus indexed by one of the pairs
`(01, 02, 03, 12, 13, 23)`. -/
public def standardFourTorusCoordinateTwoTorus (p : Fin 6) : C(StdTorus 2, StdTorus 4) where
  toFun z k :=
    if k = standardPeriodPairFirst p then z 0
    else if k = standardPeriodPairSecond p then z 1
    else 0
  continuous_toFun := by
    apply continuous_pi
    intro k
    by_cases h0 : k = standardPeriodPairFirst p
    · simp only [h0, ↓reduceIte]
      fun_prop
    · simp only [h0, ↓reduceIte]
      by_cases h1 : k = standardPeriodPairSecond p
      · simp only [h1, ↓reduceIte]
        fun_prop
      · simp only [h1, ↓reduceIte]
        fun_prop

/-- Project the standard four-torus onto one of its six coordinate two-tori. -/
public def standardFourTorusCoordinateTwoTorusProjection (p : Fin 6) :
    C(StdTorus 4, StdTorus 2) where
  toFun z := ![z (standardPeriodPairFirst p), z (standardPeriodPairSecond p)]
  continuous_toFun := by
    fun_prop

private def standardTwoTorusCoordinateProjection (i : Fin 2) :
    C(StdTorus 2, StdTorus 1) where
  toFun z _ := z i
  continuous_toFun := by
    fun_prop

private def standardTwoTorusZeroProjection : C(StdTorus 2, StdTorus 1) where
  toFun _ _ := 0
  continuous_toFun := by
    fun_prop

private def standardTwoTorusCoordinateCircle (i : Fin 2) : C(StdTorus 1, StdTorus 2) where
  toFun z k := if k = i then z 0 else 0
  continuous_toFun := by
    apply continuous_pi
    intro k
    by_cases h : k = i
    · simp only [h, ↓reduceIte]
      fun_prop
    · simp only [h, ↓reduceIte]
      fun_prop

private def standardTwoTorusPairOverlapSource (i j : Fin 6) :
    C(StdTorus 2, StdTorus 1) :=
  if standardPeriodPairFirst i = standardPeriodPairFirst j then
    standardTwoTorusCoordinateProjection 0
  else if standardPeriodPairFirst i = standardPeriodPairSecond j then
    standardTwoTorusCoordinateProjection 1
  else if standardPeriodPairSecond i = standardPeriodPairFirst j then
    standardTwoTorusCoordinateProjection 0
  else if standardPeriodPairSecond i = standardPeriodPairSecond j then
    standardTwoTorusCoordinateProjection 1
  else standardTwoTorusZeroProjection

private def standardTwoTorusPairOverlapTarget (i j : Fin 6) :
    C(StdTorus 1, StdTorus 2) :=
  if standardPeriodPairFirst i = standardPeriodPairFirst j then
    standardTwoTorusCoordinateCircle 0
  else if standardPeriodPairFirst i = standardPeriodPairSecond j then
    standardTwoTorusCoordinateCircle 0
  else if standardPeriodPairSecond i = standardPeriodPairFirst j then
    standardTwoTorusCoordinateCircle 1
  else if standardPeriodPairSecond i = standardPeriodPairSecond j then
    standardTwoTorusCoordinateCircle 1
  else standardTwoTorusCoordinateCircle 0

private theorem coordinateTwoTorusProjection_comp_coordinateTwoTorus_self (i : Fin 6) :
    (standardFourTorusCoordinateTwoTorusProjection i).comp
        (standardFourTorusCoordinateTwoTorus i) = ContinuousMap.id _ := by
  ext z k
  fin_cases i <;> fin_cases k <;>
    simp [standardFourTorusCoordinateTwoTorusProjection,
      standardFourTorusCoordinateTwoTorus, standardPeriodPairFirst, standardPeriodPairSecond]

private theorem coordinateTwoTorusProjection_comp_coordinateTwoTorus_of_ne
    {i j : Fin 6} (h : i ≠ j) :
    (standardFourTorusCoordinateTwoTorusProjection i).comp
        (standardFourTorusCoordinateTwoTorus j) =
      (standardTwoTorusPairOverlapTarget i j).comp
        (standardTwoTorusPairOverlapSource i j) := by
  ext z k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [standardFourTorusCoordinateTwoTorusProjection,
      standardFourTorusCoordinateTwoTorus, standardTwoTorusPairOverlapTarget,
      standardTwoTorusPairOverlapSource, standardTwoTorusCoordinateCircle,
      standardTwoTorusCoordinateProjection, standardTwoTorusZeroProjection,
      standardPeriodPairFirst, standardPeriodPairSecond]

private theorem subsingleton_homologyTwo_standardCircle :
    Subsingleton (IntegralSingularHomology 2 (StdTorus 1)) := by
  constructor
  intro x y
  apply (stdTorusHomologyTwo 1).injective
  funext i
  exact Fin.elim0 i

private theorem homologyMap_standardCircleFactor_degreeTwo_zero
    (f : C(StdTorus 2, StdTorus 1)) (g : C(StdTorus 1, StdTorus 2))
    (x : IntegralSingularHomology 2 (StdTorus 2)) :
    integralSingularHomologyMap 2 (g.comp f) x = 0 := by
  rw [← integralSingularHomologyMap_comp_wang]
  let _ := subsingleton_homologyTwo_standardCircle
  have hzero : integralSingularHomologyMap 2 f x = 0 := Subsingleton.elim _ _
  rw [hzero, map_zero]

public def standardTwoTorusDegreeTwoIndex : Fin (stdTorusTwoRank 2) :=
  ⟨0, by simp [stdTorusTwoRank]⟩

/-- The generator selected by the computed integral second homology of the standard two-torus. -/
public def standardTwoTorusHomologyGenerator :
    IntegralSingularHomology 2 (StdTorus 2) :=
  (stdTorusHomologyTwo 2).symm (Pi.single standardTwoTorusDegreeTwoIndex 1)

public abbrev StandardTwoRealPeriods := Fin 2 → ℝ

public abbrev StandardTwoIntegerPeriods := Fin 2 → ℤ

public def standardTwoIntegerToReal (n : StandardTwoIntegerPeriods) :
    StandardTwoRealPeriods := fun i ↦ n i

public def standardTwoTorusProjection (r : StandardTwoRealPeriods) : StdTorus 2 :=
  fun i ↦ ((r i : ℝ) : UnitAddCircle)

/-- A lifted map of the standard two-torus with its integral two-by-two lattice matrix. -/
public structure StandardTwoTorusEquivariantLift
    (g : C(StdTorus 2, StdTorus 2)) (M : Matrix (Fin 2) (Fin 2) ℤ) where
  lift : StandardTwoRealPeriods →+ StandardTwoRealPeriods
  map_projection (r : StandardTwoRealPeriods) :
    g (standardTwoTorusProjection r) = standardTwoTorusProjection (lift r)
  map_integer (n : StandardTwoIntegerPeriods) :
    lift (standardTwoIntegerToReal n) = standardTwoIntegerToReal (Matrix.mulVec M n)

public def standardTwoRealMatrixLift (M : Matrix (Fin 2) (Fin 2) ℤ) :
    StandardTwoRealPeriods →+ StandardTwoRealPeriods where
  toFun r a := ∑ b, (M a b : ℝ) * r b
  map_zero' := by
    funext a
    simp
  map_add' r s := by
    funext a
    simp [mul_add, Finset.sum_add_distrib]

public def standardTwoTorusMatrixMap (M : Matrix (Fin 2) (Fin 2) ℤ) :
    C(StdTorus 2, StdTorus 2) where
  toFun z a := ∑ b, M a b • z b
  continuous_toFun := by
    fun_prop

public theorem standardTwoTorusMatrixMap_projection
    (M : Matrix (Fin 2) (Fin 2) ℤ) (r : StandardTwoRealPeriods) :
    standardTwoTorusMatrixMap M (standardTwoTorusProjection r) =
      standardTwoTorusProjection (standardTwoRealMatrixLift M r) := by
  funext a
  unfold standardTwoTorusMatrixMap standardTwoTorusProjection standardTwoRealMatrixLift
  simp only [Fin.sum_univ_two]
  change M a 0 • ((r 0 : ℝ) : UnitAddCircle) +
      M a 1 • ((r 1 : ℝ) : UnitAddCircle) =
    (((M a 0 : ℝ) * r 0 + (M a 1 : ℝ) * r 1 : ℝ) : UnitAddCircle)
  rw [← AddCircle.coe_zsmul, ← AddCircle.coe_zsmul, ← AddCircle.coe_add]
  congr 1
  simp [zsmul_eq_mul]

public def standardTwoTorusMatrixEquivariantLift (M : Matrix (Fin 2) (Fin 2) ℤ) :
    StandardTwoTorusEquivariantLift (standardTwoTorusMatrixMap M) M where
  lift := standardTwoRealMatrixLift M
  map_projection := standardTwoTorusMatrixMap_projection M
  map_integer n := by
    funext a
    simp [standardTwoRealMatrixLift, standardTwoIntegerToReal, Matrix.mulVec]

private def standardTwoRatToReal (q : Fin 2 → ℚ) : StandardTwoRealPeriods :=
  fun i ↦ q i

private theorem standardTwoRatToReal_denseRange : DenseRange standardTwoRatToReal := by
  exact DenseRange.piMap fun _ ↦ Rat.denseRange_cast

public theorem continuous_standardTwoTorusProjection : Continuous standardTwoTorusProjection := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' 1).comp (continuous_apply i)

private theorem standardTwoEquivariantLift_rat
    {g : C(StdTorus 2, StdTorus 2)} {M : Matrix (Fin 2) (Fin 2) ℤ}
    (L : StandardTwoTorusEquivariantLift g M) (q : Fin 2 → ℚ) :
    L.lift (standardTwoRatToReal q) =
      standardTwoRealMatrixLift M (standardTwoRatToReal q) := by
  let e0 : StandardTwoRealPeriods := standardTwoIntegerToReal (Pi.single 0 1)
  let e1 : StandardTwoRealPeriods := standardTwoIntegerToReal (Pi.single 1 1)
  have hb0 : L.lift e0 = standardTwoRealMatrixLift M e0 := by
    change L.lift (standardTwoIntegerToReal (Pi.single 0 1)) = _
    rw [L.map_integer]
    exact ((standardTwoTorusMatrixEquivariantLift M).map_integer (Pi.single 0 1)).symm
  have hb1 : L.lift e1 = standardTwoRealMatrixLift M e1 := by
    change L.lift (standardTwoIntegerToReal (Pi.single 1 1)) = _
    rw [L.map_integer]
    exact ((standardTwoTorusMatrixEquivariantLift M).map_integer (Pi.single 1 1)).symm
  have hdecomp : standardTwoRatToReal q = q 0 • e0 + q 1 • e1 := by
    funext i
    fin_cases i <;>
      simp [standardTwoRatToReal, e0, e1, standardTwoIntegerToReal, Rat.smul_def]
  rw [hdecomp, map_add, map_add, map_rat_smul, map_rat_smul, map_rat_smul, map_rat_smul,
    hb0, hb1]

public theorem standardTwoTorusEquivariantLift_eq_matrixMap
    {g : C(StdTorus 2, StdTorus 2)} {M : Matrix (Fin 2) (Fin 2) ℤ}
    (L : StandardTwoTorusEquivariantLift g M) :
    g = standardTwoTorusMatrixMap M := by
  apply ContinuousMap.ext
  have heq : (fun r : StandardTwoRealPeriods ↦ g (standardTwoTorusProjection r)) =
      fun r : StandardTwoRealPeriods ↦
        standardTwoTorusMatrixMap M (standardTwoTorusProjection r) := by
    apply standardTwoRatToReal_denseRange.equalizer
    · exact g.continuous.comp continuous_standardTwoTorusProjection
    · exact (standardTwoTorusMatrixMap M).continuous.comp
        continuous_standardTwoTorusProjection
    · funext q
      dsimp only [Function.comp_apply]
      rw [L.map_projection, standardTwoTorusMatrixMap_projection,
        standardTwoEquivariantLift_rat L q]
  intro z
  have hstep : ∀ i : Fin 2, ∃ r : ℝ, ((r : ℝ) : UnitAddCircle) = z i := fun i ↦
    QuotientAddGroup.mk_surjective (z i)
  choose r hr using hstep
  have hz : z = standardTwoTorusProjection r := by
    funext i
    exact (hr i).symm
  subst z
  exact congrFun heq r

/-- The remaining determinant calculation restricted to the explicit integer-matrix maps. -/
public def StandardTwoTorusMatrixDeterminantDegree : Prop :=
  ∀ M : Matrix (Fin 2) (Fin 2) ℤ,
    integralSingularHomologyMap 2 (standardTwoTorusMatrixMap M)
        standardTwoTorusHomologyGenerator =
      Matrix.det M • standardTwoTorusHomologyGenerator

/-- The precise two-dimensional degree statement needed for exterior-square naturality. -/
public def StandardTwoTorusDeterminantDegree : Prop :=
  ∀ (g : C(StdTorus 2, StdTorus 2)) (M : Matrix (Fin 2) (Fin 2) ℤ),
    StandardTwoTorusEquivariantLift g M →
      integralSingularHomologyMap 2 g standardTwoTorusHomologyGenerator =
        Matrix.det M • standardTwoTorusHomologyGenerator

public theorem standardTwoTorusDeterminantDegree_of_matrix
    (h : StandardTwoTorusMatrixDeterminantDegree) : StandardTwoTorusDeterminantDegree := by
  intro g M L
  rw [standardTwoTorusEquivariantLift_eq_matrixMap L]
  exact h M

private def standardPeriodPair (p : Fin 6) : Fin 2 → Fin 4 :=
  ![standardPeriodPairFirst p, standardPeriodPairSecond p]

private def standardTwoRealPlane (q : Fin 6) : StandardTwoRealPeriods →+ RealPeriods where
  toFun r k :=
    if k = standardPeriodPairFirst q then r 0
    else if k = standardPeriodPairSecond q then r 1
    else 0
  map_zero' := by
    funext k
    simp
  map_add' r s := by
    fin_cases q <;> funext k <;> fin_cases k <;>
      simp [standardPeriodPairFirst, standardPeriodPairSecond]

private def standardTwoIntegerPlane (q : Fin 6) :
    StandardTwoIntegerPeriods →+ IntegerPeriods where
  toFun n k :=
    if k = standardPeriodPairFirst q then n 0
    else if k = standardPeriodPairSecond q then n 1
    else 0
  map_zero' := by
    funext k
    simp
  map_add' r s := by
    fin_cases q <;> funext k <;> fin_cases k <;>
      simp [standardPeriodPairFirst, standardPeriodPairSecond]

private theorem standardTwoRealPlane_integer (q : Fin 6) (n : StandardTwoIntegerPeriods) :
    standardTwoRealPlane q (standardTwoIntegerToReal n) =
      integerToReal (standardTwoIntegerPlane q n) := by
  funext k
  simp [standardTwoRealPlane, standardTwoIntegerToReal, integerToReal,
    standardTwoIntegerPlane]

private theorem standardTwoIntegerPlane_decomposition
    (q : Fin 6) (n : StandardTwoIntegerPeriods) :
    standardTwoIntegerPlane q n =
      n 0 • (Pi.single (standardPeriodPairFirst q) 1 : IntegerPeriods) +
        n 1 • (Pi.single (standardPeriodPairSecond q) 1 : IntegerPeriods) := by
  fin_cases q <;> funext k <;> fin_cases k <;>
    simp [standardTwoIntegerPlane, standardPeriodPairFirst, standardPeriodPairSecond]

private theorem standardFourTorusProjection_twoRealPlane
    (q : Fin 6) (r : StandardTwoRealPeriods) :
    standardFourTorusProjection (standardTwoRealPlane q r) =
      standardFourTorusCoordinateTwoTorus q (standardTwoTorusProjection r) := by
  fin_cases q <;> funext k <;> fin_cases k <;>
    simp [standardFourTorusProjection, standardTwoRealPlane,
      standardFourTorusCoordinateTwoTorus, standardTwoTorusProjection,
      standardPeriodPairFirst, standardPeriodPairSecond]

private def standardFourTorusCoordinateTwoTorusMap
    (f : C(StdTorus 4, StdTorus 4)) (p q : Fin 6) : C(StdTorus 2, StdTorus 2) :=
  ((standardFourTorusCoordinateTwoTorusProjection p).comp f).comp
    (standardFourTorusCoordinateTwoTorus q)

private def standardFourTorusCoordinateTwoMatrix
    (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) (p q : Fin 6) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  fun a b ↦ LinearMap.toMatrix' e.toLinearMap (standardPeriodPair p a)
    (standardPeriodPair q b)

private def standardFourTorusCoordinateTwoLift
    {f : C(StdTorus 4, StdTorus 4)} {e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods}
    (L : StandardFourTorusEquivariantLift f e) (p q : Fin 6) :
    StandardTwoRealPeriods →+ StandardTwoRealPeriods where
  toFun r a := L.lift (standardTwoRealPlane q r) (standardPeriodPair p a)
  map_zero' := by
    funext a
    simp
  map_add' r s := by
    funext a
    simp

private theorem standardFourTorusCoordinateTwoLift_integer
    {f : C(StdTorus 4, StdTorus 4)} {e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods}
    (L : StandardFourTorusEquivariantLift f e) (p q : Fin 6)
    (n : StandardTwoIntegerPeriods) :
    standardFourTorusCoordinateTwoLift L p q (standardTwoIntegerToReal n) =
      standardTwoIntegerToReal
        (Matrix.mulVec (standardFourTorusCoordinateTwoMatrix e p q) n) := by
  funext a
  change L.lift (standardTwoRealPlane q (standardTwoIntegerToReal n))
      (standardPeriodPair p a) = _
  rw [standardTwoRealPlane_integer, L.map_integer]
  change ((e (standardTwoIntegerPlane q n) (standardPeriodPair p a) : ℤ) : ℝ) =
    (((standardFourTorusCoordinateTwoMatrix e p q).mulVec n a : ℤ) : ℝ)
  norm_cast
  rw [standardTwoIntegerPlane_decomposition, map_add, map_zsmul, map_zsmul]
  simp [standardFourTorusCoordinateTwoMatrix, Matrix.mulVec,
    LinearMap.toMatrix'_apply, standardPeriodPair]
  ring

private theorem standardFourTorusCoordinateTwoMap_projection
    {f : C(StdTorus 4, StdTorus 4)} {e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods}
    (L : StandardFourTorusEquivariantLift f e) (p q : Fin 6)
    (r : StandardTwoRealPeriods) :
    standardFourTorusCoordinateTwoTorusMap f p q (standardTwoTorusProjection r) =
    standardTwoTorusProjection (standardFourTorusCoordinateTwoLift L p q r) := by
  dsimp [standardFourTorusCoordinateTwoTorusMap,
    standardFourTorusCoordinateTwoTorusProjection, standardFourTorusCoordinateTwoLift,
    standardTwoTorusProjection]
  funext a
  fin_cases a
  · change f (standardFourTorusCoordinateTwoTorus q (standardTwoTorusProjection r))
        (standardPeriodPairFirst p) =
      ((L.lift (standardTwoRealPlane q r) (standardPeriodPairFirst p) : ℝ) : UnitAddCircle)
    rw [← standardFourTorusProjection_twoRealPlane]
    exact congrFun (L.map_projection (standardTwoRealPlane q r)) (standardPeriodPairFirst p)
  · change f (standardFourTorusCoordinateTwoTorus q (standardTwoTorusProjection r))
        (standardPeriodPairSecond p) =
      ((L.lift (standardTwoRealPlane q r) (standardPeriodPairSecond p) : ℝ) : UnitAddCircle)
    rw [← standardFourTorusProjection_twoRealPlane]
    exact congrFun (L.map_projection (standardTwoRealPlane q r)) (standardPeriodPairSecond p)

private def standardFourTorusCoordinateTwoEquivariantLift
    {f : C(StdTorus 4, StdTorus 4)} {e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods}
    (L : StandardFourTorusEquivariantLift f e) (p q : Fin 6) :
    StandardTwoTorusEquivariantLift (standardFourTorusCoordinateTwoTorusMap f p q)
      (standardFourTorusCoordinateTwoMatrix e p q) where
  lift := standardFourTorusCoordinateTwoLift L p q
  map_projection := standardFourTorusCoordinateTwoMap_projection L p q
  map_integer := standardFourTorusCoordinateTwoLift_integer L p q

private theorem standardFourTorusCoordinateTwoMatrix_det
    (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) (p q : Fin 6) :
    Matrix.det (standardFourTorusCoordinateTwoMatrix e p q) =
      standardSecondCompoundMatrix (LinearMap.toMatrix' e.toLinearMap) p q := by
  simp [Matrix.det_fin_two, standardFourTorusCoordinateTwoMatrix, standardPeriodPair,
    standardSecondCompoundMatrix]

/-- The homology class of one of the six coordinate two-tori. -/
public def standardFourTorusCoordinateTwoTorusHomologyClass (i : Fin 6) :
    IntegralSingularHomology 2 (StdTorus 4) :=
  integralSingularHomologyMap 2 (standardFourTorusCoordinateTwoTorus i)
    standardTwoTorusHomologyGenerator

/-- Detect a degree-two class by projecting it onto the six coordinate two-tori. -/
public noncomputable def standardFourTorusCoordinateTwoTorusHom :
    IntegralSingularHomology 2 (StdTorus 4) →+ (Fin 6 → ℤ) where
  toFun x i :=
    stdTorusHomologyTwo 2
      (integralSingularHomologyMap 2
        (standardFourTorusCoordinateTwoTorusProjection i) x)
      standardTwoTorusDegreeTwoIndex
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp

/-- Coordinate two-torus projections pair with coordinate two-torus classes by the identity
matrix in the ordering `(01, 02, 03, 12, 13, 23)`. -/
public theorem standardFourTorusCoordinateTwoTorusHom_coordinateHomologyClass (j : Fin 6) :
    standardFourTorusCoordinateTwoTorusHom
        (standardFourTorusCoordinateTwoTorusHomologyClass j) =
      Pi.single j 1 := by
  funext i
  change stdTorusHomologyTwo 2
      (integralSingularHomologyMap 2 (standardFourTorusCoordinateTwoTorusProjection i)
        (integralSingularHomologyMap 2 (standardFourTorusCoordinateTwoTorus j)
          standardTwoTorusHomologyGenerator)) standardTwoTorusDegreeTwoIndex =
    (Pi.single j 1 : Fin 6 → ℤ) i
  rw [integralSingularHomologyMap_comp_wang]
  by_cases h : i = j
  · subst i
    rw [coordinateTwoTorusProjection_comp_coordinateTwoTorus_self,
      integralSingularHomologyMap_id_wang]
    simp [standardTwoTorusHomologyGenerator]
  · rw [coordinateTwoTorusProjection_comp_coordinateTwoTorus_of_ne h,
      homologyMap_standardCircleFactor_degreeTwo_zero]
    simp [h]

public theorem standardFourTorusCoordinateTwoTorusHom_surjective :
    Function.Surjective standardFourTorusCoordinateTwoTorusHom := by
  intro v
  refine ⟨∑ i, v i • standardFourTorusCoordinateTwoTorusHomologyClass i, ?_⟩
  rw [map_sum]
  simp only [map_zsmul, standardFourTorusCoordinateTwoTorusHom_coordinateHomologyClass]
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

public theorem standardFourTorusCoordinateTwoTorusHom_injective :
    Function.Injective standardFourTorusCoordinateTwoTorusHom := by
  let F : (Fin 6 → ℤ) →+ (Fin 6 → ℤ) :=
    standardFourTorusCoordinateTwoTorusHom.comp
      (stdTorusHomologyTwo 4).symm.toAddMonoidHom
  have hsurj : Function.Surjective F :=
    standardFourTorusCoordinateTwoTorusHom_surjective.comp
      (stdTorusHomologyTwo 4).symm.surjective
  have hinj : Function.Injective F :=
    Module.End.injective_of_surjective ℤ (Fin 6 → ℤ) (f := F.toIntLinearMap) hsurj
  intro x y hxy
  apply (stdTorusHomologyTwo 4).injective
  apply hinj
  change standardFourTorusCoordinateTwoTorusHom
      ((stdTorusHomologyTwo 4).symm (stdTorusHomologyTwo 4 x)) =
    standardFourTorusCoordinateTwoTorusHom
      ((stdTorusHomologyTwo 4).symm (stdTorusHomologyTwo 4 y))
  simpa using hxy

/-- The six coordinate two-torus classes are an integral basis of degree-two homology. -/
public noncomputable def standardFourTorusCanonicalHomologyTwo :
    IntegralSingularHomology 2 (StdTorus 4) ≃+ (Fin 6 → ℤ) :=
  AddEquiv.ofBijective standardFourTorusCoordinateTwoTorusHom
    ⟨standardFourTorusCoordinateTwoTorusHom_injective,
      standardFourTorusCoordinateTwoTorusHom_surjective⟩

/-- Recalibrate the choice-based Wang basis to the coordinate two-torus basis. -/
public noncomputable def standardFourTorusCanonicalDegreeTwoRecalibration :
    (Fin 6 → ℤ) ≃+ (Fin 6 → ℤ) :=
  (stdTorusHomologyTwo 4).symm.trans standardFourTorusCanonicalHomologyTwo

public theorem standardFourTorusCanonicalDegreeTwoRecalibration_apply
    (x : IntegralSingularHomology 2 (StdTorus 4)) :
    standardFourTorusCanonicalDegreeTwoRecalibration (stdTorusHomologyTwo 4 x) =
      standardFourTorusCanonicalHomologyTwo x := by
  change standardFourTorusCanonicalHomologyTwo
      ((stdTorusHomologyTwo 4).symm (stdTorusHomologyTwo 4 x)) = _
  rw [AddEquiv.symm_apply_apply]

private theorem standardFourTorusCanonicalHomologyTwo_coordinate_naturality_of_degree
    (hdegree : StandardTwoTorusDeterminantDegree)
    (f : C(StdTorus 4, StdTorus 4)) (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods)
    (L : StandardFourTorusEquivariantLift f e) (q : Fin 6) :
    standardFourTorusCanonicalHomologyTwo
        (integralSingularHomologyMap 2 f
          (standardFourTorusCoordinateTwoTorusHomologyClass q)) =
      standardExteriorSquareMap e (Pi.single q 1) := by
  funext p
  change stdTorusHomologyTwo 2
      (integralSingularHomologyMap 2 (standardFourTorusCoordinateTwoTorusProjection p)
        (integralSingularHomologyMap 2 f
          (integralSingularHomologyMap 2 (standardFourTorusCoordinateTwoTorus q)
            standardTwoTorusHomologyGenerator))) standardTwoTorusDegreeTwoIndex = _
  rw [integralSingularHomologyMap_comp_wang, integralSingularHomologyMap_comp_wang]
  change stdTorusHomologyTwo 2
      (integralSingularHomologyMap 2 (standardFourTorusCoordinateTwoTorusMap f p q)
        standardTwoTorusHomologyGenerator) standardTwoTorusDegreeTwoIndex = _
  rw [hdegree (standardFourTorusCoordinateTwoTorusMap f p q)
      (standardFourTorusCoordinateTwoMatrix e p q)
      (standardFourTorusCoordinateTwoEquivariantLift L p q), map_zsmul,
    standardFourTorusCoordinateTwoMatrix_det]
  simp [standardTwoTorusHomologyGenerator, standardExteriorSquareMap]

private theorem sum_zsmul_pi_single_six (v : Fin 6 → ℤ) :
    ∑ j, v j • (Pi.single j 1 : Fin 6 → ℤ) = v := by
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

private theorem standardFourTorusCanonicalHomologyTwo_coordinateHomologyClass (j : Fin 6) :
    standardFourTorusCanonicalHomologyTwo
        (standardFourTorusCoordinateTwoTorusHomologyClass j) = Pi.single j 1 := by
  change standardFourTorusCoordinateTwoTorusHom
      (standardFourTorusCoordinateTwoTorusHomologyClass j) = _
  exact standardFourTorusCoordinateTwoTorusHom_coordinateHomologyClass j

/-- Exterior-square naturality in degree two follows from the determinant-degree theorem for
lifted maps of the standard two-torus. -/
public theorem standardFourTorusCanonicalHomologyTwo_naturality_of_determinantDegree
    (hdegree : StandardTwoTorusDeterminantDegree)
    (f : C(StdTorus 4, StdTorus 4)) (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods)
    (L : StandardFourTorusEquivariantLift f e)
    (x : IntegralSingularHomology 2 (StdTorus 4)) :
    standardFourTorusCanonicalHomologyTwo (integralSingularHomologyMap 2 f x) =
      standardExteriorSquareMap e (standardFourTorusCanonicalHomologyTwo x) := by
  let v := standardFourTorusCanonicalHomologyTwo x
  have hx : x = ∑ j, v j • standardFourTorusCoordinateTwoTorusHomologyClass j := by
    apply standardFourTorusCanonicalHomologyTwo.injective
    rw [map_sum]
    simp only [map_zsmul]
    rw [show ∑ j, v j • standardFourTorusCanonicalHomologyTwo
        (standardFourTorusCoordinateTwoTorusHomologyClass j) =
      ∑ j, v j • (Pi.single j 1 : Fin 6 → ℤ) by
        apply Finset.sum_congr rfl
        intro j _
        rw [standardFourTorusCanonicalHomologyTwo_coordinateHomologyClass]]
    exact (sum_zsmul_pi_single_six v).symm
  calc
    standardFourTorusCanonicalHomologyTwo (integralSingularHomologyMap 2 f x) =
        ∑ j, v j • standardFourTorusCanonicalHomologyTwo
          (integralSingularHomologyMap 2 f
            (standardFourTorusCoordinateTwoTorusHomologyClass j)) := by
      rw [hx, map_sum, map_sum]
      simp only [map_zsmul]
    _ = ∑ j, v j • standardExteriorSquareMap e (Pi.single j 1) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [standardFourTorusCanonicalHomologyTwo_coordinate_naturality_of_degree
        hdegree f e L j]
    _ = standardExteriorSquareMap e
        (∑ j, v j • (Pi.single j 1 : Fin 6 → ℤ)) := by
      rw [map_sum]
      simp only [map_zsmul]
    _ = standardExteriorSquareMap e v := by rw [sum_zsmul_pi_single_six]
    _ = standardExteriorSquareMap e (standardFourTorusCanonicalHomologyTwo x) := rfl

/-- The determinant-degree theorem for lifted maps of the standard two-torus. -/
public structure StandardFourTorusNaturalRecalibration : Prop where
  matrixDeterminantDegree : StandardTwoTorusMatrixDeterminantDegree

open CategoryTheory
open SphereSixComplex.StandardCircleHomologyLiftDegree

private theorem simplexFace_comp_simplexFace (n : ℕ) (i j : Fin (n + 2)) (h : i ≤ j) :
    (simplexFace (n + 1) j.succ).comp (simplexFace n i) =
      (simplexFace (n + 1) i.castSucc).comp (simplexFace n j) := by
  apply DFunLike.ext _ _
  intro s
  change stdSimplex.map _ (stdSimplex.map _ s) = stdSimplex.map _ (stdSimplex.map _ s)
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  have hδ := congrArg SimplexCategory.Hom.toOrderHom (SimplexCategory.δ_comp_δ h)
  have hδ' := congrArg
    (fun f : Fin (n + 1) →o Fin (n + 3) ↦ (f : Fin (n + 1) → Fin (n + 3)))
    (by simpa [SimplexCategory.comp_toOrderHom] using hδ)
  exact congrArg (fun f ↦ stdSimplex.map f s) hδ'

private noncomputable def cupOneOne {X : Type} [TopologicalSpace X]
    (u v : Chains X 1 →+ ℤ) : Chains X 2 →+ ℤ :=
  chainLift X 2 fun σ ↦
    u (simplexChain X 1 (σ.comp (simplexFace 1 2))) *
      v (simplexChain X 1 (σ.comp (simplexFace 1 0)))

private theorem cupOneOne_boundary {X : Type} [TopologicalSpace X]
    (u v : Chains X 1 →+ ℤ) (hu : u.comp (boundaryTwo X) = 0)
    (hv : v.comp (boundaryTwo X) = 0) (σ : SingularSimplex X 3) :
    cupOneOne u v ((IntegralChains X).d 3 2 (simplexChain X 3 σ)) = 0 := by
  have h02 : (simplexFace 2 0).comp (simplexFace 1 2) =
      (simplexFace 2 3).comp (simplexFace 1 0) := by
    simpa using (simplexFace_comp_simplexFace 1 0 2 (by decide)).symm
  have h12 : (simplexFace 2 1).comp (simplexFace 1 2) =
      (simplexFace 2 3).comp (simplexFace 1 1) := by
    simpa using (simplexFace_comp_simplexFace 1 1 2 (by decide)).symm
  have h10 : (simplexFace 2 1).comp (simplexFace 1 0) =
      (simplexFace 2 0).comp (simplexFace 1 0) := by
    simpa using simplexFace_comp_simplexFace 1 0 0 (by decide)
  have h20 : (simplexFace 2 2).comp (simplexFace 1 0) =
      (simplexFace 2 0).comp (simplexFace 1 1) := by
    simpa using simplexFace_comp_simplexFace 1 0 1 (by decide)
  have h22 : (simplexFace 2 2).comp (simplexFace 1 2) =
      (simplexFace 2 3).comp (simplexFace 1 2) := by
    simpa using (simplexFace_comp_simplexFace 1 2 2 (by decide)).symm
  have eu02 := congrArg (fun e ↦ u (simplexChain X 1 (σ.comp e))) h02
  have eu12 := congrArg (fun e ↦ u (simplexChain X 1 (σ.comp e))) h12
  have eu22 := congrArg (fun e ↦ u (simplexChain X 1 (σ.comp e))) h22
  have ev10 := congrArg (fun e ↦ v (simplexChain X 1 (σ.comp e))) h10
  have ev20 := congrArg (fun e ↦ v (simplexChain X 1 (σ.comp e))) h20
  have ev02 := congrArg (fun e ↦ v (simplexChain X 1 (σ.comp e))) h02
  have huσ := DFunLike.congr_fun hu (simplexChain X 2 (σ.comp (simplexFace 2 3)))
  have hvσ := DFunLike.congr_fun hv (simplexChain X 2 (σ.comp (simplexFace 2 0)))
  simp only [AddMonoidHom.comp_apply, boundaryTwo_simplex, map_add, map_sub,
    AddMonoidHom.zero_apply, ContinuousMap.comp_assoc] at huσ hvσ
  rw [boundary_simplex, map_sum]
  simp only [map_zsmul, cupOneOne, chainLift_simplex]
  simp [Fin.sum_univ_succ]
  rw [eu02, eu12, ev10, eu22, ev20, ← ev02]
  linear_combination
    v (simplexChain X 1 (σ.comp ((simplexFace 2 0).comp (simplexFace 1 0)))) * huσ -
      u (simplexChain X 1 (σ.comp ((simplexFace 2 3).comp (simplexFace 1 2)))) * hvσ

private def standardTwoTorusCircleCoordinate (i : Fin 2) :
    C(StdTorus 2, UnitAddCircle) where
  toFun z := z i
  continuous_toFun := continuous_apply i

private noncomputable def standardTwoTorusCoordinateWinding (i : Fin 2) :
    Chains (StdTorus 2) 1 →+ ℤ :=
  edgeWinding.comp ((singularChainMap (standardTwoTorusCircleCoordinate i)).f 1).hom

private theorem standardTwoTorusCoordinateWinding_cocycle (i : Fin 2) :
    (standardTwoTorusCoordinateWinding i).comp (boundaryTwo (StdTorus 2)) = 0 := by
  apply chainHom_ext (StdTorus 2) 2
  intro σ
  change edgeWinding (((singularChainMap (standardTwoTorusCircleCoordinate i)).f 1)
    (boundaryTwo (StdTorus 2) (simplexChain (StdTorus 2) 2 σ))) = 0
  rw [boundaryTwo_simplex]
  simp only [map_add, map_sub, singularChainMap_simplex]
  simpa only [boundaryTwo_simplex, map_add, map_sub, ContinuousMap.comp_assoc] using
    edgeWinding_boundaryTwo
      (simplexChain UnitAddCircle 2 ((standardTwoTorusCircleCoordinate i).comp σ))

private noncomputable def standardTwoTorusArea : Chains (StdTorus 2) 2 →+ ℤ :=
  cupOneOne (standardTwoTorusCoordinateWinding 0) (standardTwoTorusCoordinateWinding 1)

private theorem standardTwoTorusArea_comp_boundary :
    standardTwoTorusArea.comp ((IntegralChains (StdTorus 2)).d 3 2).hom = 0 := by
  apply chainHom_ext (StdTorus 2) 3
  intro σ
  exact cupOneOne_boundary _ _ (standardTwoTorusCoordinateWinding_cocycle 0)
    (standardTwoTorusCoordinateWinding_cocycle 1) σ

private noncomputable def standardTwoTorusAreaChainMap :
    IntegralChains (StdTorus 2) ⟶
      (HomologicalComplex.single AddCommGrpCat (ComplexShape.down ℕ) 2).obj
        (AddCommGrpCat.of ℤ) :=
  HomologicalComplex.mkHomToSingle (AddCommGrpCat.ofHom standardTwoTorusArea) (by
    intro i hi
    have hi' : i = 3 := by simpa using hi.symm
    subst i
    apply AddCommGrpCat.hom_ext
    exact standardTwoTorusArea_comp_boundary)

private noncomputable def standardTwoTorusHomologyArea :
    IntegralSingularHomology 2 (StdTorus 2) →+ ℤ :=
  (HomologicalComplex.homologyMap standardTwoTorusAreaChainMap 2 ≫
    (HomologicalComplex.singleObjHomologySelfIso
      (ComplexShape.down ℕ) 2 (AddCommGrpCat.of ℤ)).hom).hom

private def standardTwoTorusFirstEdge : Fin 2 → ℤ := ![1, 0]

private def standardTwoTorusSecondEdge : Fin 2 → ℤ := ![0, 1]

private def standardTwoTorusIntegerEdge (v : Fin 2 → ℤ) :
    SingularSimplex (StdTorus 2) 1 where
  toFun s i :=
    (((stdSimplexHomeomorphUnitInterval s : ℝ) * (v i : ℝ) : ℝ) : UnitAddCircle)
  continuous_toFun := by fun_prop

private def standardTwoTorusTriangleA : SingularSimplex (StdTorus 2) 2 where
  toFun s := ![((s 1 + s 2 : ℝ) : UnitAddCircle), ((s 2 : ℝ) : UnitAddCircle)]
  continuous_toFun := by
    have h1 : Continuous (fun s : Simplex 2 ↦ s 1) :=
      (continuous_apply 1).comp continuous_subtype_val
    have h2 : Continuous (fun s : Simplex 2 ↦ s 2) :=
      (continuous_apply 2).comp continuous_subtype_val
    exact continuous_pi fun i ↦ by
      fin_cases i
      · exact (AddCircle.continuous_mk' 1).comp (h1.add h2)
      · exact (AddCircle.continuous_mk' 1).comp h2

private def standardTwoTorusTriangleB : SingularSimplex (StdTorus 2) 2 where
  toFun s := ![((s 2 : ℝ) : UnitAddCircle), ((s 1 + s 2 : ℝ) : UnitAddCircle)]
  continuous_toFun := by
    have h1 : Continuous (fun s : Simplex 2 ↦ s 1) :=
      (continuous_apply 1).comp continuous_subtype_val
    have h2 : Continuous (fun s : Simplex 2 ↦ s 2) :=
      (continuous_apply 2).comp continuous_subtype_val
    exact continuous_pi fun i ↦ by
      fin_cases i
      · exact (AddCircle.continuous_mk' 1).comp h2
      · exact (AddCircle.continuous_mk' 1).comp (h1.add h2)

private theorem standardTwoTorusTriangleA_face_zero :
    standardTwoTorusTriangleA.comp (simplexFace 1 0) =
      standardTwoTorusIntegerEdge standardTwoTorusSecondEdge := by
  apply ContinuousMap.ext
  intro s
  funext i
  fin_cases i
  · apply (unitAddCircle_eq_iff _ _).mpr
    refine ⟨1, ?_⟩
    have hs := stdSimplex.sum_eq_one s
    rw [Fin.sum_univ_two] at hs
    norm_num [standardTwoTorusSecondEdge]
    rw [show (1 : Fin 3) = (0 : Fin 3).succAbove (0 : Fin 2) by decide,
      show (2 : Fin 3) = (0 : Fin 3).succAbove (1 : Fin 2) by decide,
      simplexFace_apply_succAbove, simplexFace_apply_succAbove]
    exact hs
  · apply (unitAddCircle_eq_iff _ _).mpr
    refine ⟨0, ?_⟩
    norm_num [standardTwoTorusSecondEdge]
    rw [show (2 : Fin 3) = (0 : Fin 3).succAbove (1 : Fin 2) by decide,
      simplexFace_apply_succAbove]
    exact sub_self _

private theorem standardTwoTorusTriangleA_face_two :
    standardTwoTorusTriangleA.comp (simplexFace 1 2) =
      standardTwoTorusIntegerEdge standardTwoTorusFirstEdge := by
  apply ContinuousMap.ext
  intro s
  funext i
  fin_cases i
  · apply (unitAddCircle_eq_iff _ _).mpr
    refine ⟨0, ?_⟩
    norm_num [standardTwoTorusFirstEdge]
    rw [show (1 : Fin 3) = (2 : Fin 3).succAbove (1 : Fin 2) by decide,
      simplexFace_apply_succAbove]
    exact sub_self _
  · apply (unitAddCircle_eq_iff _ _).mpr
    exact ⟨0, by norm_num [standardTwoTorusFirstEdge]⟩

private theorem standardTwoTorusTriangleB_face_zero :
    standardTwoTorusTriangleB.comp (simplexFace 1 0) =
      standardTwoTorusIntegerEdge standardTwoTorusFirstEdge := by
  apply ContinuousMap.ext
  intro s
  funext i
  fin_cases i
  · apply (unitAddCircle_eq_iff _ _).mpr
    refine ⟨0, ?_⟩
    norm_num [standardTwoTorusFirstEdge]
    rw [show (2 : Fin 3) = (0 : Fin 3).succAbove (1 : Fin 2) by decide,
      simplexFace_apply_succAbove]
    exact sub_self _
  · apply (unitAddCircle_eq_iff _ _).mpr
    refine ⟨1, ?_⟩
    have hs := stdSimplex.sum_eq_one s
    rw [Fin.sum_univ_two] at hs
    norm_num [standardTwoTorusFirstEdge]
    rw [show (1 : Fin 3) = (0 : Fin 3).succAbove (0 : Fin 2) by decide,
      show (2 : Fin 3) = (0 : Fin 3).succAbove (1 : Fin 2) by decide,
      simplexFace_apply_succAbove, simplexFace_apply_succAbove]
    exact hs

private theorem standardTwoTorusTriangleB_face_two :
    standardTwoTorusTriangleB.comp (simplexFace 1 2) =
      standardTwoTorusIntegerEdge standardTwoTorusSecondEdge := by
  apply ContinuousMap.ext
  intro s
  funext i
  fin_cases i
  · apply (unitAddCircle_eq_iff _ _).mpr
    exact ⟨0, by norm_num [standardTwoTorusSecondEdge]⟩
  · apply (unitAddCircle_eq_iff _ _).mpr
    refine ⟨0, ?_⟩
    norm_num [standardTwoTorusSecondEdge]
    rw [show (1 : Fin 3) = (2 : Fin 3).succAbove (1 : Fin 2) by decide,
      simplexFace_apply_succAbove]
    exact sub_self _

private theorem standardTwoTorusTriangle_face_one :
    standardTwoTorusTriangleA.comp (simplexFace 1 1) =
      standardTwoTorusTriangleB.comp (simplexFace 1 1) := by
  apply ContinuousMap.ext
  intro s
  funext i
  fin_cases i <;>
    apply (unitAddCircle_eq_iff _ _).mpr <;>
    exact ⟨0, by norm_num⟩

private def standardTwoTorusFundamentalCycle : Chains (StdTorus 2) 2 :=
  simplexChain (StdTorus 2) 2 standardTwoTorusTriangleA -
    simplexChain (StdTorus 2) 2 standardTwoTorusTriangleB

private theorem standardTwoTorusFundamentalCycle_isCycle :
    boundaryTwo (StdTorus 2) standardTwoTorusFundamentalCycle = 0 := by
  rw [standardTwoTorusFundamentalCycle, map_sub, boundaryTwo_simplex,
    boundaryTwo_simplex, standardTwoTorusTriangleA_face_zero,
    standardTwoTorusTriangle_face_one, standardTwoTorusTriangleA_face_two,
    standardTwoTorusTriangleB_face_zero, standardTwoTorusTriangleB_face_two]
  abel

private noncomputable def degreeTwoCycleMap {X : Type} [TopologicalSpace X]
    (c : Chains X 2) : AddCommGrpCat.of ℤ ⟶ (IntegralChains X).X 2 :=
  AddCommGrpCat.asHom c

private theorem degreeTwoCycleMap_isCycle {X : Type} [TopologicalSpace X]
    (c : Chains X 2) (hc : boundaryTwo X c = 0) :
    degreeTwoCycleMap c ≫ (IntegralChains X).d 2 1 = 0 := by
  apply AddCommGrpCat.int_hom_ext
  change boundaryTwo X ((AddCommGrpCat.asHom c) 1) = 0
  rw [AddCommGrpCat.asHom_hom_apply, one_zsmul]
  exact hc

private noncomputable def degreeTwoCycleHomologyMap {X : Type} [TopologicalSpace X]
    (c : Chains X 2) (hc : boundaryTwo X c = 0) :
    AddCommGrpCat.of ℤ ⟶ (IntegralChains X).homology 2 :=
  (IntegralChains X).liftCycles (degreeTwoCycleMap c) 1 (by simp)
      (degreeTwoCycleMap_isCycle c hc) ≫
    (IntegralChains X).homologyπ 2

private noncomputable def degreeTwoCycleHomologyClass {X : Type} [TopologicalSpace X]
    (c : Chains X 2) (hc : boundaryTwo X c = 0) : IntegralSingularHomology 2 X :=
  degreeTwoCycleHomologyMap c hc 1

private theorem degreeTwoMappedCycle_isCycle {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (c : Chains X 2) (hc : boundaryTwo X c = 0) :
    boundaryTwo Y ((singularChainMap f).f 2 c) = 0 := by
  change ((IntegralChains Y).d 2 1).hom (((singularChainMap f).f 2).hom c) = 0
  rw [← ConcreteCategory.comp_apply, (singularChainMap f).comm]
  change ((singularChainMap f).f 1).hom (boundaryTwo X c) = 0
  rw [hc, map_zero]

private theorem degreeTwoCycleMap_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (c : Chains X 2) :
    degreeTwoCycleMap c ≫ (singularChainMap f).f 2 =
      degreeTwoCycleMap ((singularChainMap f).f 2 c) := by
  apply AddCommGrpCat.int_hom_ext
  change (singularChainMap f).f 2 ((AddCommGrpCat.asHom c) 1) =
    (AddCommGrpCat.asHom ((singularChainMap f).f 2 c)) 1
  rw [AddCommGrpCat.asHom_hom_apply, AddCommGrpCat.asHom_hom_apply, one_zsmul, one_zsmul]

private theorem degreeTwoCycleHomologyMap_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (c : Chains X 2) (hc : boundaryTwo X c = 0) :
    degreeTwoCycleHomologyMap c hc ≫
        HomologicalComplex.homologyMap (singularChainMap f) 2 =
      degreeTwoCycleHomologyMap ((singularChainMap f).f 2 c)
        (degreeTwoMappedCycle_isCycle f c hc) := by
  unfold degreeTwoCycleHomologyMap
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  simp only [degreeTwoCycleMap_naturality]

private theorem degreeTwoCycleHomologyMap_area (c : Chains (StdTorus 2) 2)
    (hc : boundaryTwo (StdTorus 2) c = 0) :
    degreeTwoCycleHomologyMap c hc ≫
        HomologicalComplex.homologyMap standardTwoTorusAreaChainMap 2 ≫
          (HomologicalComplex.singleObjHomologySelfIso
            (ComplexShape.down ℕ) 2 (AddCommGrpCat.of ℤ)).hom =
      AddCommGrpCat.asHom (standardTwoTorusArea c) := by
  unfold degreeTwoCycleHomologyMap
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc]
  rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
  rw [HomologicalComplex.singleObjCyclesSelfIso_hom]
  rw [HomologicalComplex.liftCycles_i_assoc]
  apply AddCommGrpCat.int_hom_ext
  simp [standardTwoTorusAreaChainMap, degreeTwoCycleMap]
  rw [AddCommGrpCat.asHom_hom_apply, one_zsmul]

private theorem standardTwoTorusHomologyArea_cycle
    (c : Chains (StdTorus 2) 2) (hc : boundaryTwo (StdTorus 2) c = 0) :
    standardTwoTorusHomologyArea (degreeTwoCycleHomologyClass c hc) =
      standardTwoTorusArea c := by
  have h := ConcreteCategory.congr_hom (degreeTwoCycleHomologyMap_area c hc) (1 : ℤ)
  exact h.trans (by rw [AddCommGrpCat.asHom_hom_apply, one_zsmul])

private noncomputable def standardTwoTorusFundamentalClass :
    IntegralSingularHomology 2 (StdTorus 2) :=
  degreeTwoCycleHomologyClass standardTwoTorusFundamentalCycle
    standardTwoTorusFundamentalCycle_isCycle

private theorem standardTwoTorusCoordinateWinding_integerEdge
    (v : Fin 2 → ℤ) (i : Fin 2) :
    standardTwoTorusCoordinateWinding i
        (simplexChain (StdTorus 2) 1 (standardTwoTorusIntegerEdge v)) = v i := by
  unfold standardTwoTorusCoordinateWinding
  rw [AddMonoidHom.comp_apply, singularChainMap_simplex]
  change edgeWinding (simplexChain UnitAddCircle 1
    (pathSimplex (unitCircleIntegerLoop (v i)))) = v i
  rw [edgeWinding_simplex, simplexPath_pathSimplex,
    basedLoopWinding_cast, basedLoopWinding_integerLoop]

private theorem standardTwoTorusArea_fundamentalCycle :
    standardTwoTorusArea standardTwoTorusFundamentalCycle = 1 := by
  rw [standardTwoTorusFundamentalCycle, map_sub]
  simp only [standardTwoTorusArea, cupOneOne, chainLift_simplex,
    standardTwoTorusTriangleA_face_two, standardTwoTorusTriangleA_face_zero,
    standardTwoTorusTriangleB_face_two, standardTwoTorusTriangleB_face_zero,
    standardTwoTorusCoordinateWinding_integerEdge]
  norm_num [standardTwoTorusFirstEdge, standardTwoTorusSecondEdge]

private theorem standardTwoTorusHomologyArea_fundamentalClass :
    standardTwoTorusHomologyArea standardTwoTorusFundamentalClass = 1 := by
  exact (standardTwoTorusHomologyArea_cycle _ _).trans
    standardTwoTorusArea_fundamentalCycle

private theorem standardTwoTorusMatrixMap_integerEdge
    (M : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℤ) (i : Fin 2) :
    (standardTwoTorusCircleCoordinate i).comp
        ((standardTwoTorusMatrixMap M).comp (standardTwoTorusIntegerEdge v)) =
      pathSimplex (unitCircleIntegerLoop (Matrix.mulVec M v i)) := by
  apply ContinuousMap.ext
  intro s
  change (∑ b, M i b •
      (((stdSimplexHomeomorphUnitInterval s : ℝ) * (v b : ℝ) : ℝ) : UnitAddCircle)) =
    (((stdSimplexHomeomorphUnitInterval s : ℝ) *
      ((Matrix.mulVec M v i : ℤ) : ℝ) : ℝ) : UnitAddCircle)
  simp only [Fin.sum_univ_two, ← AddCircle.coe_zsmul, ← AddCircle.coe_add]
  congr 1
  simp [Matrix.mulVec, zsmul_eq_mul]
  ring

private theorem standardTwoTorusCoordinateWinding_matrix_integerEdge
    (M : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℤ) (i : Fin 2) :
    standardTwoTorusCoordinateWinding i
        (simplexChain (StdTorus 2) 1
          ((standardTwoTorusMatrixMap M).comp (standardTwoTorusIntegerEdge v))) =
      Matrix.mulVec M v i := by
  unfold standardTwoTorusCoordinateWinding
  rw [AddMonoidHom.comp_apply, singularChainMap_simplex,
    standardTwoTorusMatrixMap_integerEdge, edgeWinding_simplex,
    simplexPath_pathSimplex, basedLoopWinding_cast, basedLoopWinding_integerLoop]

private theorem standardTwoTorusArea_matrix_fundamentalCycle
    (M : Matrix (Fin 2) (Fin 2) ℤ) :
    standardTwoTorusArea
        ((singularChainMap (standardTwoTorusMatrixMap M)).f 2
          standardTwoTorusFundamentalCycle) = Matrix.det M := by
  rw [standardTwoTorusFundamentalCycle, map_sub]
  simp only [singularChainMap_simplex, standardTwoTorusArea, cupOneOne]
  rw [map_sub, chainLift_simplex, chainLift_simplex]
  simp only [ContinuousMap.comp_assoc]
  rw [standardTwoTorusTriangleA_face_two, standardTwoTorusTriangleA_face_zero,
    standardTwoTorusTriangleB_face_two, standardTwoTorusTriangleB_face_zero,
    standardTwoTorusCoordinateWinding_matrix_integerEdge,
    standardTwoTorusCoordinateWinding_matrix_integerEdge,
    standardTwoTorusCoordinateWinding_matrix_integerEdge,
    standardTwoTorusCoordinateWinding_matrix_integerEdge]
  simp [standardTwoTorusFirstEdge, standardTwoTorusSecondEdge,
    Matrix.mulVec, Matrix.det_fin_two, Matrix.vecHead, Matrix.vecTail]

private theorem standardTwoTorusHomologyArea_matrix_fundamentalClass
    (M : Matrix (Fin 2) (Fin 2) ℤ) :
    standardTwoTorusHomologyArea
        (integralSingularHomologyMap 2 (standardTwoTorusMatrixMap M)
          standardTwoTorusFundamentalClass) = Matrix.det M := by
  have hmap := ConcreteCategory.congr_hom
    (degreeTwoCycleHomologyMap_naturality (standardTwoTorusMatrixMap M)
      standardTwoTorusFundamentalCycle standardTwoTorusFundamentalCycle_isCycle) (1 : ℤ)
  rw [show integralSingularHomologyMap 2 (standardTwoTorusMatrixMap M)
      standardTwoTorusFundamentalClass =
        degreeTwoCycleHomologyClass
          ((singularChainMap (standardTwoTorusMatrixMap M)).f 2
            standardTwoTorusFundamentalCycle)
          (degreeTwoMappedCycle_isCycle (standardTwoTorusMatrixMap M)
            standardTwoTorusFundamentalCycle standardTwoTorusFundamentalCycle_isCycle) by
      exact hmap]
  exact (standardTwoTorusHomologyArea_cycle _ _).trans
    (standardTwoTorusArea_matrix_fundamentalCycle M)

private noncomputable def standardTwoTorusHomologyAreaCoordinates :
    IntegralSingularHomology 2 (StdTorus 2) →+ (Fin 1 → ℤ) where
  toFun x := fun _ : Fin 1 ↦ standardTwoTorusHomologyArea x
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp

private theorem standardTwoTorusHomologyAreaCoordinates_surjective :
    Function.Surjective standardTwoTorusHomologyAreaCoordinates := by
  intro v
  refine ⟨v 0 • standardTwoTorusFundamentalClass, ?_⟩
  funext i
  fin_cases i
  simp [standardTwoTorusHomologyAreaCoordinates, map_zsmul,
    standardTwoTorusHomologyArea_fundamentalClass]

private theorem standardTwoTorusHomologyArea_injective :
    Function.Injective standardTwoTorusHomologyArea := by
  let F : (Fin 1 → ℤ) →+ (Fin 1 → ℤ) :=
    standardTwoTorusHomologyAreaCoordinates.comp
      (stdTorusHomologyTwo 2).symm.toAddMonoidHom
  have hsurj : Function.Surjective F :=
    standardTwoTorusHomologyAreaCoordinates_surjective.comp
      (stdTorusHomologyTwo 2).symm.surjective
  have hinj : Function.Injective F :=
    Module.End.injective_of_surjective ℤ (Fin 1 → ℤ) (f := F.toIntLinearMap) hsurj
  intro x y hxy
  apply (stdTorusHomologyTwo 2).injective
  apply hinj
  change (fun _ ↦ standardTwoTorusHomologyArea
      ((stdTorusHomologyTwo 2).symm (stdTorusHomologyTwo 2 x))) =
    fun _ ↦ standardTwoTorusHomologyArea
      ((stdTorusHomologyTwo 2).symm (stdTorusHomologyTwo 2 y))
  funext i
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  exact hxy

private theorem standardTwoTorus_eq_area_smul_fundamentalClass
    (x : IntegralSingularHomology 2 (StdTorus 2)) :
    x = standardTwoTorusHomologyArea x • standardTwoTorusFundamentalClass := by
  apply standardTwoTorusHomologyArea_injective
  rw [map_zsmul, standardTwoTorusHomologyArea_fundamentalClass]
  simp

public theorem standardTwoTorusMatrixDeterminantDegree :
    StandardTwoTorusMatrixDeterminantDegree := by
  intro M
  rw [standardTwoTorus_eq_area_smul_fundamentalClass standardTwoTorusHomologyGenerator,
    map_zsmul]
  apply standardTwoTorusHomologyArea_injective
  simp only [map_zsmul, standardTwoTorusHomologyArea_matrix_fundamentalClass,
    standardTwoTorusHomologyArea_fundamentalClass]
  simp [mul_comm]

/-- The determinant-degree theorem supplies the natural four-torus recalibration. -/
public theorem standardFourTorusNaturalRecalibration_nonempty :
    Nonempty StandardFourTorusNaturalRecalibration :=
  ⟨⟨standardTwoTorusMatrixDeterminantDegree⟩⟩

public def standardFourTorusNaturalRecalibration :
    StandardFourTorusNaturalRecalibration :=
  standardFourTorusNaturalRecalibration_nonempty.some

/-- Natural degree-one coordinates on the standard four-torus. -/
public def naturalStdTorusFourHomologyOne :
    IntegralSingularHomology 1 (StdTorus 4) ≃+ (Fin 4 → ℤ) :=
  standardFourTorusCanonicalHomologyOne

/-- Natural degree-two coordinates on the standard four-torus. -/
public def naturalStdTorusFourHomologyTwo :
    IntegralSingularHomology 2 (StdTorus 4) ≃+ (Fin 6 → ℤ) :=
  standardFourTorusCanonicalHomologyTwo

public theorem naturalStdTorusFourHomology_naturality
    (f : C(StdTorus 4, StdTorus 4)) (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods)
    (L : StandardFourTorusEquivariantLift f e) :
    (∀ x, naturalStdTorusFourHomologyOne (integralSingularHomologyMap 1 f x) =
      e (naturalStdTorusFourHomologyOne x)) ∧
    (∀ x, naturalStdTorusFourHomologyTwo (integralSingularHomologyMap 2 f x) =
      standardExteriorSquareMap e (naturalStdTorusFourHomologyTwo x)) := by
  constructor
  · exact standardFourTorusCanonicalHomologyOne_naturality f e L
  · exact standardFourTorusCanonicalHomologyTwo_naturality_of_determinantDegree
      (standardTwoTorusDeterminantDegree_of_matrix
        standardFourTorusNaturalRecalibration.matrixDeterminantDegree) f e L

/-! ## The period torus in standard coordinates -/

section PeriodTorus

open Geometry Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open SphereSixComplex.Periods

variable (x : Parameters) (h : FullRank x)

/-- Real period coordinates modulo the standard integral lattice. -/
public def periodCoordMap (z : ComplexTwoSpace) : StdTorus 4 :=
  fun i ↦ ((h.realEquiv.symm z i : ℝ) : UnitAddCircle)

public theorem continuous_periodCoordMap : Continuous (periodCoordMap x h) :=
  continuous_pi fun i ↦
    (AddCircle.continuous_mk' 1).comp ((continuous_apply i).comp h.realEquiv.symm.continuous)

public theorem realEquiv_symm_periodVector (n : IntegerPeriods) :
    h.realEquiv.symm (periodVector x n) = integerToReal n := by
  apply h.realEquiv.injective
  rw [h.realEquiv.apply_symm_apply, h.map_integer]

public theorem periodCoordMap_eq_iff (z w : ComplexTwoSpace) :
    periodCoordMap x h z = periodCoordMap x h w ↔
      ∃ n : IntegerPeriods, z = periodVector x n + w := by
  constructor
  · intro hzw
    have hstep : ∀ i : Fin 4, ∃ k : ℤ,
        h.realEquiv.symm z i - h.realEquiv.symm w i = k := fun i ↦
      (unitAddCircle_eq_iff _ _).mp (congrFun hzw i)
    choose n hn using hstep
    refine ⟨n, ?_⟩
    have hreal : h.realEquiv.symm z = integerToReal n + h.realEquiv.symm w := by
      funext i
      have := hn i
      change h.realEquiv.symm z i = (n i : ℝ) + h.realEquiv.symm w i
      linarith [hn i]
    have := congrArg h.realEquiv hreal
    rw [h.realEquiv.apply_symm_apply, map_add, h.realEquiv.apply_symm_apply,
      h.map_integer] at this
    exact this
  · rintro ⟨n, rfl⟩
    funext i
    have hreal : h.realEquiv.symm (periodVector x n + w) =
        integerToReal n + h.realEquiv.symm w := by
      rw [map_add, realEquiv_symm_periodVector]
    change ((h.realEquiv.symm (periodVector x n + w) i : ℝ) : UnitAddCircle) = _
    rw [hreal]
    refine (unitAddCircle_eq_iff _ _).mpr ⟨n i, ?_⟩
    change (n i : ℝ) + h.realEquiv.symm w i - h.realEquiv.symm w i = (n i : ℝ)
    ring

public theorem periodCoordMap_orbitRel (z w : ComplexTwoSpace) :
    MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace z w ↔
      periodCoordMap x h z = periodCoordMap x h w := by
  rw [periodCoordMap_eq_iff, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨n, hn⟩ := g.toAdd.2
    refine ⟨n, ?_⟩
    have hn' : periodVector x n = (g.toAdd : ComplexTwoSpace) := hn
    rw [hn']
    exact hg.symm
  · rintro ⟨n, hn⟩
    exact ⟨Multiplicative.ofAdd ⟨periodVector x n, ⟨n, rfl⟩⟩, hn.symm⟩

/-- Standard real coordinates on a full-rank period torus. -/
public def additiveTorusStdMap : AdditiveTorus x → StdTorus 4 :=
  Quotient.lift (periodCoordMap x h) fun z w hzw ↦ (periodCoordMap_orbitRel x h z w).mp hzw

public theorem additiveTorusStdMap_injective : Function.Injective (additiveTorusStdMap x h) := by
  refine fun a b ↦ Quotient.inductionOn₂ a b fun z w hzw ↦ ?_
  exact Quotient.sound ((periodCoordMap_orbitRel x h z w).mpr hzw)

public theorem additiveTorusStdMap_surjective : Function.Surjective (additiveTorusStdMap x h) := by
  intro c
  have hstep : ∀ i : Fin 4, ∃ r : ℝ, ((r : ℝ) : UnitAddCircle) = c i := fun i ↦
    QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ)) (c i)
  choose r hr using hstep
  refine ⟨Quotient.mk _ (h.realEquiv r), ?_⟩
  show periodCoordMap x h (h.realEquiv r) = c
  funext i
  change ((h.realEquiv.symm (h.realEquiv r) i : ℝ) : UnitAddCircle) = c i
  rw [h.realEquiv.symm_apply_apply]
  exact hr i

/-- A full-rank period torus is the standard real four-torus. -/
public def additiveTorusStdHomeomorph : AdditiveTorus x ≃ₜ StdTorus 4 :=
  haveI := torus_compactSpace x h
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (additiveTorusStdMap x h)
      ⟨additiveTorusStdMap_injective x h, additiveTorusStdMap_surjective x h⟩)
    (continuous_quot_lift _ (continuous_periodCoordMap x h))

@[simp]
public theorem additiveTorusStdHomeomorph_apply (q : AdditiveTorus x) :
    additiveTorusStdHomeomorph x h q = additiveTorusStdMap x h q := rfl

end PeriodTorus

/-! ## The standard integral bases of a full-rank period torus -/

section Bases

open Geometry Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open SphereSixComplex.Periods

private theorem integralSingularHomologyEquiv_eq_map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (k : ℕ) (e : X ≃ₜ Y) (z : IntegralSingularHomology k X) :
    integralSingularHomologyEquiv k e z =
      integralSingularHomologyMap k (e : C(X, Y)) z := rfl

/-- Degree-one coordinates on the standard four-torus. -/
public def stdTorusFourHomologyOne : IntegralSingularHomology 1 (StdTorus 4) ≃+ (Fin 4 → ℤ) :=
  naturalStdTorusFourHomologyOne

/-- Degree-two coordinates on the standard four-torus. -/
public def stdTorusFourHomologyTwo : IntegralSingularHomology 2 (StdTorus 4) ≃+ (Fin 6 → ℤ) :=
  naturalStdTorusFourHomologyTwo

/-- The standard integral degree-one basis of a full-rank period torus. -/
public def additiveTorusHomologyDegreeOne (x : Parameters) (h : FullRank x) :
    IntegralSingularHomology 1 (AdditiveTorus x) ≃+ (Fin 4 → ℤ) :=
  (integralSingularHomologyEquiv 1 (additiveTorusStdHomeomorph x h)).trans
    stdTorusFourHomologyOne

private theorem additiveTorusHomologyDegreeOne_apply (x : Parameters) (h : FullRank x)
    (z : IntegralSingularHomology 1 (AdditiveTorus x)) :
    additiveTorusHomologyDegreeOne x h z =
      stdTorusFourHomologyOne
        (integralSingularHomologyEquiv 1 (additiveTorusStdHomeomorph x h) z) := rfl

/-- The standard integral degree-two basis of a full-rank period torus. -/
public def additiveTorusHomologyDegreeTwo (x : Parameters) (h : FullRank x) :
    IntegralSingularHomology 2 (AdditiveTorus x) ≃+ (Fin 6 → ℤ) :=
  (integralSingularHomologyEquiv 2 (additiveTorusStdHomeomorph x h)).trans
    stdTorusFourHomologyTwo

private theorem additiveTorusHomologyDegreeTwo_apply (x : Parameters) (h : FullRank x)
    (z : IntegralSingularHomology 2 (AdditiveTorus x)) :
    additiveTorusHomologyDegreeTwo x h z =
      stdTorusFourHomologyTwo
        (integralSingularHomologyEquiv 2 (additiveTorusStdHomeomorph x h) z) := rfl

/-- Any homeomorphism of period tori covered by the real-coordinate identification is compatible
with the standard real coordinates. -/
private theorem additiveTorusStdHomeomorph_comp (x y : Parameters) (hx : FullRank x)
    (hy : FullRank y) (e : AdditiveTorus x ≃ₜ AdditiveTorus y)
    (he : ∀ z : ComplexTwoSpace,
      e (Quotient.mk _ z) = Quotient.mk _ (hy.realEquiv (hx.realEquiv.symm z)))
    (q : AdditiveTorus x) :
    additiveTorusStdHomeomorph y hy (e q) = additiveTorusStdHomeomorph x hx q := by
  rw [additiveTorusStdHomeomorph_apply, additiveTorusStdHomeomorph_apply]
  induction q using Quotient.inductionOn with
  | _ z =>
    rw [he z]
    show periodCoordMap y hy (hy.realEquiv (hx.realEquiv.symm z)) = periodCoordMap x hx z
    funext i
    change ((hy.realEquiv.symm (hy.realEquiv (hx.realEquiv.symm z)) i : ℝ) : UnitAddCircle) = _
    rw [hy.realEquiv.symm_apply_apply]
    rfl

private theorem additiveTorusStdHomeomorph_comp_continuousMap (x y : Parameters) (hx : FullRank x)
    (hy : FullRank y) (e : AdditiveTorus x ≃ₜ AdditiveTorus y)
    (he : ∀ z : ComplexTwoSpace,
      e (Quotient.mk _ z) = Quotient.mk _ (hy.realEquiv (hx.realEquiv.symm z))) :
    ((additiveTorusStdHomeomorph y hy : C(AdditiveTorus y, StdTorus 4)).comp
        (e : C(AdditiveTorus x, AdditiveTorus y))) =
      (additiveTorusStdHomeomorph x hx : C(AdditiveTorus x, StdTorus 4)) :=
  ContinuousMap.ext fun q ↦ additiveTorusStdHomeomorph_comp x y hx hy e he q

/-- Naturality of the standard bases across a real-coordinate identification of two full-rank
period tori.

Declared as a `@[no_expose] def` rather than a `theorem` on purpose: the proof unfolds the
non-exposed `additiveTorusHomologyDegreeOne`, and the body of an exported theorem must be
checkable against the exposed interface alone. -/
@[no_expose] public def additiveTorusHomologyDegreeOne_naturality
    (x y : Parameters) (hx : FullRank x)
    (hy : FullRank y) (e : AdditiveTorus x ≃ₜ AdditiveTorus y)
    (he : ∀ z : ComplexTwoSpace,
      e (Quotient.mk _ z) = Quotient.mk _ (hy.realEquiv (hx.realEquiv.symm z)))
    (z : IntegralSingularHomology 1 (AdditiveTorus x)) :
    additiveTorusHomologyDegreeOne y hy
        (integralSingularHomologyMap 1 (e : C(AdditiveTorus x, AdditiveTorus y)) z) =
      additiveTorusHomologyDegreeOne x hx z := by
  rw [additiveTorusHomologyDegreeOne_apply, additiveTorusHomologyDegreeOne_apply]
  refine congrArg stdTorusFourHomologyOne ?_
  rw [integralSingularHomologyEquiv_eq_map, integralSingularHomologyMap_comp_wang,
    additiveTorusStdHomeomorph_comp_continuousMap x y hx hy e he,
    integralSingularHomologyEquiv_eq_map]

/-- The degree-two half of the same naturality statement.  See
`additiveTorusHomologyDegreeOne_naturality` for why this is a `@[no_expose] def`. -/
@[no_expose] public def additiveTorusHomologyDegreeTwo_naturality
    (x y : Parameters) (hx : FullRank x)
    (hy : FullRank y) (e : AdditiveTorus x ≃ₜ AdditiveTorus y)
    (he : ∀ z : ComplexTwoSpace,
      e (Quotient.mk _ z) = Quotient.mk _ (hy.realEquiv (hx.realEquiv.symm z)))
    (z : IntegralSingularHomology 2 (AdditiveTorus x)) :
    additiveTorusHomologyDegreeTwo y hy
        (integralSingularHomologyMap 2 (e : C(AdditiveTorus x, AdditiveTorus y)) z) =
      additiveTorusHomologyDegreeTwo x hx z := by
  rw [additiveTorusHomologyDegreeTwo_apply, additiveTorusHomologyDegreeTwo_apply]
  refine congrArg stdTorusFourHomologyTwo ?_
  rw [integralSingularHomologyEquiv_eq_map, integralSingularHomologyMap_comp_wang,
    additiveTorusStdHomeomorph_comp_continuousMap x y hx hy e he,
    integralSingularHomologyEquiv_eq_map]

end Bases

end StandardTorusHomologyGroups

end StandardTorusHomology

end SphereSixComplex

end

end
