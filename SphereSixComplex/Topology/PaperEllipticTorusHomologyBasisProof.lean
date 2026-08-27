module

public import SphereSixComplex.Topology.WangHomologyPresentationProof
public import SphereSixComplex.Topology.ConnectedMayerVietorisDegreeZero
public import SphereSixComplex.Geometry.EllipticFamilySpecialization
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# The standard integral homology bases of a full-rank period torus

This file computes the integral singular homology of a real four-torus in degrees one and two,
and identifies a full-rank complex two-torus with the standard four-torus.
-/

@[expose] public section

noncomputable section

-- The two naturality statements below are `@[no_expose] def`s rather than `theorem`s, because
-- the body of an exported theorem must be checkable against the exposed interface alone.
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

/-- The standard `n`-dimensional real torus. -/
public abbrev StdTorus (n : ℕ) : Type := Fin n → UnitAddCircle

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
  stdTorusHomologyOne 4

/-- Degree-two coordinates on the standard four-torus. -/
public def stdTorusFourHomologyTwo : IntegralSingularHomology 2 (StdTorus 4) ≃+ (Fin 6 → ℤ) :=
  stdTorusHomologyTwo 4

/-- The standard integral degree-one basis of a full-rank period torus. -/
@[no_expose] public def additiveTorusHomologyDegreeOne (x : Parameters) (h : FullRank x) :
    IntegralSingularHomology 1 (AdditiveTorus x) ≃+ (Fin 4 → ℤ) :=
  (integralSingularHomologyEquiv 1 (additiveTorusStdHomeomorph x h)).trans
    stdTorusFourHomologyOne

private theorem additiveTorusHomologyDegreeOne_apply (x : Parameters) (h : FullRank x)
    (z : IntegralSingularHomology 1 (AdditiveTorus x)) :
    additiveTorusHomologyDegreeOne x h z =
      stdTorusFourHomologyOne
        (integralSingularHomologyEquiv 1 (additiveTorusStdHomeomorph x h) z) := rfl

/-- The standard integral degree-two basis of a full-rank period torus. -/
@[no_expose] public def additiveTorusHomologyDegreeTwo (x : Parameters) (h : FullRank x) :
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
