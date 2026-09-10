module

public import SphereSixComplex.Prerequisites.Topology.CyclicPuncturedProductMappingTorus
public import SphereSixComplex.Prerequisites.Topology.StandardTorusHomology
public import Mathlib.Topology.Constructions

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Topology.PaperAffineCyclicReducedFiberMappingTorus
open Geometry Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.StandardTorusHomology

/-- The standard four-torus split into its `gamma` circle and the remaining three-torus. -/
public def standardFourTorusGammaSplit :
    StdTorus 4 ≃ₜ UnitAddCircle × StdTorus 3 where
  toEquiv := (Fin.consEquiv (fun _ : Fin 4 ↦ UnitAddCircle)).symm
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
public theorem standardFourTorusGammaSplit_apply (u : StdTorus 4) :
    standardFourTorusGammaSplit u = (u 0, Fin.tail u) :=
  rfl

/-! ## A normal affine cyclic quotient -/

variable {m : ℕ} {F : Type} [TopologicalSpace F]

/-- The integer lift of the normalized affine cyclic generator.  It advances the gamma circle
by `-k/m` and applies the `k`-th power of the three-torus clutching map. -/
public noncomputable def normalizedAffineShift (phi : F ≃ₜ F) (k : ℤ) :
    UnitAddCircle × F ≃ₜ UnitAddCircle × F :=
  (Homeomorph.addRight
    (-((((k : ℤ) : ℝ) / (m : ℝ) : ℝ) : UnitAddCircle))).prodCongr (phi ^ k)

@[simp]
public theorem normalizedAffineShift_apply (phi : F ≃ₜ F) (k : ℤ)
    (p : UnitAddCircle × F) :
    normalizedAffineShift (m := m) phi k p =
      (p.1 - ((((k : ℤ) : ℝ) / (m : ℝ) : ℝ) : UnitAddCircle),
        (phi ^ k) p.2) :=
  rfl

public theorem normalizedAffineShift_zero (phi : F ≃ₜ F) (p : UnitAddCircle × F) :
    normalizedAffineShift (m := m) phi 0 p = p := by
  simp

public theorem normalizedAffineShift_add (phi : F ≃ₜ F) (k l : ℤ)
    (p : UnitAddCircle × F) :
    normalizedAffineShift (m := m) phi (k + l) p =
      normalizedAffineShift (m := m) phi k (normalizedAffineShift (m := m) phi l p) := by
  rw [normalizedAffineShift_apply, normalizedAffineShift_apply, normalizedAffineShift_apply]
  apply Prod.ext
  · rw [show (((((k + l : ℤ) : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle) =
        (((((k : ℤ) : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle) +
        (((((l : ℤ) : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle) by
          rw [← QuotientAddGroup.mk_add]
          congr 1
          push_cast
          ring]
    simp only [sub_eq_add_neg, neg_add_rev]
    ac_rfl
  · rw [zpow_add]
    rfl

/-- Orbit relation of the normalized integer lift.  When `phi ^ m = 1`, this is the same
relation as the corresponding finite cyclic action. -/
public def normalizedAffineCyclicSetoid (phi : F ≃ₜ F) : Setoid (UnitAddCircle × F) where
  r p q := ∃ k : ℤ, q = normalizedAffineShift (m := m) phi k p
  iseqv := by
    refine ⟨fun p ↦ ⟨0, (normalizedAffineShift_zero phi p).symm⟩, ?_, ?_⟩
    · rintro p q ⟨k, rfl⟩
      exact ⟨-k, by rw [← normalizedAffineShift_add, neg_add_cancel,
        normalizedAffineShift_zero]⟩
    · rintro p q r ⟨k, rfl⟩ ⟨l, rfl⟩
      exact ⟨l + k, by rw [normalizedAffineShift_add]⟩

/-- The normalized affine cyclic quotient in gamma coordinates. -/
public abbrev NormalizedAffineCyclicQuotient (phi : F ≃ₜ F) :=
  Quotient (normalizedAffineCyclicSetoid (m := m) phi)

section NonzeroOrder

variable [NeZero m]

/-- Common real cover of the normalized affine cyclic quotient and its mapping torus. -/
public def normalizedAffineBaseCover (_phi : F ≃ₜ F) :
    C(ℝ × F, UnitAddCircle × F) where
  toFun w := (((w.1 / (m : ℝ) : ℝ) : UnitAddCircle), w.2)
  continuous_toFun := by fun_prop

public theorem normalizedAffineBaseCover_surjective (phi : F ≃ₜ F) :
    Function.Surjective (normalizedAffineBaseCover (m := m) phi) := by
  rintro ⟨s, x⟩
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective
    (s := AddSubgroup.zmultiples (1 : ℝ)) s
  refine ⟨((m : ℝ) * t, x), ?_⟩
  apply Prod.ext
  · change ((((m : ℝ) * t) / (m : ℝ) : ℝ) : UnitAddCircle) = s
    rw [mul_div_cancel_left₀ t (by exact_mod_cast (NeZero.ne m))]
    exact ht
  · rfl

public def normalizedAffineQuotientMap (phi : F ≃ₜ F) :
    C(ℝ × F, NormalizedAffineCyclicQuotient (m := m) phi) where
  toFun w := Quotient.mk _ (normalizedAffineBaseCover (m := m) phi w)
  continuous_toFun := continuous_quot_mk.comp
    (normalizedAffineBaseCover (m := m) phi).continuous

public theorem normalizedAffineQuotientMap_surjective (phi : F ≃ₜ F) :
    Function.Surjective (normalizedAffineQuotientMap (m := m) phi) :=
  Quotient.mk_surjective.comp (normalizedAffineBaseCover_surjective phi)

omit [NeZero m] in
public theorem isOpenMap_normalizedAffineCyclicQuotientMk (phi : F ≃ₜ F) :
    IsOpenMap (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi)) := by
  intro U hU
  rw [← (isQuotientMap_quotient_mk'
    (s := normalizedAffineCyclicSetoid (m := m) phi)).isOpen_preimage]
  show IsOpen (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi) ⁻¹'
    (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi) '' U))
  have hpre : Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi) ⁻¹'
      (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi) '' U) =
      ⋃ k : ℤ, normalizedAffineShift (m := m) phi k '' U := by
    ext q
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨u, hu, heq⟩
      change Quotient.mk _ u = Quotient.mk _ q at heq
      obtain ⟨k, hk⟩ := Quotient.exact heq
      exact ⟨k, u, hu, hk.symm⟩
    · rintro ⟨k, u, hu, hk⟩
      refine ⟨u, hu, ?_⟩
      apply Quotient.sound
      exact ⟨k, hk.symm⟩
  rw [hpre]
  exact isOpen_iUnion fun k ↦ (normalizedAffineShift (m := m) phi k).isOpenMap U hU

public theorem isOpenMap_normalizedAffineBaseCover (phi : F ≃ₜ F) :
    IsOpenMap (normalizedAffineBaseCover (m := m) phi) := by
  have hm : ((m : ℝ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast (NeZero.ne m))
  have hscale : IsOpenMap (fun t : ℝ ↦ t / (m : ℝ)) := by
    convert (Homeomorph.mulLeft₀ ((m : ℝ)⁻¹) hm).isOpenMap using 1
    funext t
    simp [div_eq_inv_mul]
  have hcircle : IsOpenMap (fun t : ℝ ↦ ((t / (m : ℝ) : ℝ) : UnitAddCircle)) :=
    (AddCircle.isLocalHomeomorph_coe (1 : ℝ)).isOpenMap.comp hscale
  exact hcircle.prodMap IsOpenMap.id

public theorem normalizedAffineQuotientMap_isQuotientMap (phi : F ≃ₜ F) :
    IsQuotientMap (normalizedAffineQuotientMap (m := m) phi) := by
  apply IsOpenMap.isQuotientMap
  · exact (isOpenMap_normalizedAffineCyclicQuotientMk phi).comp
      (isOpenMap_normalizedAffineBaseCover phi)
  · exact (normalizedAffineQuotientMap (m := m) phi).continuous
  · exact normalizedAffineQuotientMap_surjective phi

omit [NeZero m] in
public theorem homeomorph_zpow_of_dvd (phi : F ≃ₜ F) (hpow : phi ^ m = 1)
    (j : ℤ) (hj : (m : ℤ) ∣ j) : phi ^ j = 1 := by
  obtain ⟨t, rfl⟩ := hj
  rw [zpow_mul, zpow_natCast, hpow, one_zpow]

public theorem normalizedAffineQuotientMap_eq_iff
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (w w' : ℝ × F) :
    normalizedAffineQuotientMap (m := m) phi w =
        normalizedAffineQuotientMap (m := m) phi w' ↔
      Quotient.mk (realMappingTorusSetoid phi) w =
        Quotient.mk (realMappingTorusSetoid phi) w' := by
  constructor
  · intro h
    change Quotient.mk _ (normalizedAffineBaseCover (m := m) phi w) =
      Quotient.mk _ (normalizedAffineBaseCover (m := m) phi w') at h
    obtain ⟨j, hj⟩ := Quotient.exact h
    have hcircle := congrArg Prod.fst hj
    have hfibre := congrArg Prod.snd hj
    change ((w'.1 / (m : ℝ) : ℝ) : UnitAddCircle) =
      ((w.1 / (m : ℝ) - (j : ℝ) / (m : ℝ) : ℝ) : UnitAddCircle) at hcircle
    obtain ⟨n, hn⟩ := (unitAddCircle_eq_iff _ _).mp hcircle
    apply (realMappingTorusMk_eq_iff phi w w').mpr
    refine ⟨j - n * (m : ℤ), ?_⟩
    rw [mappingTorusShift_apply]
    apply Prod.ext
    · have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
      push_cast at hn ⊢
      field_simp [hm] at hn ⊢
      linarith
    · change w'.2 = (phi ^ (j - n * (m : ℤ))) w.2
      have heq : phi ^ (j - n * (m : ℤ)) = phi ^ j := by
        rw [zpow_sub, homeomorph_zpow_of_dvd phi hpow
          (n * (m : ℤ)) ⟨n, by ring⟩]
        simp
      rw [heq]
      exact hfibre
  · intro h
    obtain ⟨k, hk⟩ := (realMappingTorusMk_eq_iff phi w w').mp h
    change Quotient.mk _ (normalizedAffineBaseCover (m := m) phi w) =
      Quotient.mk _ (normalizedAffineBaseCover (m := m) phi w')
    apply Quotient.sound
    refine ⟨k, ?_⟩
    rw [hk, mappingTorusShift_apply]
    apply Prod.ext
    · change (((w.1 - (k : ℝ)) / (m : ℝ) : ℝ) : UnitAddCircle) =
        ((w.1 / (m : ℝ) - (k : ℝ) / (m : ℝ) : ℝ) : UnitAddCircle)
      congr 1
      ring
    · rfl

/-- The normalized affine cyclic quotient is the real-line model of the mapping torus. -/
public noncomputable def normalizedAffineCyclicQuotientRealMappingTorusHomeomorph
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) :
    NormalizedAffineCyclicQuotient (m := m) phi ≃ₜ RealMappingTorus phi :=
  homeomorphOfQuotientMaps
    (normalizedAffineQuotientMap_isQuotientMap phi)
    ((isOpenMap_realMappingTorusMk phi).isQuotientMap continuous_quot_mk
      Quotient.mk_surjective)
    (normalizedAffineQuotientMap_eq_iff phi hpow)

/-- The normalized affine cyclic quotient is the ordinary circle mapping torus. -/
public noncomputable def normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) :
    NormalizedAffineCyclicQuotient (m := m) phi ≃ₜ CircleMappingTorus phi :=
  (normalizedAffineCyclicQuotientRealMappingTorusHomeomorph phi hpow).trans
    (realMappingTorusHomeomorph phi)

/-! ## Recognition of a finite cyclic action in normal form -/

variable {X : Type} [TopologicalSpace X]

omit [NeZero m] in
public theorem finiteCyclicGeneratorPow_conjugates_normalizedAffineShift
    (A : MulAction (FiniteCyclic m) X) (e : X ≃ₜ UnitAddCircle × F)
    (phi : F ≃ₜ F)
    (hgen : ∀ x, e (actionMap A (cyclicGenerator m) x) =
      normalizedAffineShift (m := m) phi 1 (e x))
    (k : ℕ) (x : X) :
    e (actionMap A (cyclicGenerator m ^ k) x) =
      normalizedAffineShift (m := m) phi (k : ℤ) (e x) := by
  induction k with
  | zero =>
      simp [actionMap]
  | succ k ih =>
      calc
        e (actionMap A (cyclicGenerator m ^ (k + 1)) x) =
            e (actionMap A (cyclicGenerator m)
              (actionMap A (cyclicGenerator m ^ k) x)) := by
                rw [pow_succ', actionMap_mul]
        _ = normalizedAffineShift (m := m) phi 1
              (e (actionMap A (cyclicGenerator m ^ k) x)) := hgen _
        _ = normalizedAffineShift (m := m) phi 1
              (normalizedAffineShift (m := m) phi (k : ℤ) (e x)) := by rw [ih]
        _ = normalizedAffineShift (m := m) phi (1 + (k : ℤ)) (e x) :=
              (normalizedAffineShift_add phi 1 (k : ℤ) (e x)).symm
        _ = normalizedAffineShift (m := m) phi (k + 1 : ℕ) (e x) := by
              congr 2
              omega

public theorem normalizedAffineShift_eq_self_of_dvd
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (j : ℤ) (hj : (m : ℤ) ∣ j)
    (p : UnitAddCircle × F) :
    normalizedAffineShift (m := m) phi j p = p := by
  obtain ⟨t, rfl⟩ := hj
  rw [normalizedAffineShift_apply]
  apply Prod.ext
  · have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
    change p.1 - ((((((m : ℤ) * t : ℤ) : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle) = p.1
    rw [Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ (t : ℝ) hm]
    simp
  · rw [homeomorph_zpow_of_dvd phi hpow ((m : ℤ) * t) ⟨t, rfl⟩]
    rfl

/-- A finite cyclic action whose generator has the normalized gamma-coordinate formula has
exactly the integer-lift relation used in `NormalizedAffineCyclicQuotient`. -/
public theorem finiteCyclicOrbitRel_iff_normalizedAffineCyclicSetoid
    (A : MulAction (FiniteCyclic m) X) (e : X ≃ₜ UnitAddCircle × F)
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1)
    (hgen : ∀ x, e (actionMap A (cyclicGenerator m) x) =
      normalizedAffineShift (m := m) phi 1 (e x))
    (x y : X) :
    MulAction.orbitRel (FiniteCyclic m) X x y ↔
      normalizedAffineCyclicSetoid (m := m) phi (e x) (e y) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    rw [cyclic_eq_generator_pow g] at hg
    let k := (Multiplicative.toAdd g).val
    have hconj := finiteCyclicGeneratorPow_conjugates_normalizedAffineShift
      A e phi hgen k y
    change actionMap A (cyclicGenerator m ^ k) y = x at hg
    rw [hg] at hconj
    apply (normalizedAffineCyclicSetoid (m := m) phi).symm
    exact ⟨k, hconj⟩
  · rintro ⟨k, hk⟩
    obtain ⟨n, hn⟩ := exists_natCast_add_dvd (m := m) k
    refine ⟨cyclicGenerator m ^ n, ?_⟩
    change actionMap A (cyclicGenerator m ^ n) y = x
    apply e.injective
    rw [finiteCyclicGeneratorPow_conjugates_normalizedAffineShift A e phi hgen]
    rw [hk, ← normalizedAffineShift_add]
    exact normalizedAffineShift_eq_self_of_dvd phi hpow ((n : ℤ) + k) hn (e x)

/-- Quotient-to-mapping-torus recognition theorem.  Its only geometric input is the literal
generator formula in gamma-circle times three-torus coordinates. -/
public noncomputable def finiteCyclicOrbitQuotientCircleMappingTorusHomeomorph
    (A : MulAction (FiniteCyclic m) X) (e : X ≃ₜ UnitAddCircle × F)
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1)
    (hgen : ∀ x, e (actionMap A (cyclicGenerator m) x) =
      normalizedAffineShift (m := m) phi 1 (e x)) :
    Quotient (MulAction.orbitRel (FiniteCyclic m) X) ≃ₜ CircleMappingTorus phi :=
  (Homeomorph.Quotient.congr e fun x y ↦
    finiteCyclicOrbitRel_iff_normalizedAffineCyclicSetoid A e phi hpow hgen x y).trans
      (normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph phi hpow)

end NonzeroOrder
end SphereSixComplex.Topology.PaperAffineCyclicReducedFiberMappingTorus
