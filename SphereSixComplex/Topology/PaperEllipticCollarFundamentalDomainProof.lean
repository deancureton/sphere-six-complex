module

public import SphereSixComplex.Geometry.EllipticFilling
public import SphereSixComplex.Geometry.EllipticLocalCoordinates
public import SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
public import SphereSixComplex.Topology.IntervalClutchingQuotientCore
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The cyclic angular fundamental domain

A free scalar cyclic action on a punctured disc, diagonal with a fibre homeomorphism, has
quotient the open radial interval times the mapping torus of the fibre map.  This file proves
that general point-set theorem, `quotientHomeomorphRadialMappingTorusOfStandardMultiplier`, for
the standard clockwise multiplier `standardMultiplier m = exp (-2 π I / m)`, which is exactly the
multiplier occurring in both elliptic collars (`orderThreeMultiplier_eq_standardMultiplier` and
`orderFourMultiplier_eq_standardMultiplier`).

The normalisation of the multiplier is not cosmetic.  For a general primitive multiplier
`exp (2 π I j / m)` the quotient is the mapping torus of `φ ^ (j⁻¹ mod m)`, not of `φ`: the
angular fundamental sector runs between two consecutive rays of the rotation group, and the
group element identifying its two ends is the one rotating by `2 π / m`.  Only for
`j ≡ ± 1 [MOD m]` is that element the given generator or its inverse.

The proof never mentions arguments of complex numbers.  Polar coordinates split the punctured
product as `(0, r) × Circle × T`, the circle factor is covered by `ℝ` through `Circle.exp`, and
the induced `ℤ`-action on `ℝ × T` is exactly the deck action of the mapping torus.  The two
resulting open quotient maps out of `(0, r) × ℝ × T` have the same fibres, which gives the
homeomorphism.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Real

namespace SphereSixComplex

namespace CyclicAngularFundamentalDomain

section QuotientMaps

variable {W A B : Type*} [TopologicalSpace W] [TopologicalSpace A] [TopologicalSpace B]

/-- Two quotient maps out of a common space with the same fibres have homeomorphic targets. -/
public def homeomorphOfQuotientMaps {f : W → A} {g : W → B}
    (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (hfibre : ∀ w w' : W, f w = f w' ↔ g w = g w') : A ≃ₜ B := by
  have key : ∀ w, g (Function.surjInv hf.surjective (f w)) = g w := fun w =>
    (hfibre _ _).mp (Function.surjInv_eq hf.surjective (f w))
  have key' : ∀ w, f (Function.surjInv hg.surjective (g w)) = f w := fun w =>
    (hfibre _ _).mpr (Function.surjInv_eq hg.surjective (g w))
  refine ⟨⟨fun a => g (Function.surjInv hf.surjective a),
      fun b => f (Function.surjInv hg.surjective b), ?_, ?_⟩, ?_, ?_⟩
  · intro a
    obtain ⟨w, rfl⟩ := hf.surjective a
    simp only [key w, key' w]
  · intro b
    obtain ⟨w, rfl⟩ := hg.surjective b
    simp only [key' w, key w]
  · rw [hf.continuous_iff]
    have hcomp : (fun a => g (Function.surjInv hf.surjective a)) ∘ f = g := funext key
    rw [hcomp]
    exact hg.continuous
  · rw [hg.continuous_iff]
    have hcomp : (fun b => f (Function.surjInv hg.surjective b)) ∘ g = f := funext key'
    rw [hcomp]
    exact hf.continuous

end QuotientMaps


section OrbitQuotient

open Geometry Geometry.EquivariantQuotientHomeomorph

variable {G X : Type*} [Group G] [TopologicalSpace X]

/-- Two points of an invariant carrier have the same orbit class exactly when some group element
carries one to the other. -/
public theorem restrictedQuotientMk_eq_iff (A : MulAction G X) (S : InvariantOpenCarrier A)
    (x y : S.carrier) :
    Quotient.mk (restrictedOrbitRel A S) x = Quotient.mk (restrictedOrbitRel A S) y ↔
      ∃ g : G, restrictedActionMap S g y = x := by
  rw [Quotient.eq]
  exact Iff.rfl

/-- The restricted action of a single group element is continuous. -/
public theorem continuous_restrictedActionMap {A : MulAction G X} (S : InvariantOpenCarrier A)
    (hcont : ∀ g : G, Continuous (actionMap A g)) (g : G) :
    Continuous (restrictedActionMap S g) :=
  Continuous.subtype_mk ((hcont g).comp continuous_subtype_val) _

/-- The quotient map onto the orbit space of a continuous action on an invariant carrier is
open. -/
public theorem isOpenMap_restrictedQuotientMk (A : MulAction G X) (S : InvariantOpenCarrier A)
    (hcont : ∀ g : G, Continuous (actionMap A g)) :
    IsOpenMap (Quotient.mk (restrictedOrbitRel A S)) := by
  intro U hU
  rw [← (isQuotientMap_quotient_mk' (s := restrictedOrbitRel A S)).isOpen_preimage]
  show IsOpen (Quotient.mk (restrictedOrbitRel A S) ⁻¹'
    (Quotient.mk (restrictedOrbitRel A S) '' U))
  have hpre : Quotient.mk (restrictedOrbitRel A S) ⁻¹'
      (Quotient.mk (restrictedOrbitRel A S) '' U) =
      ⋃ g : G, restrictedActionMap S g ⁻¹' U := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨u, hu, heq⟩
      obtain ⟨g, hg⟩ := (restrictedQuotientMk_eq_iff A S u y).mp heq
      exact ⟨g, by rwa [hg]⟩
    · rintro ⟨g, hg⟩
      exact ⟨restrictedActionMap S g y, hg,
        (restrictedQuotientMk_eq_iff A S _ y).mpr ⟨g, rfl⟩⟩
  rw [hpre]
  exact isOpen_iUnion fun g => hU.preimage (continuous_restrictedActionMap S hcont g)

end OrbitQuotient


section RealMappingTorus

variable {T : Type} [TopologicalSpace T]

/-- The deck transformation of the real model of the mapping torus of `φ`. -/
public def mappingTorusShift (φ : T ≃ₜ T) (k : ℤ) : ℝ × T ≃ₜ ℝ × T :=
  (Homeomorph.subRight (k : ℝ)).prodCongr (φ ^ k)

public theorem mappingTorusShift_apply (φ : T ≃ₜ T) (k : ℤ) (p : ℝ × T) :
    mappingTorusShift φ k p = (p.1 - k, (φ ^ k) p.2) := rfl

public theorem mappingTorusShift_zero (φ : T ≃ₜ T) (p : ℝ × T) :
    mappingTorusShift φ 0 p = p := by
  rw [mappingTorusShift_apply]
  simp

public theorem mappingTorusShift_add (φ : T ≃ₜ T) (k l : ℤ) (p : ℝ × T) :
    mappingTorusShift φ (k + l) p = mappingTorusShift φ k (mappingTorusShift φ l p) := by
  rw [mappingTorusShift_apply, mappingTorusShift_apply, mappingTorusShift_apply]
  refine Prod.ext ?_ ?_
  · push_cast
    ring
  · rw [zpow_add φ k l]
    rfl

/-- The real model of the mapping torus: `ℝ × T` modulo the deck action of `φ`. -/
public def realMappingTorusSetoid (φ : T ≃ₜ T) : Setoid (ℝ × T) where
  r p q := ∃ k : ℤ, q = mappingTorusShift φ k p
  iseqv := by
    refine ⟨fun p => ⟨0, (mappingTorusShift_zero φ p).symm⟩, ?_, ?_⟩
    · rintro p q ⟨k, rfl⟩
      exact ⟨-k, by rw [← mappingTorusShift_add, neg_add_cancel, mappingTorusShift_zero]⟩
    · rintro p q r ⟨k, rfl⟩ ⟨l, rfl⟩
      exact ⟨l + k, by rw [mappingTorusShift_add]⟩

/-- The total space of the real model of the mapping torus. -/
public abbrev RealMappingTorus (φ : T ≃ₜ T) := Quotient (realMappingTorusSetoid φ)

public theorem realMappingTorusMk_eq_iff (φ : T ≃ₜ T) (p q : ℝ × T) :
    Quotient.mk (realMappingTorusSetoid φ) p = Quotient.mk (realMappingTorusSetoid φ) q ↔
      ∃ k : ℤ, q = mappingTorusShift φ k p := by
  rw [Quotient.eq]
  exact Iff.rfl

public theorem isOpenMap_realMappingTorusMk (φ : T ≃ₜ T) :
    IsOpenMap (Quotient.mk (realMappingTorusSetoid φ)) := by
  intro U hU
  rw [← (isQuotientMap_quotient_mk' (s := realMappingTorusSetoid φ)).isOpen_preimage]
  show IsOpen (Quotient.mk (realMappingTorusSetoid φ) ⁻¹'
    (Quotient.mk (realMappingTorusSetoid φ) '' U))
  have hpre : Quotient.mk (realMappingTorusSetoid φ) ⁻¹'
      (Quotient.mk (realMappingTorusSetoid φ) '' U) =
      ⋃ k : ℤ, mappingTorusShift φ k '' U := by
    ext q
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨u, hu, heq⟩
      obtain ⟨k, hk⟩ := (realMappingTorusMk_eq_iff φ u q).mp heq
      exact ⟨k, u, hu, hk.symm⟩
    · rintro ⟨k, u, hu, hk⟩
      exact ⟨u, hu, (realMappingTorusMk_eq_iff φ u q).mpr ⟨k, hk.symm⟩⟩
  rw [hpre]
  exact isOpen_iUnion fun k => (mappingTorusShift φ k).isOpenMap U hU

end RealMappingTorus


section IntervalPresentation

variable {T : Type} [TopologicalSpace T]

/-- Inclusion of the unit-interval cylinder into the real cylinder. -/
public def cylinderInclusion (T : Type) [TopologicalSpace T] : unitInterval × T → ℝ × T :=
  fun p => ((p.1 : ℝ), p.2)

public theorem isClosedMap_cylinderInclusion :
    IsClosedMap (cylinderInclusion T) :=
  ((isClosed_Icc.isClosedEmbedding_subtypeVal).prodMap
    (Topology.IsClosedEmbedding.id)).isClosedMap

/-- The unit-interval cylinder projected into the real model of the mapping torus. -/
public def realMappingTorusIntervalProjection (φ : T ≃ₜ T) :
    C(unitInterval × T, RealMappingTorus φ) :=
  ⟨fun p => Quotient.mk (realMappingTorusSetoid φ) (cylinderInclusion T p),
    continuous_quot_mk.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩

public theorem realMappingTorusIntervalProjection_apply (φ : T ≃ₜ T) (p : unitInterval × T) :
    realMappingTorusIntervalProjection φ p =
      Quotient.mk (realMappingTorusSetoid φ) ((p.1 : ℝ), p.2) := rfl

public theorem realMappingTorusIntervalProjection_surjective (φ : T ≃ₜ T) :
    Function.Surjective (realMappingTorusIntervalProjection φ) := by
  intro y
  induction y using Quotient.inductionOn with
  | _ p =>
    refine ⟨(⟨Int.fract p.1, ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩,
      (φ ^ ⌊p.1⌋) p.2), ?_⟩
    rw [realMappingTorusIntervalProjection_apply]
    exact ((realMappingTorusMk_eq_iff φ p _).mpr ⟨⌊p.1⌋, rfl⟩).symm

public theorem isClosedMap_realMappingTorusIntervalProjection (φ : T ≃ₜ T) :
    IsClosedMap (realMappingTorusIntervalProjection φ) := by
  intro F hF
  rw [← (isQuotientMap_quotient_mk' (s := realMappingTorusSetoid φ)).isClosed_preimage]
  show IsClosed (Quotient.mk (realMappingTorusSetoid φ) ⁻¹'
    (realMappingTorusIntervalProjection φ '' F))
  have hF' : IsClosed (cylinderInclusion T '' F) := isClosedMap_cylinderInclusion F hF
  have hpre : Quotient.mk (realMappingTorusSetoid φ) ⁻¹'
      (realMappingTorusIntervalProjection φ '' F) =
      ⋃ k : ℤ, mappingTorusShift φ k '' (cylinderInclusion T '' F) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨u, hu, heq⟩
      obtain ⟨k, hk⟩ := (realMappingTorusMk_eq_iff φ (cylinderInclusion T u) q).mp heq
      exact ⟨k, cylinderInclusion T u, ⟨u, hu, rfl⟩, hk.symm⟩
    · rintro ⟨k, w, ⟨u, hu, rfl⟩, hk⟩
      exact ⟨u, hu, (realMappingTorusMk_eq_iff φ (cylinderInclusion T u) q).mpr ⟨k, hk.symm⟩⟩
  rw [hpre]
  refine LocallyFinite.isClosed_iUnion ?_
    (fun k => (mappingTorusShift φ k).isClosedMap _ hF')
  intro z
  refine ⟨Set.Ioo (z.1 - 1) (z.1 + 1) ×ˢ (Set.univ : Set T), ?_, ?_⟩
  · exact (isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨⟨by linarith, by linarith⟩, trivial⟩
  · apply Set.Finite.subset (Set.finite_Icc ⌈-z.1 - 1⌉ ⌊2 - z.1⌋)
    rintro k ⟨w, ⟨v, ⟨u, _, rfl⟩, rfl⟩, hw⟩
    have h0 : (0 : ℝ) ≤ (u.1 : ℝ) := u.1.2.1
    have h1 : ((u.1 : ℝ)) ≤ 1 := u.1.2.2
    have hlt : z.1 - 1 < (u.1 : ℝ) - k ∧ (u.1 : ℝ) - k < z.1 + 1 := hw.1
    refine ⟨?_, ?_⟩
    · rw [Int.ceil_le]
      linarith [hlt.2]
    · rw [Int.le_floor]
      linarith [hlt.1]

public theorem realMappingTorusIntervalProjection_eq_iff (φ : T ≃ₜ T)
    (p q : unitInterval × T) :
    realMappingTorusIntervalProjection φ p = realMappingTorusIntervalProjection φ q ↔
      circleMappingTorusCylinderProjection φ p = circleMappingTorusCylinderProjection φ q := by
  have key : ∀ a b : Unit × unitInterval × T,
      finiteBouquetMappingTorusRelation (fun _ : Unit ↦ φ) a b →
      realMappingTorusIntervalProjection φ a.2 =
        realMappingTorusIntervalProjection φ b.2 := by
    rintro a b (⟨-, h2⟩ | ⟨ha, hb, hab⟩ | ⟨ha, hb, hab⟩)
    · rw [h2]
    · rw [show a.2 = b.2 from Prod.ext (ha.trans hb.symm) hab]
    · rw [realMappingTorusIntervalProjection_apply,
        realMappingTorusIntervalProjection_apply]
      refine (realMappingTorusMk_eq_iff φ _ _).mpr ⟨1, ?_⟩
      rw [mappingTorusShift_apply]
      refine Prod.ext ?_ ?_
      · rw [ha, hb]
        norm_num
      · rw [hab, zpow_one]
  constructor
  · intro h
    rw [realMappingTorusIntervalProjection_apply, realMappingTorusIntervalProjection_apply,
      realMappingTorusMk_eq_iff] at h
    obtain ⟨k, hk⟩ := h
    have h1 : (q.1 : ℝ) = (p.1 : ℝ) - k := congrArg Prod.fst hk
    have h2 : q.2 = (φ ^ k) p.2 := congrArg Prod.snd hk
    have hp0 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2.1
    have hp1 : ((p.1 : ℝ)) ≤ 1 := p.1.2.2
    have hq0 : (0 : ℝ) ≤ (q.1 : ℝ) := q.1.2.1
    have hq1 : ((q.1 : ℝ)) ≤ 1 := q.1.2.2
    have hkl : (-1 : ℤ) ≤ k := by
      have : (-1 : ℝ) ≤ (k : ℝ) := by linarith
      exact_mod_cast this
    have hku : k ≤ 1 := by
      have : (k : ℝ) ≤ 1 := by linarith
      exact_mod_cast this
    interval_cases k
    · have hp : (p.1 : ℝ) = 0 := by push_cast at h1; linarith
      have hq : (q.1 : ℝ) = 1 := by push_cast at h1; linarith
      refine (Quotient.sound (Relation.EqvGen.rel ((), q) ((), p) ?_)).symm
      refine Or.inr (Or.inr ⟨Subtype.ext hq, Subtype.ext hp, ?_⟩)
      rw [h2]
      change p.2 = φ ((φ ^ (-1 : ℤ)) p.2)
      rw [zpow_neg_one]
      exact (φ.apply_symm_apply p.2).symm
    · have hp : (q.1 : ℝ) = (p.1 : ℝ) := by push_cast at h1; linarith
      have : q = p := Prod.ext (Subtype.ext hp) (by rw [h2]; norm_num)
      rw [this]
    · have hp : (p.1 : ℝ) = 1 := by push_cast at h1; linarith
      have hq : (q.1 : ℝ) = 0 := by push_cast at h1; linarith
      refine Quotient.sound (Relation.EqvGen.rel ((), p) ((), q) ?_)
      refine Or.inr (Or.inr ⟨Subtype.ext hp, Subtype.ext hq, ?_⟩)
      rw [h2, zpow_one]
  · intro h
    have main : ∀ a b : Unit × unitInterval × T,
        Relation.EqvGen (finiteBouquetMappingTorusRelation (fun _ : Unit ↦ φ)) a b →
        realMappingTorusIntervalProjection φ a.2 =
          realMappingTorusIntervalProjection φ b.2 := by
      intro a b hab
      induction hab with
      | rel a b hab => exact key a b hab
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact main ((), p) ((), q) (Quotient.exact h)

/-- The interval clutching presentation of the real model of the mapping torus. -/
public def realMappingTorusClutchingData (φ : T ≃ₜ T) :
    IntervalClutchingQuotientData (RealMappingTorus φ) T φ where
  projection := realMappingTorusIntervalProjection φ
  projection_surjective := realMappingTorusIntervalProjection_surjective φ
  projection_isQuotientMap :=
    (isClosedMap_realMappingTorusIntervalProjection φ).isQuotientMap
      (realMappingTorusIntervalProjection φ).continuous
      (realMappingTorusIntervalProjection_surjective φ)
  projection_eq_iff := realMappingTorusIntervalProjection_eq_iff φ

/-- The real model of the mapping torus is the explicit circle mapping torus. -/
public def realMappingTorusHomeomorph (φ : T ≃ₜ T) :
    RealMappingTorus φ ≃ₜ CircleMappingTorus φ :=
  (realMappingTorusClutchingData φ).totalHomeomorphCircleMappingTorus

end IntervalPresentation


section Polar

open Geometry Geometry.EllipticLocalCoordinates

variable {T : Type} [TopologicalSpace T] {r : ℝ}

/-- The open radial interval occurring in a punctured disc of radius `r`. -/
public abbrev RadialInterval (r : ℝ) := {s : ℝ // 0 < s ∧ s < r}

/-- The punctured product of the disc of radius `r` with the fibre. -/
public def puncturedProduct (T : Type) [TopologicalSpace T] (r : ℝ) :
    Set (ComplexUnitDisc × T) :=
  {p | 0 < ‖(p.1 : ℂ)‖ ∧ ‖(p.1 : ℂ)‖ < r}

public theorem norm_polar (ρ : ℝ) (hρ : 0 < ρ) (u : Circle) :
    ‖((ρ : ℂ) * (u : ℂ))‖ = ρ := by
  rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ.le]

/-- Polar coordinates identify the punctured product with radius, angle and fibre. -/
public def polarHomeomorph (hr1 : r ≤ 1) :
    RadialInterval r × Circle × T ≃ₜ (puncturedProduct T r) where
  toFun q :=
    ⟨(⟨((q.1 : ℝ) : ℂ) * (q.2.1 : ℂ), by
        rw [norm_polar _ q.1.2.1]
        exact lt_of_lt_of_le q.1.2.2 hr1⟩, q.2.2), by
      refine ⟨?_, ?_⟩
      · show 0 < ‖(((q.1 : ℝ) : ℂ) * (q.2.1 : ℂ))‖
        rw [norm_polar _ q.1.2.1]
        exact q.1.2.1
      · show ‖(((q.1 : ℝ) : ℂ) * (q.2.1 : ℂ))‖ < r
        rw [norm_polar _ q.1.2.1]
        exact q.1.2.2⟩
  invFun p :=
    (⟨‖((p.1.1 : ComplexUnitDisc) : ℂ)‖, p.2⟩,
      ⟨((p.1.1 : ComplexUnitDisc) : ℂ) / ‖((p.1.1 : ComplexUnitDisc) : ℂ)‖, by
        simp [Submonoid.unitSphere, norm_pos_iff.mp p.2.1]⟩,
      p.1.2)
  left_inv q := by
    have hρ : (0 : ℝ) < (q.1 : ℝ) := q.1.2.1
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) rfl)
    · exact norm_polar _ hρ _
    · show (((q.1 : ℝ) : ℂ) * (q.2.1 : ℂ)) / ‖((q.1 : ℝ) : ℂ) * (q.2.1 : ℂ)‖ = (q.2.1 : ℂ)
      rw [norm_polar _ hρ]
      field_simp
      exact div_self (Complex.ofReal_ne_zero.mpr (ne_of_gt hρ))
  right_inv p := by
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) rfl)
    show ((‖((p.1.1 : ComplexUnitDisc) : ℂ)‖ : ℝ) : ℂ) *
      (((p.1.1 : ComplexUnitDisc) : ℂ) / ‖((p.1.1 : ComplexUnitDisc) : ℂ)‖) =
      ((p.1.1 : ComplexUnitDisc) : ℂ)
    have hne : ((‖((p.1.1 : ComplexUnitDisc) : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt p.2.1
    field_simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_
    · exact (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
    · exact continuous_snd.comp continuous_snd
  continuous_invFun := by
    have hnorm : Continuous fun p : (puncturedProduct T r) =>
        ‖((p.1.1 : ComplexUnitDisc) : ℂ)‖ :=
      continuous_norm.comp (continuous_subtype_val.comp
        (continuous_fst.comp continuous_subtype_val))
    have hval : Continuous fun p : (puncturedProduct T r) =>
        ((p.1.1 : ComplexUnitDisc) : ℂ) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
    refine Continuous.prodMk (Continuous.subtype_mk hnorm _) (Continuous.prodMk ?_ ?_)
    · refine Continuous.subtype_mk ?_ _
      exact hval.div (Complex.continuous_ofReal.comp hnorm) fun p => by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact ne_of_gt p.2.1
    · exact continuous_snd.comp continuous_subtype_val

end Polar


section AngleMap

/-- The angle map of order `m`: the parameter `θ` measures the angle in units of one `m`-th of a
full turn. -/
public def angleMap (m : ℕ) (θ : ℝ) : Circle := Circle.exp ((2 * π / m) * θ)

/-- The standard multiplier: the clockwise rotation by one `m`-th of a full turn. -/
public def standardMultiplier (m : ℕ) : ℂ :=
  Complex.exp ((-(2 * π / m) : ℝ) * Complex.I)

public theorem norm_standardMultiplier (m : ℕ) : ‖standardMultiplier m‖ = 1 :=
  Circle.norm_coe (Circle.exp (-(2 * π / m)))

/-- The degenerate case: a trivial cyclic group has the standard multiplier `1`, so `hmul` is
free for actions of `FiniteCyclic 1`. -/
@[simp] public theorem standardMultiplier_one : standardMultiplier 1 = 1 := by
  have h : Circle.exp (-(2 * π / ((1 : ℕ) : ℝ))) = 1 := by
    rw [Nat.cast_one, div_one, Circle.exp_neg, Circle.exp_two_pi, inv_one]
  exact congrArg (fun z : Circle => (z : ℂ)) h

public theorem angleMap_coe (m : ℕ) (θ : ℝ) :
    ((angleMap m θ : Circle) : ℂ) = Complex.exp (((2 * π / m) * θ : ℝ) * Complex.I) := rfl

section Nonzero

variable {m : ℕ} [NeZero m]

public theorem angleScale_ne_zero : (2 * π / m) ≠ 0 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hπ : π ≠ 0 := Real.pi_ne_zero
  positivity

public theorem isOpenMap_angleMap : IsOpenMap (angleMap m) := by
  have hscale : IsOpenMap fun θ : ℝ => (2 * π / m) * θ :=
    (Homeomorph.mulLeft₀ (2 * π / m) angleScale_ne_zero).isOpenMap
  exact isLocalHomeomorph_circleExp.isOpenMap.comp hscale

omit [NeZero m] in
public theorem continuous_angleMap : Continuous (angleMap m) :=
  Circle.exp.continuous.comp (continuous_const.mul continuous_id)

public theorem angleMap_surjective : Function.Surjective (angleMap m) := by
  intro u
  obtain ⟨t, ht⟩ := Circle.exp_surjective u
  refine ⟨t / (2 * π / m), ?_⟩
  rw [angleMap, mul_div_cancel₀ _ angleScale_ne_zero, ht]

public theorem angleMap_eq_iff (θ θ' : ℝ) :
    angleMap m θ = angleMap m θ' ↔ ∃ k : ℤ, θ = θ' + k * m := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [angleMap, angleMap, Circle.exp_eq_exp]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h := hk
    field_simp at h ⊢
    nlinarith [Real.pi_ne_zero, h]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    field_simp

omit [NeZero m] in
public theorem standardMultiplier_mul_angleMap (θ : ℝ) :
    standardMultiplier m * ((angleMap m θ : Circle) : ℂ) =
      ((angleMap m (θ - 1) : Circle) : ℂ) := by
  have : (Circle.exp (-(2 * π / m)) : Circle) * angleMap m θ = angleMap m (θ - 1) := by
    rw [angleMap, angleMap, ← Circle.exp_add]
    congr 1
    ring
  exact congrArg (fun z : Circle => (z : ℂ)) this

end Nonzero

end AngleMap


section Cover

open Geometry Geometry.EllipticLocalCoordinates

variable {T : Type} [TopologicalSpace T] {r : ℝ}

/-- The angular covering of the punctured product by radius, angle parameter and fibre. -/
public def angularCover (m : ℕ) (hr1 : r ≤ 1) (w : RadialInterval r × ℝ × T) :
    (puncturedProduct T r) :=
  polarHomeomorph hr1 (w.1, angleMap m w.2.1, w.2.2)

public theorem angularCover_fst (m : ℕ) (hr1 : r ≤ 1) (w : RadialInterval r × ℝ × T) :
    (((angularCover m hr1 w).1.1 : ComplexUnitDisc) : ℂ) =
      ((w.1 : ℝ) : ℂ) * ((angleMap m w.2.1 : Circle) : ℂ) := rfl

public theorem angularCover_snd (m : ℕ) (hr1 : r ≤ 1) (w : RadialInterval r × ℝ × T) :
    (angularCover m hr1 w).1.2 = w.2.2 := rfl

public theorem angularCover_eq (m : ℕ) (hr1 : r ≤ 1) :
    angularCover (T := T) m hr1 =
      (polarHomeomorph hr1) ∘ (Prod.map id (Prod.map (angleMap m) id)) := rfl

public theorem continuous_angularCover (m : ℕ) [NeZero m] (hr1 : r ≤ 1) :
    Continuous (angularCover (T := T) m hr1) := by
  rw [angularCover_eq]
  exact (polarHomeomorph hr1).continuous.comp
    (continuous_id.prodMap (continuous_angleMap.prodMap continuous_id))

public theorem isOpenMap_angularCover (m : ℕ) [NeZero m] (hr1 : r ≤ 1) :
    IsOpenMap (angularCover (T := T) m hr1) := by
  rw [angularCover_eq]
  exact (polarHomeomorph hr1).isOpenMap.comp
    (IsOpenMap.id.prodMap (isOpenMap_angleMap.prodMap IsOpenMap.id))

public theorem angularCover_surjective (m : ℕ) [NeZero m] (hr1 : r ≤ 1) :
    Function.Surjective (angularCover (T := T) m hr1) := by
  rw [angularCover_eq]
  exact (polarHomeomorph hr1).surjective.comp
    (Function.surjective_id.prodMap (angleMap_surjective.prodMap Function.surjective_id))

end Cover

section Main

open Geometry Geometry.EllipticLocalCoordinates Geometry.EquivariantQuotientHomeomorph

variable {m : ℕ} [NeZero m] {T : Type} [TopologicalSpace T] {r : ℝ}

public theorem actionMap_mul {G X : Type*} [Group G] (A : MulAction G X) (a b : G) (p : X) :
    actionMap A (a * b) p = actionMap A a (actionMap A b p) := by
  simp [actionMap, mul_smul]

public theorem cyclicGenerator_pow_self (m : ℕ) [NeZero m] : cyclicGenerator m ^ m = 1 := by
  rw [cyclicGenerator, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self]
  rfl

variable (A : MulAction (FiniteCyclic m) (ComplexUnitDisc × T)) (φ : T ≃ₜ T)

/-- The diagonal generator formula, in the standard-multiplier normalisation. -/
public abbrev IsStandardGenerator : Prop :=
  ∀ p : ComplexUnitDisc × T,
    actionMap A (cyclicGenerator m) p =
      (discScalarEquiv (standardMultiplier m) (norm_standardMultiplier m) p.1, φ p.2)

omit [NeZero m] in
public theorem actionMap_pow_fst (hgen : IsStandardGenerator A φ) (k : ℕ)
    (p : ComplexUnitDisc × T) :
    (((actionMap A (cyclicGenerator m ^ k) p).1 : ComplexUnitDisc) : ℂ) =
      standardMultiplier m ^ k * ((p.1 : ComplexUnitDisc) : ℂ) := by
  induction k with
  | zero => simp [actionMap]
  | succ k ih =>
      rw [pow_succ', actionMap_mul, hgen, discScalarEquiv_apply_val, ih, pow_succ']
      ring

omit [NeZero m] in
public theorem actionMap_pow_snd (hgen : IsStandardGenerator A φ) (k : ℕ)
    (p : ComplexUnitDisc × T) :
    (actionMap A (cyclicGenerator m ^ k) p).2 = (φ ^ k) p.2 := by
  induction k with
  | zero => simp [actionMap]
  | succ k ih =>
      rw [pow_succ', actionMap_mul, hgen, ih, pow_succ']
      rfl

public theorem clutching_pow_self (hgen : IsStandardGenerator A φ) : φ ^ m = 1 := by
  ext x
  have h := actionMap_pow_snd A φ hgen m (discCenter, x)
  rw [cyclicGenerator_pow_self] at h
  simpa [actionMap] using h.symm

public theorem clutching_zpow_of_dvd (hgen : IsStandardGenerator A φ) (j : ℤ)
    (hj : (m : ℤ) ∣ j) : φ ^ j = 1 := by
  obtain ⟨t, rfl⟩ := hj
  rw [zpow_mul, zpow_natCast, clutching_pow_self A φ hgen, one_zpow]

omit [NeZero m] in
public theorem standardMultiplier_pow_mul_angleMap (k : ℕ) (θ : ℝ) :
    standardMultiplier m ^ k * ((angleMap m θ : Circle) : ℂ) =
      ((angleMap m (θ - k) : Circle) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_assoc, ih, standardMultiplier_mul_angleMap,
        show θ - (k : ℝ) - 1 = θ - ((k + 1 : ℕ) : ℝ) by push_cast; ring]

public theorem polar_eq_iff (k : ℕ) (ρ ρ' : ℝ) (hρ : 0 < ρ) (hρ' : 0 < ρ') (θ θ' : ℝ) :
    standardMultiplier m ^ k * ((ρ' : ℂ) * ((angleMap m θ' : Circle) : ℂ)) =
        (ρ : ℂ) * ((angleMap m θ : Circle) : ℂ) ↔
      ρ' = ρ ∧ ∃ l : ℤ, θ' - k = θ + l * m := by
  have hne : ((ρ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hρ)
  have hrewrite : standardMultiplier m ^ k * ((ρ' : ℂ) * ((angleMap m θ' : Circle) : ℂ)) =
      (ρ' : ℂ) * ((angleMap m (θ' - k) : Circle) : ℂ) := by
    rw [← standardMultiplier_pow_mul_angleMap]
    ring
  rw [hrewrite]
  constructor
  · intro h
    have hρρ : ρ' = ρ := by
      have h1 : ‖((ρ' : ℝ) : ℂ) * ((angleMap m (θ' - k) : Circle) : ℂ)‖ = ρ' :=
        norm_polar _ hρ' _
      have h2 : ‖((ρ : ℝ) : ℂ) * ((angleMap m θ : Circle) : ℂ)‖ = ρ := norm_polar _ hρ _
      rw [← h1, h, h2]
    subst hρρ
    have h3 : ((angleMap m (θ' - k) : Circle) : ℂ) = ((angleMap m θ : Circle) : ℂ) :=
      mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hρ')) h
    exact ⟨rfl, (angleMap_eq_iff (θ' - k) θ).mp (Circle.ext h3)⟩
  · rintro ⟨hρρ, l, hl⟩
    subst hρρ
    rw [(angleMap_eq_iff (θ' - k) θ).mpr ⟨l, hl⟩]

public theorem exists_natCast_add_dvd (K : ℤ) :
    ∃ k : ℕ, (m : ℤ) ∣ ((k : ℤ) + K) := by
  have hm : (0 : ℤ) < (m : ℤ) := Int.natCast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  refine ⟨((-K) % (m : ℤ)).toNat, ?_⟩
  have hnn : 0 ≤ (-K) % (m : ℤ) := Int.emod_nonneg _ (ne_of_gt hm)
  rw [Int.toNat_of_nonneg hnn, Int.emod_def]
  exact ⟨-((-K) / (m : ℤ)), by ring⟩

/-- The angular quotient presentation of the orbit space. -/
public def angularQuotientMap (hr1 : r ≤ 1) (S : InvariantOpenCarrier A)
    (hS : S.carrier = puncturedProduct T r) (w : RadialInterval r × ℝ × T) :
    Quotient (restrictedOrbitRel A S) :=
  Quotient.mk _ ((Homeomorph.setCongr hS).symm (angularCover m hr1 w))

/-- The radial mapping-torus presentation of the same space. -/
public def radialTorusMap (w : RadialInterval r × ℝ × T) :
    RadialInterval r × RealMappingTorus φ :=
  (w.1, Quotient.mk (realMappingTorusSetoid φ) w.2)

omit [NeZero m] in
public theorem radialTorusMap_eq :
    radialTorusMap (r := r) φ = Prod.map id (Quotient.mk (realMappingTorusSetoid φ)) := rfl

public theorem isQuotientMap_radialTorusMap :
    IsQuotientMap (radialTorusMap (r := r) φ) := by
  rw [radialTorusMap_eq]
  refine IsOpenMap.isQuotientMap (IsOpenMap.id.prodMap (isOpenMap_realMappingTorusMk φ))
    (continuous_id.prodMap continuous_quot_mk)
    (Function.surjective_id.prodMap Quotient.mk_surjective)

public theorem isQuotientMap_angularQuotientMap (hr1 : r ≤ 1) (S : InvariantOpenCarrier A)
    (hS : S.carrier = puncturedProduct T r) (hcont : ∀ g, Continuous (actionMap A g)) :
    IsQuotientMap (angularQuotientMap A hr1 S hS) := by
  refine IsOpenMap.isQuotientMap ?_ ?_ ?_
  · exact ((isOpenMap_restrictedQuotientMk A S hcont).comp
      (Homeomorph.setCongr hS).symm.isOpenMap).comp (isOpenMap_angularCover m hr1)
  · exact continuous_quot_mk.comp
      ((Homeomorph.setCongr hS).symm.continuous.comp (continuous_angularCover m hr1))
  · exact (Quotient.mk_surjective.comp
      (Homeomorph.setCongr hS).symm.surjective).comp (angularCover_surjective m hr1)


public theorem angularQuotientMap_eq_iff (hr1 : r ≤ 1) (S : InvariantOpenCarrier A)
    (hS : S.carrier = puncturedProduct T r) (hgen : IsStandardGenerator A φ)
    (w w' : RadialInterval r × ℝ × T) :
    angularQuotientMap A hr1 S hS w = angularQuotientMap A hr1 S hS w' ↔
      radialTorusMap φ w = radialTorusMap φ w' := by
  rw [angularQuotientMap, angularQuotientMap, restrictedQuotientMk_eq_iff]
  constructor
  · rintro ⟨g, hg⟩
    rw [cyclic_eq_generator_pow g] at hg
    set k := (Multiplicative.toAdd g).val with hkdef
    have hval : actionMap A (cyclicGenerator m ^ k)
        ((angularCover m hr1 w' : (puncturedProduct T r)) : ComplexUnitDisc × T) =
        ((angularCover m hr1 w : (puncturedProduct T r)) : ComplexUnitDisc × T) :=
      congrArg Subtype.val hg
    have hfst : standardMultiplier m ^ k *
        (((w'.1 : ℝ) : ℂ) * ((angleMap m w'.2.1 : Circle) : ℂ)) =
        ((w.1 : ℝ) : ℂ) * ((angleMap m w.2.1 : Circle) : ℂ) := by
      rw [← angularCover_fst m hr1 w, ← angularCover_fst m hr1 w',
        ← actionMap_pow_fst A φ hgen k]
      exact congrArg (fun p : ComplexUnitDisc × T => ((p.1 : ComplexUnitDisc) : ℂ)) hval
    have hsnd : (φ ^ k) w'.2.2 = w.2.2 := by
      rw [← angularCover_snd m hr1 w, ← angularCover_snd m hr1 w',
        ← actionMap_pow_snd A φ hgen k]
      exact congrArg (fun p : ComplexUnitDisc × T => p.2) hval
    obtain ⟨hρ, l, hl⟩ := (polar_eq_iff k _ _ w.1.2.1 w'.1.2.1 _ _).mp hfst
    refine Prod.ext (Subtype.ext hρ.symm) ?_
    refine (realMappingTorusMk_eq_iff φ w.2 w'.2).mpr ⟨-((k : ℤ) + l * m), ?_⟩
    rw [mappingTorusShift_apply]
    refine Prod.ext ?_ ?_
    · push_cast
      linarith
    · have hzp : (φ ^ (-((k : ℤ) + l * (m : ℤ)))) = φ ^ (-(k : ℤ)) := by
        rw [neg_add, zpow_add,
          clutching_zpow_of_dvd A φ hgen (-(l * (m : ℤ))) ⟨-l, by ring⟩, mul_one]
      rw [hzp, ← hsnd, zpow_neg, zpow_natCast, Homeomorph.inv_apply]
      exact ((φ ^ k).symm_apply_apply w'.2.2).symm
  · intro h
    have h1 : (radialTorusMap φ w).1 = (radialTorusMap φ w').1 := congrArg Prod.fst h
    have h2 : (radialTorusMap φ w).2 = (radialTorusMap φ w').2 := congrArg Prod.snd h
    obtain ⟨K, hK⟩ := (realMappingTorusMk_eq_iff φ w.2 w'.2).mp h2
    rw [mappingTorusShift_apply] at hK
    have hθ : w'.2.1 = w.2.1 - (K : ℝ) := congrArg Prod.fst hK
    have hx : w'.2.2 = (φ ^ K) w.2.2 := congrArg Prod.snd hK
    obtain ⟨k, t, ht⟩ := exists_natCast_add_dvd (m := m) K
    refine ⟨cyclicGenerator m ^ k, Subtype.ext ?_⟩
    show actionMap A (cyclicGenerator m ^ k)
        ((angularCover m hr1 w' : (puncturedProduct T r)) : ComplexUnitDisc × T) =
      ((angularCover m hr1 w : (puncturedProduct T r)) : ComplexUnitDisc × T)
    refine Prod.ext (Subtype.ext ?_) ?_
    · rw [actionMap_pow_fst A φ hgen k, angularCover_fst, angularCover_fst]
      refine (polar_eq_iff k _ _ w.1.2.1 w'.1.2.1 _ _).mpr
        ⟨congrArg (fun z : RadialInterval r => (z : ℝ)) h1.symm, -t, ?_⟩
      have htR : (k : ℝ) + (K : ℝ) = (m : ℝ) * (t : ℝ) := by exact_mod_cast ht
      rw [hθ]
      push_cast
      linarith
    · rw [actionMap_pow_snd A φ hgen k, angularCover_snd, angularCover_snd, hx]
      have hone : (φ ^ (k : ℤ)) * (φ ^ K) = 1 := by
        rw [← zpow_add]
        exact clutching_zpow_of_dvd A φ hgen _ ⟨t, ht⟩
      calc (φ ^ k) ((φ ^ K) w.2.2)
          = ((φ ^ (k : ℤ)) * (φ ^ K)) w.2.2 := by
            rw [Homeomorph.mul_apply, zpow_natCast]
        _ = w.2.2 := by rw [hone]; rfl

omit [NeZero m] in
/-- Recognising the standard generator formula from an arbitrary multiplier known to be the
standard one. -/
public theorem isStandardGenerator_of_multiplier_eq (lambda : ℂ) (hlambda : ‖lambda‖ = 1)
    (hmul : lambda = standardMultiplier m)
    (hgen : ∀ p : ComplexUnitDisc × T,
      actionMap A (cyclicGenerator m) p = (discScalarEquiv lambda hlambda p.1, φ p.2)) :
    IsStandardGenerator A φ := by
  intro p
  rw [hgen p]
  congr 1
  apply Subtype.ext
  rw [discScalarEquiv_apply_val, discScalarEquiv_apply_val, hmul]

/-- **The angular fundamental-domain theorem.**  A cyclic action on a punctured disc--fibre
product whose generator rotates the disc clockwise by one `m`-th of a full turn and acts on the
fibre by `φ` has quotient the open radial interval times the mapping torus of `φ`.

The angular sector runs from the generator ray to the identity ray, so the clutching map is `φ`
itself rather than its inverse. -/
public def quotientHomeomorphRadialMappingTorusOfStandardMultiplier
    (hr1 : r ≤ 1) (S : InvariantOpenCarrier A)
    (hS : S.carrier = puncturedProduct T r) (hgen : IsStandardGenerator A φ)
    (hcont : ∀ g : FiniteCyclic m, Continuous (actionMap A g)) :
    Quotient (restrictedOrbitRel A S) ≃ₜ
      {s : ℝ // 0 < s ∧ s < r} × CircleMappingTorus φ :=
  (homeomorphOfQuotientMaps (isQuotientMap_angularQuotientMap A hr1 S hS hcont)
      (isQuotientMap_radialTorusMap (r := r) φ)
      (angularQuotientMap_eq_iff A φ hr1 S hS hgen)).trans
    ((Homeomorph.refl (RadialInterval r)).prodCongr (realMappingTorusHomeomorph φ))

end Main

section ActualMultipliers

open Geometry Geometry.EllipticLocalCoordinates

/-- The order-three collar multiplier is the standard clockwise third of a turn. -/
public theorem orderThreeMultiplier_eq_standardMultiplier :
    orderThreeMultiplier = standardMultiplier 3 := by
  have hsplit : (2 * π / (3 : ℕ) : ℝ) = π - π / 3 := by
    push_cast
    ring
  apply Complex.ext
  · show (-1 / 2 : ℝ) = (Complex.exp (((-(2 * π / (3 : ℕ)) : ℝ) : ℂ) * Complex.I)).re
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg, hsplit, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  · show (-Real.sqrt 3 / 2 : ℝ) = (Complex.exp (((-(2 * π / (3 : ℕ)) : ℝ) : ℂ) * Complex.I)).im
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg, hsplit, Real.sin_pi_sub,
      Real.sin_pi_div_three]
    ring

/-- The order-four collar multiplier is the standard clockwise quarter of a turn. -/
public theorem orderFourMultiplier_eq_standardMultiplier :
    orderFourMultiplier = standardMultiplier 4 := by
  have hsplit : (2 * π / (4 : ℕ) : ℝ) = π / 2 := by
    push_cast
    ring
  apply Complex.ext
  · show (-Complex.I).re = (Complex.exp (((-(2 * π / (4 : ℕ)) : ℝ) : ℂ) * Complex.I)).re
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg, hsplit, Real.cos_pi_div_two]
    simp
  · show (-Complex.I).im = (Complex.exp (((-(2 * π / (4 : ℕ)) : ℝ) : ℂ) * Complex.I)).im
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg, hsplit, Real.sin_pi_div_two]
    simp

end ActualMultipliers

end CyclicAngularFundamentalDomain

end SphereSixComplex
