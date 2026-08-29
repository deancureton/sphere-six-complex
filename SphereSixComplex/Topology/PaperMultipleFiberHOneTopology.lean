module

public import SphereSixComplex.Topology.PaperMultipleFiberHOneTopologyProof
public import SphereSixComplex.Topology.CyclicExtensionAbelianization
public import SphereSixComplex.Topology.EstablishedUnwrappedAffineFillings

/-!
# First homology of the reduced elliptic fibres

This file isolates the standard covering-space calculation for a free affine cyclic quotient
of a torus.  The hypotheses retain the affine lift, including the lattice translation made by
its full cyclic iterate, so the resulting multiple-fibre presentation records the correct
extension class rather than only the linear monodromy.
-/

open AlgebraicTopology

namespace SphereSixComplex.Topology.PaperMultipleFiberHOneTopology

open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus Geometry.GlobalTorusFamily
open Geometry.EllipticFamilySpecialization Geometry.EllipticFixedPointCriterion
open LatticeData Periods TriangleGroup
open PaperEllipticFillingRadialRetraction
open PaperEllipticReducedCentralFiberCoverModels
open PaperLemmaSevenThirteenAlgebra TwistObstruction

noncomputable section

namespace EstablishedAffineCyclicQuotientHomology

variable {m : ℕ} [NeZero m] {p : SphereSixComplex.Periods.Parameters}
  {D : RadialEllipticActionData m (AdditiveTorus p)}

/-- The canonical map from the affine universal-cover coordinates to the reduced central fibre. -/
@[expose] public def complexTwoReducedCentralFiberProjection :
    C(ComplexTwoSpace, D.reducedCentralFiber) :=
  (RadialEllipticActionData.centralFiberCoverProjection D).comp
    ((⟨(RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm,
      (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm.continuous⟩ :
        C(AdditiveTorus p, RadialEllipticActionData.centralFiberCoverSource D)).comp
      ⟨torusProjection p, continuous_quot_mk⟩)

private theorem affineEquiv_pow_sub {T : Type*} [AddCommGroup T]
    (A : T ≃+ T) (b : T) (n : ℕ) (x y : T) :
    (affineEquiv A b ^ n) x - (affineEquiv A b ^ n) y =
      (A.toEquiv ^ n) (x - y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        affineEquiv_apply, affineEquiv_apply, add_sub_add_right_eq_sub, ← map_sub, ih]
      rw [pow_succ', Equiv.Perm.mul_apply]
      rfl

private theorem lift_period_pow
    (A : DescendedAffineTorusAutomorphism p) (n : ℕ) (x : Lattice) :
    (A.lift.toEquiv ^ n) (periodVector p x) =
      periodVector p ((A.latticeMap.toEquiv ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, ih]
      exact A.lift_period _

private theorem addAut_nsmul_apply {T : Type*} [AddGroup T]
    (A : AddAut T) (n : ℕ) (x : T) :
    (n • A) x = (A.toEquiv ^ n) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, AddAut.add_apply, ih, pow_succ, Equiv.Perm.mul_apply]
      rfl

/-- The full-iterate affine lift forces the integral linear monodromy to have order dividing the
cyclic degree. -/
public theorem affineLatticeMap_pow_eq_one
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    P.affine.latticeMap.toEquiv ^ m = 1 := by
  apply Equiv.ext
  intro x
  apply (periodHom_injective P.fullRank)
  change periodVector p ((P.affine.latticeMap.toEquiv ^ m) x) = periodVector p x
  rw [← lift_period_pow]
  have h := affineEquiv_pow_sub P.affine.lift P.liftTranslation m
    (periodVector p x) 0
  rw [P.lift_full_iterate, P.lift_full_iterate, add_sub_add_right_eq_sub, sub_zero] at h
  exact h.symm

/-- The full-iterate translation is fixed by the integral linear monodromy. -/
public theorem affineLatticeMap_twist
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    P.affine.latticeMap P.twist = P.twist := by
  apply (periodHom_injective P.fullRank)
  change periodVector p (P.affine.latticeMap P.twist) = periodVector p P.twist
  rw [← P.affine.lift_period]
  let f := affineEquiv P.affine.lift P.liftTranslation
  have hcomm : f ((f ^ m) 0) = (f ^ m) (f 0) := by
    change (f * f ^ m) 0 = (f ^ m * f) 0
    rw [← pow_succ', ← pow_succ]
  change P.affine.lift (periodVector p P.twist) = periodVector p P.twist
  have ht : (f ^ m) 0 = periodVector p P.twist := by
    simpa [f] using P.lift_full_iterate 0
  rw [ht] at hcomm
  rw [P.lift_full_iterate] at hcomm
  apply add_right_cancel (b := P.liftTranslation)
  simpa [f, affineEquiv_apply, add_comm] using hcomm

/-- The canonical unwrapped affine deck presentation determined by `P`. -/
@[expose] public def affineCyclicBoundaryDeckData
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    UnwrappedCyclicAffineBoundaryDeckData m Lattice
      (CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv) :=
  canonicalCyclicAffineBoundaryDeckData P.affine.latticeMap.toAddEquiv P.twist (by
    apply Multiplicative.toAdd.injective
    change m • P.affine.latticeMap.toAddEquiv = 0
    apply AddEquiv.ext
    intro x
    have h := congrArg (fun e : Equiv.Perm Lattice ↦ e x) (affineLatticeMap_pow_eq_one P)
    change (P.affine.latticeMap.toAddEquiv.toEquiv ^ m) x = x at h
    simpa [addAut_nsmul_apply] using h) (affineLatticeMap_twist P)

private theorem meridian_pow_conjugate
    {m : ℕ} {Λ G : Type*} [NeZero m] [AddCommGroup Λ] [Group G]
    (D : UnwrappedCyclicAffineBoundaryDeckData m Λ G) (n : ℕ) (a : Λ) :
    D.meridian ^ n * Additive.toMul (D.translation a) * (D.meridian ^ n)⁻¹ =
      Additive.toMul (D.translation ((D.monodromy ^ n).toAdd a)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        D.meridian ^ (n + 1) * Additive.toMul (D.translation a) *
              (D.meridian ^ (n + 1))⁻¹ =
            D.meridian *
              (D.meridian ^ n * Additive.toMul (D.translation a) *
                (D.meridian ^ n)⁻¹) * D.meridian⁻¹ := by
                  rw [pow_succ']
                  group
        _ = D.meridian *
              Additive.toMul (D.translation ((D.monodromy ^ n).toAdd a)) *
                D.meridian⁻¹ := by rw [ih]
        _ = Additive.toMul
              (D.translation (D.monodromy.toAdd ((D.monodromy ^ n).toAdd a))) :=
            D.conjugate _
        _ = Additive.toMul (D.translation ((D.monodromy ^ (n + 1)).toAdd a)) := by
            rw [pow_succ']
            rfl

private theorem fillingRelation_commute_translation
    {m : ℕ} {Λ G : Type*} [NeZero m] [AddCommGroup Λ] [Group G]
    (D : UnwrappedCyclicAffineBoundaryDeckData m Λ G) (a : Λ) :
    Commute D.fillingRelation (Additive.toMul (D.translation a)) := by
  have hpow := meridian_pow_conjugate D m a
  rw [D.monodromy_pow] at hpow
  have hpcomm :
      Commute (D.meridian ^ m) (Additive.toMul (D.translation a)) := by
    rw [commute_iff_eq]
    simpa using mul_inv_eq_iff_eq_mul.mp hpow
  have htcomm :
      Commute (Additive.toMul (D.translation D.twist))
        (Additive.toMul (D.translation a)) := by
    rw [commute_iff_eq]
    have hadd : D.translation D.twist + D.translation a =
        D.translation a + D.translation D.twist := by
      rw [← D.translation.map_add, add_comm D.twist a, D.translation.map_add]
    exact congrArg Additive.toMul hadd
  exact hpcomm.mul_left htcomm.inv_left

private theorem fillingRelation_commute_meridian
    {m : ℕ} {Λ G : Type*} [NeZero m] [AddCommGroup Λ] [Group G]
    (D : UnwrappedCyclicAffineBoundaryDeckData m Λ G) :
    Commute D.fillingRelation D.meridian := by
  have htcomm : Commute (Additive.toMul (D.translation D.twist)) D.meridian := by
    rw [commute_iff_eq]
    have h := D.conjugate D.twist
    rw [D.twist_fixed] at h
    exact (eq_mul_of_mul_inv_eq h).symm
  exact (Commute.refl D.meridian).pow_left m |>.mul_left htcomm.inv_left

private theorem fillingRelation_central
    {m : ℕ} {Λ G : Type*} [NeZero m] [AddCommGroup Λ] [Group G]
    (D : UnwrappedCyclicAffineBoundaryDeckData m Λ G) :
    ∀ g, Commute D.fillingRelation g := by
  intro g
  suffices g ∈ Subgroup.centralizer {D.fillingRelation} by
    exact (Subgroup.mem_centralizer_iff.mp this) D.fillingRelation (Set.mem_singleton _)
  have hg :
      g ∈ Subgroup.closure
        (Set.range (fun a ↦ Additive.toMul (D.translation a)) ∪ {D.meridian}) := by
    rw [D.generators_generate]
    trivial
  apply (Subgroup.closure_le _).mpr _ hg
  rintro x (⟨a, rfl⟩ | hx)
  · exact Subgroup.mem_centralizer_iff.mpr fun y hy ↦ by
      rw [Set.mem_singleton_iff.mp hy]
      exact fillingRelation_commute_translation D a
  · rw [Set.mem_singleton_iff.mp hx]
    exact Subgroup.mem_centralizer_iff.mpr fun y hy ↦ by
      rw [Set.mem_singleton_iff.mp hy]
      exact fillingRelation_commute_meridian D

private theorem fillingKernel_eq_zpowers
    {m : ℕ} {Λ G : Type*} [NeZero m] [AddCommGroup Λ] [Group G]
    (D : UnwrappedCyclicAffineBoundaryDeckData m Λ G) :
    D.fillingKernel = Subgroup.zpowers D.fillingRelation := by
  let _ : (Subgroup.zpowers D.fillingRelation).Normal := ⟨by
    intro n hn g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have h := (fillingRelation_central D g).zpow_left k
    have : g * D.fillingRelation ^ k * g⁻¹ = D.fillingRelation ^ k := by
      rw [← h.eq]
      group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k⟩
  rw [UnwrappedCyclicAffineBoundaryDeckData.fillingKernel]
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal (by simp)
  · rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_le_normalClosure

private theorem affineCyclicFillingRelation_right
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    (affineCyclicBoundaryDeckData P).fillingRelation.right =
      Multiplicative.ofAdd (m : ℤ) := by
  change
    (SemidirectProduct.inr
        (φ := integerAffineMonodromy P.affine.latticeMap.toAddEquiv)
        (Multiplicative.ofAdd 1) ^ m *
      (SemidirectProduct.inl (Multiplicative.ofAdd P.twist))⁻¹).right = _
  have hmeridian :
      (SemidirectProduct.inr
          (φ := integerAffineMonodromy P.affine.latticeMap.toAddEquiv)
          (Multiplicative.ofAdd 1) ^ m).right = Multiplicative.ofAdd (m : ℤ) := by
    rw [show SemidirectProduct.inr
          (φ := integerAffineMonodromy P.affine.latticeMap.toAddEquiv)
          (Multiplicative.ofAdd 1) ^ m =
        SemidirectProduct.inr
          (φ := integerAffineMonodromy P.affine.latticeMap.toAddEquiv)
          (Multiplicative.ofAdd 1 ^ m) by rw [map_pow]]
    rw [SemidirectProduct.right_inr]
    apply Multiplicative.toAdd.injective
    simp
  rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
    SemidirectProduct.right_inl, hmeridian, inv_one, mul_one]

private theorem affineCyclicTranslation_right
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    (Additive.toMul ((affineCyclicBoundaryDeckData P).translation x)).right = 1 := rfl

private def affineCyclicBoundaryDegree
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    (affineCyclicBoundaryDeckData P).FillingDeck →* Multiplicative (ZMod m) :=
  QuotientGroup.lift (affineCyclicBoundaryDeckData P).fillingKernel
    ((Int.castAddHom (ZMod m)).toMultiplicative.comp SemidirectProduct.rightHom) (by
      rw [fillingKernel_eq_zpowers]
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [MonoidHom.mem_ker]
      rw [map_zpow]
      suffices ((Int.castAddHom (ZMod m)).toMultiplicative.comp
          SemidirectProduct.rightHom)
          (affineCyclicBoundaryDeckData P).fillingRelation = 1 by simp [this]
      change Multiplicative.ofAdd
          (((affineCyclicBoundaryDeckData P).fillingRelation.right.toAdd : ℤ) : ZMod m) = 1
      rw [affineCyclicFillingRelation_right]
      simp)

/-- The period-lattice inclusion into the canonical affine filling deck quotient. -/
@[expose] public def affineCyclicKernelIncl
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    (affineCyclicBoundaryDeckData P).FillingDeck :=
  (affineCyclicBoundaryDeckData P).fillingDeckMap
    (Additive.toMul ((affineCyclicBoundaryDeckData P).translation x))

private theorem affineCyclicKernelIncl_add
    (P : AffineCyclicCentralFiberPresentationData m p D) (x y : Lattice) :
    affineCyclicKernelIncl P (x + y) =
      affineCyclicKernelIncl P x * affineCyclicKernelIncl P y := by
  rw [affineCyclicKernelIncl, affineCyclicKernelIncl, affineCyclicKernelIncl,
    map_add]
  change (affineCyclicBoundaryDeckData P).fillingDeckMap
      (Additive.toMul ((affineCyclicBoundaryDeckData P).translation x) *
        Additive.toMul ((affineCyclicBoundaryDeckData P).translation y)) = _
  rw [map_mul]

private def affineCyclicKernelInclHom
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    Multiplicative Lattice →* (affineCyclicBoundaryDeckData P).FillingDeck where
  toFun x := affineCyclicKernelIncl P x.toAdd
  map_one' := by
    rw [affineCyclicKernelIncl]
    change (affineCyclicBoundaryDeckData P).fillingDeckMap
      (Additive.toMul ((affineCyclicBoundaryDeckData P).translation 0)) = 1
    simp
  map_mul' x y := affineCyclicKernelIncl_add P x.toAdd y.toAdd

private theorem affineCyclicKernelIncl_zsmul
    (P : AffineCyclicCentralFiberPresentationData m p D) (k : ℤ) (x : Lattice) :
    affineCyclicKernelIncl P (k • x) = affineCyclicKernelIncl P x ^ k := by
  simpa [affineCyclicKernelInclHom, ofAdd_zsmul] using
    map_zpow (affineCyclicKernelInclHom P) (Multiplicative.ofAdd x) k

private theorem affineCyclicKernelIncl_injective
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    Function.Injective (affineCyclicKernelIncl P) := by
  intro x y hxy
  have hmem :
      Additive.toMul ((affineCyclicBoundaryDeckData P).translation (x - y)) ∈
        (affineCyclicBoundaryDeckData P).fillingKernel := by
    rw [← QuotientGroup.eq_one_iff]
    rw [map_sub]
    change affineCyclicKernelIncl P x / affineCyclicKernelIncl P y = 1
    exact div_eq_one.mpr hxy
  rw [fillingKernel_eq_zpowers] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hright := congrArg SemidirectProduct.right hk
  change SemidirectProduct.rightHom ((affineCyclicBoundaryDeckData P).fillingRelation ^ k) =
    SemidirectProduct.rightHom
      (Additive.toMul ((affineCyclicBoundaryDeckData P).translation (x - y))) at hright
  rw [map_zpow] at hright
  change (affineCyclicBoundaryDeckData P).fillingRelation.right ^ k =
    (Additive.toMul ((affineCyclicBoundaryDeckData P).translation (x - y))).right at hright
  rw [affineCyclicFillingRelation_right, affineCyclicTranslation_right] at hright
  have hkzero : k = 0 := by
    have hkm : k * (m : ℤ) = 0 := by
      simpa [ofAdd_zsmul, zsmul_eq_mul] using congrArg Multiplicative.toAdd hright
    exact (mul_eq_zero.mp hkm).resolve_right (by exact_mod_cast NeZero.ne m)
  rw [hkzero, zpow_zero] at hk
  apply sub_eq_zero.mp
  apply (affineCyclicBoundaryDeckData P).translation_injective
  apply Additive.toMul.injective
  simpa using hk.symm

private theorem affineCyclicBoundary_decompose
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (g : CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv) :
    g = Additive.toMul
        ((affineCyclicBoundaryDeckData P).translation g.left.toAdd) *
      (affineCyclicBoundaryDeckData P).meridian ^ g.right.toAdd := by
  change g = SemidirectProduct.inl (Multiplicative.ofAdd g.left.toAdd) *
    SemidirectProduct.inr (Multiplicative.ofAdd 1) ^ g.right.toAdd
  rw [show SemidirectProduct.inr
        (φ := integerAffineMonodromy P.affine.latticeMap.toAddEquiv)
        (Multiplicative.ofAdd 1) ^ g.right.toAdd =
      SemidirectProduct.inr g.right by
    rw [← map_zpow]
    congr 1
    apply Multiplicative.toAdd.injective
    simp]
  exact (SemidirectProduct.inl_left_mul_inr_right g).symm

private theorem affineCyclicGenerator_pow
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    (affineCyclicBoundaryDeckData P).fillingDeckMap
          (affineCyclicBoundaryDeckData P).meridian ^ m =
      affineCyclicKernelIncl P P.twist := by
  have hrel := (affineCyclicBoundaryDeckData P).fillingDeckMap_fillingRelation
  rw [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation, map_mul, map_pow, map_inv] at hrel
  change (affineCyclicBoundaryDeckData P).fillingDeckMap
      (affineCyclicBoundaryDeckData P).meridian ^ m *
    (affineCyclicKernelIncl P P.twist)⁻¹ = 1 at hrel
  exact eq_of_mul_inv_eq_one hrel

private theorem affineCyclicBoundaryDegree_eq_one_iff
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (q : (affineCyclicBoundaryDeckData P).FillingDeck) :
    affineCyclicBoundaryDegree P q = 1 ↔ ∃ x, affineCyclicKernelIncl P x = q := by
  constructor
  · intro hq
    obtain ⟨g, rfl⟩ := (affineCyclicBoundaryDeckData P).fillingDeckMap_surjective q
    change Multiplicative.ofAdd ((g.right.toAdd : ℤ) : ZMod m) = 1 at hq
    have hzero : ((g.right.toAdd : ℤ) : ZMod m) = 0 := by
      exact Multiplicative.ofAdd.injective hq
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd g.right.toAdd m).mp hzero
    refine ⟨g.left.toAdd + k • P.twist, ?_⟩
    rw [affineCyclicKernelIncl_add, affineCyclicKernelIncl_zsmul]
    have hg := congrArg (affineCyclicBoundaryDeckData P).fillingDeckMap
      (affineCyclicBoundary_decompose P g)
    rw [map_mul, map_zpow] at hg
    rw [hg, hk, zpow_mul, zpow_natCast, affineCyclicGenerator_pow,
      affineCyclicKernelIncl]
  · rintro ⟨x, rfl⟩
    change Multiplicative.ofAdd
      ((((Additive.toMul ((affineCyclicBoundaryDeckData P).translation x)).right).toAdd : ℤ) :
        ZMod m) = 1
    rw [affineCyclicTranslation_right]
    simp

private noncomputable def canonicalAffineCyclicFillingExtension
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    SphereSixComplex.Topology.CyclicExtension.Data m Lattice
      (affineCyclicBoundaryDeckData P).FillingDeck where
  incl := affineCyclicKernelIncl P
  incl_add := affineCyclicKernelIncl_add P
  incl_injective := affineCyclicKernelIncl_injective P
  proj := affineCyclicBoundaryDegree P
  proj_eq_one_iff := affineCyclicBoundaryDegree_eq_one_iff P
  gen := (affineCyclicBoundaryDeckData P).fillingDeckMap
    (affineCyclicBoundaryDeckData P).meridian
  proj_gen := by
    change Multiplicative.ofAdd ((1 : ℤ) : ZMod m) = Multiplicative.ofAdd 1
    simp
  act := P.affine.latticeMap
  conj_incl := by
    intro x
    have h := congrArg (affineCyclicBoundaryDeckData P).fillingDeckMap
      ((affineCyclicBoundaryDeckData P).conjugate x)
    rw [map_mul, map_mul, map_inv] at h
    change (affineCyclicBoundaryDeckData P).fillingDeckMap
          (affineCyclicBoundaryDeckData P).meridian *
        affineCyclicKernelIncl P x *
          ((affineCyclicBoundaryDeckData P).fillingDeckMap
            (affineCyclicBoundaryDeckData P).meridian)⁻¹ =
      affineCyclicKernelIncl P (P.affine.latticeMap x)
    simpa [affineCyclicKernelIncl, affineCyclicBoundaryDeckData,
      canonicalCyclicAffineBoundaryDeckData] using h
  twist := P.twist
  gen_pow := affineCyclicGenerator_pow P

/-- The exact input left by the degree-one Hurewicz comparison for the affine cyclic deck
extension.

The marked group is a cyclic extension of the period lattice with the prescribed monodromy and
full-iterate translation.  Its abelianization is identified with first homology, naturally on the
lattice subgroup. -/
public structure AffineCyclicUniversalCoverHOneIdentification
    (P : AffineCyclicCentralFiberPresentationData m p D) where
  extension : SphereSixComplex.Topology.CyclicExtension.Data m Lattice
    (affineCyclicBoundaryDeckData P).FillingDeck
  action_eq : extension.act = P.affine.latticeMap
  twist_eq : extension.twist = P.twist
  hOneEquiv : Additive (Abelianization (affineCyclicBoundaryDeckData P).FillingDeck) ≃ₗ[ℤ]
    IntegralSingularHomology 1 D.reducedCentralFiber
  projection : ∀ x, hOneEquiv (extension.kernelToAbelianization x) =
    coverProjectionLatticeMap P x

/-- The remaining classical degree-one Hurewicz input.  The filling deck group has already been
constructed algebraically as the canonical cyclic extension; this comparison identifies its
abelianization with first homology and records naturality on period-lattice translations. -/
public structure AffineCyclicDeckHurewiczComparison
    (P : AffineCyclicCentralFiberPresentationData m p D) where
  hOneEquiv : Additive (Abelianization (affineCyclicBoundaryDeckData P).FillingDeck) ≃ₗ[ℤ]
    IntegralSingularHomology 1 D.reducedCentralFiber
  projection : ∀ x,
    hOneEquiv (Additive.ofMul (Abelianization.of (affineCyclicKernelIncl P x))) =
      coverProjectionLatticeMap P x

/-- The standard marked degree-one Hurewicz comparison for the affine universal cover. -/
public axiom establishedAffineCyclicDeckHurewiczComparison
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    AffineCyclicDeckHurewiczComparison P

/-- The canonical algebraic extension together with the marked degree-one Hurewicz comparison. -/
public noncomputable def establishedAffineCyclicUniversalCoverHOneIdentification
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    AffineCyclicUniversalCoverHOneIdentification P := by
  let H := establishedAffineCyclicDeckHurewiczComparison P
  exact {
    extension := canonicalAffineCyclicFillingExtension P
    action_eq := rfl
    twist_eq := rfl
    hOneEquiv := H.hOneEquiv
    projection := H.projection }

namespace AffineCyclicUniversalCoverHOneIdentification

variable (P : AffineCyclicCentralFiberPresentationData m p D)
  (I : AffineCyclicUniversalCoverHOneIdentification P)

public theorem difference_eq : I.extension.difference = P.latticeDifference := by
  apply LinearMap.ext
  intro x
  rw [SphereSixComplex.Topology.CyclicExtension.Data.difference_apply,
    P.latticeDifference_eq, LinearMap.sub_apply, LinearMap.id_apply]
  exact congrArg (fun y ↦ y - x) (LinearEquiv.congr_fun I.action_eq x)

/-- The homology class of the marked affine deck generator. -/
@[expose] public def meridian : IntegralSingularHomology 1 D.reducedCentralFiber :=
  I.hOneEquiv (Additive.ofMul (Abelianization.of I.extension.gen))

/-- The full cyclic iterate of the marked meridian is the twist lattice class. -/
public theorem fullIterate :
    (m : ℤ) • I.meridian P = coverProjectionLatticeMap P P.twist := by
  rw [meridian, ← map_smul]
  change I.hOneEquiv
      (Additive.ofMul (Abelianization.of I.extension.gen ^ (m : ℤ))) = _
  rw [← map_zpow, zpow_natCast, I.extension.gen_pow]
  change I.hOneEquiv (I.extension.kernelToAbelianization I.extension.twist) = _
  rw [I.projection, I.twist_eq]

/-- The canonical map from the multiple-fibre presentation to the abelianized affine deck
group. -/
@[expose] public noncomputable def toAbelianization :
    MultipleFiberHOnePresentation P.latticeDifference P.twist (m : ℤ) →ₗ[ℤ]
      Additive (Abelianization (affineCyclicBoundaryDeckData P).FillingDeck) :=
  multipleFiberLift P.latticeDifference P.twist (m : ℤ)
    I.extension.kernelToAbelianization (by
      intro x
      rw [← I.difference_eq P]
      exact I.extension.kernelToAbelianization_difference x)
    (Additive.ofMul (Abelianization.of I.extension.gen)) (by
      rw [← ofMul_zpow, ← map_zpow, zpow_natCast, I.extension.gen_pow,
        ← I.extension.kernelToAbelianization_apply, I.twist_eq])

@[simp] public theorem toAbelianization_mk (x : Lattice) (k : ℤ) :
    I.toAbelianization P (Submodule.Quotient.mk (Submodule.Quotient.mk x, k)) =
      Additive.ofMul
        (Abelianization.of (I.extension.incl x) * Abelianization.of I.extension.gen ^ k) := by
  rw [toAbelianization, multipleFiberLift_mk,
    SphereSixComplex.Topology.CyclicExtension.Data.kernelToAbelianization_apply,
    ← ofMul_zpow, ← ofMul_mul]

public theorem toAbelianization_surjective : Function.Surjective (I.toAbelianization P) := by
  intro y
  obtain ⟨x, hx⟩ := Quot.exists_rep (Additive.toMul y)
  obtain ⟨k, l, rfl⟩ := I.extension.exists_zpow_mul_incl x
  refine ⟨Submodule.Quotient.mk (Submodule.Quotient.mk l, k), ?_⟩
  rw [I.toAbelianization_mk]
  have hval : Abelianization.of (I.extension.gen ^ k * I.extension.incl l) =
      Additive.toMul y := hx
  rw [map_mul, map_zpow, mul_comm] at hval
  rw [hval]
  rfl

public theorem toAbelianization_injective : Function.Injective (I.toAbelianization P) := by
  have key : ∀ y, I.toAbelianization P y = 0 → y = 0 := by
    intro y hy
    obtain ⟨⟨lq, k⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ lq
    rw [I.toAbelianization_mk] at hy
    have h1 : Abelianization.of (I.extension.incl l * I.extension.gen ^ k) = 1 := by
      rw [map_mul, map_zpow]
      exact hy
    have h2 : I.extension.incl l * I.extension.gen ^ k ∈
        commutator (affineCyclicBoundaryDeckData P).FillingDeck := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      exact h1
    obtain ⟨μ, hμ⟩ := I.extension.commutator_le_differenceSubgroup h2
    have hprojl : I.extension.proj (I.extension.incl l) = 1 :=
      (I.extension.proj_eq_one_iff _).mpr ⟨l, rfl⟩
    have hprojd : I.extension.proj (I.extension.incl (I.extension.difference μ)) = 1 :=
      (I.extension.proj_eq_one_iff _).mpr ⟨I.extension.difference μ, rfl⟩
    have hgk : I.extension.proj (I.extension.gen ^ k) = 1 := by
      have hcong := congrArg I.extension.proj hμ
      rw [hprojd, map_mul, hprojl, one_mul] at hcong
      exact hcong.symm
    have hzero : ((k : ℤ) : ZMod m) = 0 := by
      rw [map_zpow, I.extension.proj_gen, ← ofAdd_zsmul, zsmul_eq_mul, mul_one] at hgk
      exact hgk
    obtain ⟨j, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k m).mp hzero
    have hgpow : I.extension.gen ^ ((m : ℤ) * j) =
        I.extension.incl (j • I.extension.twist) := by
      rw [zpow_mul, zpow_natCast, I.extension.gen_pow, I.extension.incl_zsmul]
    have heq : I.extension.difference μ = l + j • I.extension.twist := by
      apply I.extension.incl_injective
      rw [I.extension.incl_add, ← hgpow, hμ]
    have heqP : P.latticeDifference μ = l + j • P.twist := by
      rw [← I.difference_eq P, ← I.twist_eq]
      exact heq
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨j, ?_⟩
    have hmk :
        (Submodule.Quotient.mk l : Lattice ⧸ LinearMap.range P.latticeDifference) =
          -(j • Submodule.Quotient.mk P.twist) := by
      have hz :
          (Submodule.Quotient.mk (P.latticeDifference μ) :
            Lattice ⧸ LinearMap.range P.latticeDifference) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨μ, rfl⟩
      rw [heqP] at hz
      rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul] at hz
      linear_combination (norm := abel) hz
    rw [multipleFiberRelationMap]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Prod.smul_mk, smul_neg, Prod.mk.injEq]
    exact ⟨by rw [hmk], by rw [smul_eq_mul, mul_comm]⟩
  intro a b hab
  have hsub : I.toAbelianization P (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (key _ hsub)

public theorem presentationLift_eq :
    presentationLift isCentralFiberCoverSourceCoordinate P (I.meridian P) (I.fullIterate P) =
      I.hOneEquiv.toLinearMap.comp (I.toAbelianization P) := by
  apply LinearMap.ext
  intro q
  obtain ⟨⟨lq, k⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ lq
  rw [presentationLift_mk, LinearMap.comp_apply, I.toAbelianization_mk, meridian]
  change coverProjectionLatticeMap P x +
      k • I.hOneEquiv (Additive.ofMul (Abelianization.of I.extension.gen)) =
    I.hOneEquiv
      (Additive.ofMul
        (Abelianization.of (I.extension.incl x) * Abelianization.of I.extension.gen ^ k))
  rw [← I.projection, ← map_smul, ← map_add]
  congr 1

public theorem presentationLift_bijective :
    Function.Bijective
      (presentationLift isCentralFiberCoverSourceCoordinate P (I.meridian P)
        (I.fullIterate P)) := by
  rw [I.presentationLift_eq P]
  exact ⟨I.hOneEquiv.injective.comp (I.toAbelianization_injective P),
    I.hOneEquiv.surjective.comp (I.toAbelianization_surjective P)⟩

end AffineCyclicUniversalCoverHOneIdentification

/-- The exact data consumed by the final presentation wrapper. -/
public structure AffineCyclicHOnePresentationLiftWitness
    (P : AffineCyclicCentralFiberPresentationData m p D) where
  meridian : IntegralSingularHomology 1 D.reducedCentralFiber
  fullIterate : (m : ℤ) • meridian = coverProjectionLatticeMap P P.twist
  bijective : Function.Bijective
    (presentationLift isCentralFiberCoverSourceCoordinate P meridian fullIterate)

/-- The marked universal-cover identification supplies the meridian, its full-iterate relation,
and bijectivity of the presentation map. -/
public noncomputable def establishedAffineCyclicHOnePresentationLift_bijective
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    AffineCyclicHOnePresentationLiftWitness P := by
  let I := establishedAffineCyclicUniversalCoverHOneIdentification P
  exact {
    meridian := I.meridian P
    fullIterate := I.fullIterate P
    bijective := I.presentationLift_bijective P }

/-- The usual presentation theorem for a free affine cyclic torus quotient, including the
canonical value of the presentation coordinates on the covering torus. -/
public noncomputable def reducedCentralFiberHOnePresentation
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    ReducedCentralFiberHOnePresentation P := by
  let R := establishedAffineCyclicHOnePresentationLift_bijective P
  exact reducedCentralFiberHOnePresentation_of_bijective
    isCentralFiberCoverSourceCoordinate P R.meridian R.fullIterate R.bijective

/-- For a free affine action of a finite cyclic group on a full-rank torus, first integral
homology is the abelianization of the standard covering-group presentation.  Thus it is the
coinvariants of the lattice together with a meridian, subject to the relation that `m` times
the meridian is the full-iterate lattice translation.

This combines the standard identification of first homology with the abelianized fundamental
group and the usual presentation of the fundamental group of a free affine cyclic torus
quotient. -/
public noncomputable def reducedCentralFiberHOneEquivPresentation
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    IntegralSingularHomology 1 D.reducedCentralFiber ≃ₗ[ℤ]
      MultipleFiberHOnePresentation
        P.latticeDifference P.twist (m : ℤ) :=
  (reducedCentralFiberHOnePresentation P).equiv

/-- The presentation equivalence sends the homology map of the covering torus to the canonical
lattice-to-presentation map. -/
public theorem reducedCentralFiberHOneEquivPresentation_projection
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    reducedCentralFiberHOneEquivPresentation P
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection D)
          ((centralFiberCoverSourceDegreeOneBasis P).symm x)) =
      latticeProjection P x :=
  (reducedCentralFiberHOnePresentation P).projection x

end EstablishedAffineCyclicQuotientHomology

variable {U : TriangleUniformization} (F : PeriodFunctions U)

private theorem orderThreeLiftTranslation_fixed :
    (orderThreeDescendedAffineTorusAutomorphism F).lift
        ((3 : ℝ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon) =
      (3 : ℝ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon := by
  change periodTransport g₁ (parameterMap F U.zOne)
      ((3 : ℝ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon) = _
  rw [map_smul]
  rw [periodTransport_periodVector, rhoLambda_g₁_apply, A₁_epsilon]
  rw [parameterMap_zOne_fixed F]

private theorem orderFourLiftTranslation_fixed :
    (orderFourDescendedAffineTorusAutomorphism F).lift
        ((4 : ℝ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')) =
      (4 : ℝ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon') := by
  change periodTransport g₂ (parameterMap F U.zTwo)
      ((4 : ℝ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')) = _
  rw [map_smul]
  rw [periodTransport_periodVector, rhoLambda_g₂_apply, Matrix.mulVec_neg, A₂_epsilon']
  rw [parameterMap_zTwo_fixed F]

/-- The actual order-three reduced fibre supplies all inputs to the general affine cyclic
quotient calculation. -/
@[expose] public def orderThreeCentralFiberPresentationData :
    AffineCyclicCentralFiberPresentationData 3 (parameterMap F U.zOne).1
      (orderThreeRadialActionData F) where
  fullRank := fullRankDomain (parameterMap F U.zOne)
  affine := orderThreeDescendedAffineTorusAutomorphism F
  latticeDifference := orderOneDifference
  latticeDifference_eq := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.sub_apply, LinearMap.id_apply, orderOneDifference_apply]
    exact (congrArg (fun y ↦ y - x) (rhoLambda_g₁_apply x)).symm
  twist := epsilon
  translationVector_eq := rfl
  liftTranslation := (3 : ℝ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon
  translation_mk := by
    change Quotient.mk _ ((3 : ℂ)⁻¹ • periodVector _ epsilon) =
      Quotient.mk _ ((3 : ℝ)⁻¹ • periodVector _ epsilon)
    congr 1
    ext i
    norm_num
  generator_eq _ := rfl
  lift_full_iterate z := by
    rw [affineEquiv_pow_apply _ _ (orderThreeLiftTranslation_fixed F)]
    change periodTransport g₁ (parameterMap F U.zOne)
        (periodTransport g₁ (parameterMap F U.zOne)
          (periodTransport g₁ (parameterMap F U.zOne) z)) +
        3 • ((3 : ℝ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon) = _
    rw [periodTransport_gOne_three]
    congr 1
    ext i
    simp
  free := orderThreeAction_free F

/-- The actual order-four reduced fibre supplies all inputs to the general affine cyclic
quotient calculation. -/
@[expose] public def orderFourCentralFiberPresentationData :
    AffineCyclicCentralFiberPresentationData 4 (parameterMap F U.zTwo).1
      (orderFourRadialActionData F) where
  fullRank := fullRankDomain (parameterMap F U.zTwo)
  affine := orderFourDescendedAffineTorusAutomorphism F
  latticeDifference := orderTwoDifference
  latticeDifference_eq := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.sub_apply, LinearMap.id_apply, orderTwoDifference_apply]
    exact (congrArg (fun y ↦ y - x) (rhoLambda_g₂_apply x)).symm
  twist := -epsilon'
  translationVector_eq := rfl
  liftTranslation := (4 : ℝ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')
  translation_mk := by
    change Quotient.mk _ ((4 : ℂ)⁻¹ • periodVector _ (-epsilon')) =
      Quotient.mk _ ((4 : ℝ)⁻¹ • periodVector _ (-epsilon'))
    congr 1
    ext i
    norm_num
  generator_eq _ := rfl
  lift_full_iterate z := by
    rw [affineEquiv_pow_apply _ _ (orderFourLiftTranslation_fixed F)]
    change periodTransport g₂ (parameterMap F U.zTwo)
        (periodTransport g₂ (parameterMap F U.zTwo)
          (periodTransport g₂ (parameterMap F U.zTwo)
            (periodTransport g₂ (parameterMap F U.zTwo) z))) +
        4 • ((4 : ℝ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')) = _
    rw [periodTransport_gTwo_four]
    congr 1
    ext i
    simp
  free := orderFourAction_free F

/-- First integral homology of the actual order-three reduced elliptic fibre, with the exact
multiple-fibre presentation from Lemma 7.13. -/
public noncomputable def orderThreeReducedCentralFiberHOneEquivPresentation :
    IntegralSingularHomology 1 (OrderThreeReducedCentralFiber F) ≃ₗ[ℤ]
      OrderOneSelectedPresentation := by
  exact EstablishedAffineCyclicQuotientHomology.reducedCentralFiberHOneEquivPresentation
    (orderThreeCentralFiberPresentationData F)

/-- First integral homology of the actual order-four reduced elliptic fibre, with the exact
multiple-fibre presentation from Lemma 7.13. -/
public noncomputable def orderFourReducedCentralFiberHOneEquivPresentation :
    IntegralSingularHomology 1 (OrderFourReducedCentralFiber F) ≃ₗ[ℤ]
      OrderTwoSelectedPresentation := by
  exact EstablishedAffineCyclicQuotientHomology.reducedCentralFiberHOneEquivPresentation
    (orderFourCentralFiberPresentationData F)

/-- In particular, first integral homology of the actual order-three reduced fibre is free of
rank two. -/
public noncomputable def orderThreeReducedCentralFiberHOneEquivIntSquared :
    IntegralSingularHomology 1 (OrderThreeReducedCentralFiber F) ≃ₗ[ℤ] IntSquared :=
  (orderThreeReducedCentralFiberHOneEquivPresentation F).trans
    orderOneSelectedPresentationEquivIntSquared

/-- In particular, first integral homology of the actual order-four reduced fibre is free of
rank two. -/
public noncomputable def orderFourReducedCentralFiberHOneEquivIntSquared :
    IntegralSingularHomology 1 (OrderFourReducedCentralFiber F) ≃ₗ[ℤ] IntSquared :=
  (orderFourReducedCentralFiberHOneEquivPresentation F).trans
    orderTwoSelectedPresentationEquivIntSquared

/-- The fixed order-three coordinates of the covering projection, before evaluating the explicit
presentation-coordinate map. -/
public theorem orderThreeReducedCentralFiberHOneEquivIntSquared_projection_raw (x : Lattice) :
    orderThreeReducedCentralFiberHOneEquivIntSquared F
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderThreeRadialActionData F))
          ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) =
      orderOneSelectedPresentationEquivIntSquared
        (Submodule.Quotient.mk (Submodule.Quotient.mk x, 0)) := by
  have h :=
    EstablishedAffineCyclicQuotientHomology.reducedCentralFiberHOneEquivPresentation_projection
      (orderThreeCentralFiberPresentationData F) x
  change orderThreeReducedCentralFiberHOneEquivPresentation F
      (integralSingularHomologyMap 1
        (RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData F))
        ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) =
      EstablishedAffineCyclicQuotientHomology.latticeProjection
        (orderThreeCentralFiberPresentationData F) x at h
  have hc := congrArg orderOneSelectedPresentationEquivIntSquared h
  change orderOneSelectedPresentationEquivIntSquared
      (orderThreeReducedCentralFiberHOneEquivPresentation F
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderThreeRadialActionData F))
          ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x))) = _
  exact hc

/-- The fixed order-four coordinates of the covering projection, before evaluating the explicit
presentation-coordinate map. -/
public theorem orderFourReducedCentralFiberHOneEquivIntSquared_projection_raw (x : Lattice) :
    orderFourReducedCentralFiberHOneEquivIntSquared F
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderFourRadialActionData F))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) =
      orderTwoSelectedPresentationEquivIntSquared
        (Submodule.Quotient.mk (Submodule.Quotient.mk x, 0)) := by
  have h :=
    EstablishedAffineCyclicQuotientHomology.reducedCentralFiberHOneEquivPresentation_projection
      (orderFourCentralFiberPresentationData F) x
  change orderFourReducedCentralFiberHOneEquivPresentation F
      (integralSingularHomologyMap 1
        (RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData F))
        ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) =
      EstablishedAffineCyclicQuotientHomology.latticeProjection
        (orderFourCentralFiberPresentationData F) x at h
  have hc := congrArg orderTwoSelectedPresentationEquivIntSquared h
  change orderTwoSelectedPresentationEquivIntSquared
      (orderFourReducedCentralFiberHOneEquivPresentation F
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderFourRadialActionData F))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x))) = _
  exact hc

end

end SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
