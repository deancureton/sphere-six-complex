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

@[expose] public def affineCyclicBoundaryDegree
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

public structure CanonicalAffineCyclicFillingExtensionData
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    Type where
  extension : SphereSixComplex.Topology.CyclicExtension.Data m Lattice
    (affineCyclicBoundaryDeckData P).FillingDeck
  action_eq : extension.act = P.affine.latticeMap
  twist_eq : extension.twist = P.twist
  kernelToAbelianization : ∀ x,
    extension.kernelToAbelianization x =
      Additive.ofMul (Abelianization.of (affineCyclicKernelIncl P x))

public noncomputable def canonicalAffineCyclicFillingExtensionData
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    CanonicalAffineCyclicFillingExtensionData P where
  extension := {
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
    gen_pow := affineCyclicGenerator_pow P }
  action_eq := rfl
  twist_eq := rfl
  kernelToAbelianization _ := rfl

@[expose] public noncomputable def canonicalAffineCyclicFillingExtension
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    SphereSixComplex.Topology.CyclicExtension.Data m Lattice
      (affineCyclicBoundaryDeckData P).FillingDeck :=
  (canonicalAffineCyclicFillingExtensionData P).extension

public theorem canonicalAffineCyclicFillingExtension_action_eq
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    (canonicalAffineCyclicFillingExtension P).act = P.affine.latticeMap :=
  (canonicalAffineCyclicFillingExtensionData P).action_eq

public theorem canonicalAffineCyclicFillingExtension_twist_eq
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    (canonicalAffineCyclicFillingExtension P).twist = P.twist :=
  (canonicalAffineCyclicFillingExtensionData P).twist_eq

public theorem canonicalAffineCyclicFillingExtension_kernelToAbelianization
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    (canonicalAffineCyclicFillingExtension P).kernelToAbelianization x =
      Additive.ofMul (Abelianization.of (affineCyclicKernelIncl P x)) :=
  (canonicalAffineCyclicFillingExtensionData P).kernelToAbelianization x

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

/-- The marked degree-one Hurewicz comparison for the affine filling deck group. -/
public structure AffineCyclicDeckHurewiczComparison
    (P : AffineCyclicCentralFiberPresentationData m p D) where
  hOneEquiv : Additive (Abelianization (affineCyclicBoundaryDeckData P).FillingDeck) ≃ₗ[ℤ]
    IntegralSingularHomology 1 D.reducedCentralFiber
  projection : ∀ x,
    hOneEquiv (Additive.ofMul (Abelianization.of (affineCyclicKernelIncl P x))) =
      coverProjectionLatticeMap P x

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
  lift_continuous := LinearMap.continuous_of_finiteDimensional
    (periodTransport g₁ (parameterMap F U.zOne)).toLinearMap
  lift_symm_continuous := LinearMap.continuous_of_finiteDimensional
    (periodTransport g₁ (parameterMap F U.zOne)).symm.toLinearMap
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
  lift_continuous := LinearMap.continuous_of_finiteDimensional
    (periodTransport g₂ (parameterMap F U.zTwo)).toLinearMap
  lift_symm_continuous := LinearMap.continuous_of_finiteDimensional
    (periodTransport g₂ (parameterMap F U.zTwo)).symm.toLinearMap
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

end

end SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
