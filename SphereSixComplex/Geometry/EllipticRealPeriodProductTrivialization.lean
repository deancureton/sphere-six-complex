module

public import SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient

/-!
# Real-period product coordinates for the elliptic family

The canonical real period basis gives a product trivialization of the moving vector cover and
torus family. Explicit inverse coordinates prove joint continuity of the inverse period map.
-/

namespace SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization

open SphereSixComplex.Geometry SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.FamilyEquivariance

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- The determinant of the imaginary two-by-two system which recovers the first two real period
coordinates. -/
@[expose] public def periodCoordinateDenominator (x : PeriodDomain) : ℝ :=
  6 * x.1.mu.im ^ 2 - x.1.tau.im * x.1.beta.im

public theorem periodCoordinateDenominator_pos (x : PeriodDomain) :
    0 < periodCoordinateDenominator x := by
  have ht : x.1.tau.im ≠ 0 := ne_of_gt x.2.tau_im_pos
  have hmul : x.1.tau.im *
      (x.1.beta.im - 6 * x.1.mu.im ^ 2 / x.1.tau.im) < 0 :=
    mul_neg_of_pos_of_neg x.2.tau_im_pos x.2.schur_im_neg
  rw [periodCoordinateDenominator]
  field_simp [ht] at hmul
  nlinarith

/-- Explicit inverse real-period coordinates. -/
@[expose] public def explicitPeriodCoordinates (x : PeriodDomain)
    (v : ComplexTwoSpace) : RealPeriods :=
  let d := periodCoordinateDenominator x
  let a₀ := (x.1.mu.im * (v 0).im - x.1.tau.im * (v 1).im) / d
  let a₁ := (-x.1.beta.im * (v 0).im + 6 * x.1.mu.im * (v 1).im) / d
  ![a₀, a₁,
    (v 0).re - 6 * a₀ * x.1.mu.re - a₁ * x.1.tau.re,
    (v 1).re - a₀ * x.1.beta.re - a₁ * x.1.mu.re]

/-- The explicit formula reconstructs the supplied vector in the real period basis. -/
public theorem periodRealLinear_explicitPeriodCoordinates (x : PeriodDomain)
    (v : ComplexTwoSpace) :
    periodRealLinear x.1 (explicitPeriodCoordinates x v) = v := by
  have hd : periodCoordinateDenominator x ≠ 0 :=
    ne_of_gt (periodCoordinateDenominator_pos x)
  funext i
  fin_cases i
  · apply Complex.ext
    · simp [explicitPeriodCoordinates, periodRealLinear]
      ring
    · simp [explicitPeriodCoordinates]
      field_simp [hd]
      rw [periodCoordinateDenominator]
      ring
  · apply Complex.ext
    · simp [explicitPeriodCoordinates, periodRealLinear]
    · simp [explicitPeriodCoordinates]
      field_simp [hd]
      rw [periodCoordinateDenominator]
      ring

/-- The abstract inverse period equivalence is the explicit coordinate formula. -/
public theorem periodCoordinates_eq_explicitPeriodCoordinates (x : PeriodDomain)
    (v : ComplexTwoSpace) :
    periodCoordinates x v = explicitPeriodCoordinates x v := by
  apply (fullRankDomain x).realEquiv.injective
  change (fullRankDomain x).realEquiv ((fullRankDomain x).realEquiv.symm v) = _
  rw [(fullRankDomain x).realEquiv.apply_symm_apply]
  rw [fullRankDomain.eq_def, FullRank.ofSetupInequalities_realEquiv_apply]
  exact (periodRealLinear_explicitPeriodCoordinates x v).symm

/-- The inverse moving period coordinates vary jointly continuously. -/
public theorem periodCoordinates_parameterMap_continuous :
    Continuous (fun p : UpperHalfPlane × ComplexTwoSpace ↦
      periodCoordinates (parameterMap F p.1) p.2) := by
  have ht : Continuous (fun p : UpperHalfPlane × ComplexTwoSpace ↦ (F.tau p.1 : ℂ)) :=
    (tau_contMDiff F 0).continuous.comp continuous_fst
  have hm : Continuous (fun p : UpperHalfPlane × ComplexTwoSpace ↦ F.mu p.1) :=
    (mu_contMDiff F 0).continuous.comp continuous_fst
  have hb : Continuous (fun p : UpperHalfPlane × ComplexTwoSpace ↦ F.beta p.1) :=
    (beta_contMDiff F 0).continuous.comp continuous_fst
  have hv (i : Fin 2) : Continuous (fun p : UpperHalfPlane × ComplexTwoSpace ↦ p.2 i) :=
    (continuous_apply i).comp continuous_snd
  have ht_re := Complex.continuous_re.comp ht
  have ht_im := Complex.continuous_im.comp ht
  have hm_re := Complex.continuous_re.comp hm
  have hm_im := Complex.continuous_im.comp hm
  have hb_re := Complex.continuous_re.comp hb
  have hb_im := Complex.continuous_im.comp hb
  have hv_re (i : Fin 2) := Complex.continuous_re.comp (hv i)
  have hv_im (i : Fin 2) := Complex.continuous_im.comp (hv i)
  have hd : Continuous (fun p : UpperHalfPlane × ComplexTwoSpace ↦
      periodCoordinateDenominator (parameterMap F p.1)) := by
    convert (hm_im.pow 2 |>.const_mul 6).sub (ht_im.mul hb_im) using 1
    funext p
    rfl
  have hd_ne (p : UpperHalfPlane × ComplexTwoSpace) :
      periodCoordinateDenominator (parameterMap F p.1) ≠ 0 :=
    ne_of_gt (periodCoordinateDenominator_pos (parameterMap F p.1))
  let a₀ := fun p : UpperHalfPlane × ComplexTwoSpace ↦
    ((F.mu p.1).im * (p.2 0).im - (F.tau p.1).im * (p.2 1).im) /
      periodCoordinateDenominator (parameterMap F p.1)
  let a₁ := fun p : UpperHalfPlane × ComplexTwoSpace ↦
    (-(F.beta p.1).im * (p.2 0).im + 6 * (F.mu p.1).im * (p.2 1).im)
      / periodCoordinateDenominator (parameterMap F p.1)
  have ha₀ : Continuous a₀ :=
    (hm_im.mul (hv_im 0) |>.sub (ht_im.mul (hv_im 1))).div hd hd_ne |>.congr fun _ ↦ rfl
  have ha₁ : Continuous a₁ := by
    convert ((hb_im.neg.mul (hv_im 0)).add
      (hm_im.mul (hv_im 1) |>.const_mul 6)).div hd hd_ne using 1
    funext p
    simp [a₁]
    ring
  rw [show (fun p : UpperHalfPlane × ComplexTwoSpace ↦
      periodCoordinates (parameterMap F p.1) p.2) =
      fun p ↦ explicitPeriodCoordinates (parameterMap F p.1) p.2 by
    funext p
    exact periodCoordinates_eq_explicitPeriodCoordinates _ _]
  apply continuous_pi
  intro i
  fin_cases i
  · convert ha₀ using 1
    funext p
    rfl
  · convert ha₁ using 1
    funext p
    rfl
  · convert (hv_re 0).sub ((ha₀.const_mul 6).mul hm_re) |>.sub (ha₁.mul ht_re)
      using 1
    funext p
    rfl
  · convert (hv_re 1).sub (ha₀.mul hb_re) |>.sub (ha₁.mul hm_re) using 1
    funext p
    rfl

/-- Write a vector in the moving real period basis and rebuild it in the fixed basis over `z₀`. -/
@[expose] public def movingToFixedCover (z₀ : UpperHalfPlane)
    (p : UpperHalfPlane × ComplexTwoSpace) : UpperHalfPlane × ComplexTwoSpace :=
  (p.1, (fullRankDomain (parameterMap F z₀)).realEquiv
    (periodCoordinates (parameterMap F p.1) p.2))

/-- Rebuild fixed real period coordinates in the moving period basis. -/
@[expose] public def fixedToMovingCover (z₀ : UpperHalfPlane)
    (p : UpperHalfPlane × ComplexTwoSpace) : UpperHalfPlane × ComplexTwoSpace :=
  (p.1, (fullRankDomain (parameterMap F p.1)).realEquiv
    ((fullRankDomain (parameterMap F z₀)).realEquiv.symm p.2))

public theorem movingToFixedCover_fixedToMovingCover (z₀ : UpperHalfPlane)
    (p : UpperHalfPlane × ComplexTwoSpace) :
    movingToFixedCover F z₀ (fixedToMovingCover F z₀ p) = p := by
  apply Prod.ext
  · rfl
  · simp [movingToFixedCover, fixedToMovingCover, periodCoordinates]

public theorem fixedToMovingCover_movingToFixedCover (z₀ : UpperHalfPlane)
    (p : UpperHalfPlane × ComplexTwoSpace) :
    fixedToMovingCover F z₀ (movingToFixedCover F z₀ p) = p := by
  apply Prod.ext
  · rfl
  · simp [movingToFixedCover, fixedToMovingCover, periodCoordinates]

/-- Algebraic product equivalence of the moving vector cover with the fixed vector product. -/
@[expose] public def realPeriodCoverEquiv (z₀ : UpperHalfPlane) :
    (UpperHalfPlane × ComplexTwoSpace) ≃ (UpperHalfPlane × ComplexTwoSpace) where
  toFun := movingToFixedCover F z₀
  invFun := fixedToMovingCover F z₀
  left_inv := fixedToMovingCover_movingToFixedCover F z₀
  right_inv := movingToFixedCover_fixedToMovingCover F z₀

/-- The fixed-to-moving direction is jointly continuous using the existing forward period-map
continuity theorem. -/
public theorem fixedToMovingCover_continuous (z₀ : UpperHalfPlane) :
    Continuous (fixedToMovingCover F z₀) := by
  have hcoordinates : Continuous (fun p : UpperHalfPlane × ComplexTwoSpace ↦
      (p.1, (fullRankDomain (parameterMap F z₀)).realEquiv.symm p.2)) :=
    continuous_fst.prodMk
      ((fullRankDomain (parameterMap F z₀)).realEquiv.symm.continuous.comp continuous_snd)
  have hperiod := (periodRealLinear_parameterMap_continuous F).comp hcoordinates
  apply continuous_fst.prodMk
  convert hperiod using 1
  funext p
  rw [fullRankDomain.eq_def, FullRank.ofSetupInequalities_realEquiv_apply]
  rfl

/-- The moving-to-fixed direction is jointly continuous. -/
public theorem movingToFixedCover_continuous (z₀ : UpperHalfPlane) :
    Continuous (movingToFixedCover F z₀) := by
  exact continuous_fst.prodMk
    ((fullRankDomain (parameterMap F z₀)).realEquiv.continuous.comp
      (periodCoordinates_parameterMap_continuous F))

/-- The canonical real-period change of coordinates is a homeomorphism of vector covers. -/
@[expose] public def realPeriodCoverHomeomorph (z₀ : UpperHalfPlane) :
    (UpperHalfPlane × ComplexTwoSpace) ≃ₜ (UpperHalfPlane × ComplexTwoSpace) where
  toEquiv := realPeriodCoverEquiv F z₀
  continuous_toFun := movingToFixedCover_continuous F z₀
  continuous_invFun := fixedToMovingCover_continuous F z₀

/-- Moving integer-period translations become the same integer-period translations in the fixed
basis. -/
public theorem movingToFixedCover_period_add (z₀ z : UpperHalfPlane)
    (n : IntegerPeriods) (v : ComplexTwoSpace) :
    movingToFixedCover F z₀
        (z, periodVector (parameterMap F z).1 n + v) =
      (z, periodVector (parameterMap F z₀).1 n +
        (movingToFixedCover F z₀ (z, v)).2) := by
  apply Prod.ext
  · rfl
  · change (fullRankDomain (parameterMap F z₀)).realEquiv
        (periodCoordinates (parameterMap F z)
          (periodVector (parameterMap F z).1 n + v)) = _
    change (fullRankDomain (parameterMap F z₀)).realEquiv
        (periodCoordinates (parameterMap F z)
          (periodVector (parameterMap F z).1 n + v)) =
      periodVector (parameterMap F z₀).1 n +
        (fullRankDomain (parameterMap F z₀)).realEquiv
          (periodCoordinates (parameterMap F z) v)
    rw [show periodCoordinates (parameterMap F z)
          (periodVector (parameterMap F z).1 n + v) =
        periodCoordinates (parameterMap F z) (periodVector (parameterMap F z).1 n) +
          periodCoordinates (parameterMap F z) v by
        exact map_add (fullRankDomain (parameterMap F z)).realEquiv.symm _ _,
      periodCoordinates_periodVector, map_add,
      (fullRankDomain (parameterMap F z₀)).map_integer]

/-- Fixed integer-period translations rebuild as moving integer periods. -/
public theorem fixedToMovingCover_period_add (z₀ z : UpperHalfPlane)
    (n : IntegerPeriods) (v : ComplexTwoSpace) :
    fixedToMovingCover F z₀
        (z, periodVector (parameterMap F z₀).1 n + v) =
      (z, periodVector (parameterMap F z).1 n +
        (fixedToMovingCover F z₀ (z, v)).2) := by
  apply Prod.ext
  · rfl
  · rw [fixedToMovingCover]
    change (fullRankDomain (parameterMap F z)).realEquiv
        ((fullRankDomain (parameterMap F z₀)).realEquiv.symm
          (periodVector (parameterMap F z₀).1 n + v)) =
      periodVector (parameterMap F z).1 n +
        (fullRankDomain (parameterMap F z)).realEquiv
          ((fullRankDomain (parameterMap F z₀)).realEquiv.symm v)
    rw [← (fullRankDomain (parameterMap F z₀)).map_integer n, map_add,
      (fullRankDomain (parameterMap F z₀)).realEquiv.symm_apply_apply, map_add,
      (fullRankDomain (parameterMap F z)).map_integer]

/-- The constant family whose fibre is the torus over `z₀`. -/
@[expose] public def fixedParameterMap (z₀ : UpperHalfPlane) :
    UpperHalfPlane → PeriodDomain :=
  fun _ ↦ parameterMap F z₀

public theorem movingToFixedCover_orbitRel (z₀ : UpperHalfPlane)
    (p q : UpperHalfPlane × ComplexTwoSpace)
    (h : MulAction.orbitRel (FamilyPeriodGroup (parameterMap F)) _ p q) :
    MulAction.orbitRel (FamilyPeriodGroup (fixedParameterMap F z₀)) _
      (movingToFixedCover F z₀ p) (movingToFixedCover F z₀ q) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
  obtain ⟨g, rfl⟩ := h
  refine ⟨g, ?_⟩
  exact (movingToFixedCover_period_add F z₀ q.1 g.coeff q.2).symm

public theorem fixedToMovingCover_orbitRel (z₀ : UpperHalfPlane)
    (p q : UpperHalfPlane × ComplexTwoSpace)
    (h : MulAction.orbitRel (FamilyPeriodGroup (fixedParameterMap F z₀)) _ p q) :
    MulAction.orbitRel (FamilyPeriodGroup (parameterMap F)) _
      (fixedToMovingCover F z₀ p) (fixedToMovingCover F z₀ q) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
  obtain ⟨g, rfl⟩ := h
  refine ⟨g, ?_⟩
  exact (fixedToMovingCover_period_add F z₀ q.1 g.coeff q.2).symm

/-- Descended real-period coordinates from the moving torus family to the constant family. -/
@[expose] public def movingToFixedFamily (z₀ : UpperHalfPlane) :
    TotalSpace (parameterMap F) → TotalSpace (fixedParameterMap F z₀) :=
  Quotient.map (movingToFixedCover F z₀) (movingToFixedCover_orbitRel F z₀)

/-- Rebuild the moving torus family from the constant-family real-period coordinates. -/
@[expose] public def fixedToMovingFamily (z₀ : UpperHalfPlane) :
    TotalSpace (fixedParameterMap F z₀) → TotalSpace (parameterMap F) :=
  Quotient.map (fixedToMovingCover F z₀) (fixedToMovingCover_orbitRel F z₀)

@[simp]
public theorem movingToFixedFamily_mk (z₀ : UpperHalfPlane)
    (p : UpperHalfPlane × ComplexTwoSpace) :
    movingToFixedFamily F z₀ (Quotient.mk _ p) =
      Quotient.mk _ (movingToFixedCover F z₀ p) :=
  rfl

@[simp]
public theorem fixedToMovingFamily_mk (z₀ : UpperHalfPlane)
    (p : UpperHalfPlane × ComplexTwoSpace) :
    fixedToMovingFamily F z₀ (Quotient.mk _ p) =
      Quotient.mk _ (fixedToMovingCover F z₀ p) :=
  rfl

/-- The varying-lattice torus family is canonically homeomorphic to its constant real-period
model. -/
@[expose] public def realPeriodFamilyHomeomorph (z₀ : UpperHalfPlane) :
    TotalSpace (parameterMap F) ≃ₜ TotalSpace (fixedParameterMap F z₀) where
  toFun := movingToFixedFamily F z₀
  invFun := fixedToMovingFamily F z₀
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ p => exact congrArg (Quotient.mk _) (fixedToMovingCover_movingToFixedCover F z₀ p)
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ p => exact congrArg (Quotient.mk _) (movingToFixedCover_fixedToMovingCover F z₀ p)
  continuous_toFun := continuous_quot_map
    (movingToFixedCover_orbitRel F z₀) (movingToFixedCover_continuous F z₀)
  continuous_invFun := continuous_quot_map
    (fixedToMovingCover_orbitRel F z₀) (fixedToMovingCover_continuous F z₀)

public theorem fixedFamilyCoverToProduct_respects (z₀ : UpperHalfPlane)
    (p q : UpperHalfPlane × ComplexTwoSpace)
    (h : MulAction.orbitRel (FamilyPeriodGroup (fixedParameterMap F z₀)) _ p q) :
    (p.1, (Quotient.mk _ p.2 : AdditiveTorus (parameterMap F z₀).1)) =
      (q.1, Quotient.mk _ q.2) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, rfl⟩ := h
  apply Prod.ext
  · rfl
  · apply Quotient.sound
    change MulAction.orbitRel (PeriodGroup (parameterMap F z₀).1) _ (g • q).2 q.2
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    let a : PeriodGroup (parameterMap F z₀).1 := Multiplicative.ofAdd
      ⟨periodVector (parameterMap F z₀).1 g.coeff, ⟨g.coeff, rfl⟩⟩
    exact ⟨a, rfl⟩

/-- The constant family quotient mapped to the base times its fixed period torus. -/
@[expose] public def fixedFamilyToProduct (z₀ : UpperHalfPlane) :
    TotalSpace (fixedParameterMap F z₀) →
      UpperHalfPlane × AdditiveTorus (parameterMap F z₀).1 :=
  Quotient.lift (fun p ↦ (p.1, Quotient.mk _ p.2))
    (fixedFamilyCoverToProduct_respects F z₀)

public theorem fixedProductToFamily_respects (z₀ z : UpperHalfPlane)
    (v w : ComplexTwoSpace)
    (h : MulAction.orbitRel (PeriodGroup (parameterMap F z₀).1) _ v w) :
    (Quotient.mk _ (z, v) : TotalSpace (fixedParameterMap F z₀)) =
      Quotient.mk _ (z, w) := by
  apply Quotient.sound
  change MulAction.orbitRel (FamilyPeriodGroup (fixedParameterMap F z₀)) _ (z, v) (z, w)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
  obtain ⟨g, hg⟩ := h
  obtain ⟨n, hn⟩ := g.toAdd.2
  refine ⟨Multiplicative.ofAdd n, ?_⟩
  apply Prod.ext
  · rfl
  · change periodVector (parameterMap F z₀).1 n + w = v
    change periodVector (parameterMap F z₀).1 n = (g.toAdd : ComplexTwoSpace) at hn
    change (g.toAdd : ComplexTwoSpace) + w = v at hg
    rw [hn]
    exact hg

/-- Rebuild the constant family quotient from a base point and a fixed-torus point. -/
@[expose] public def fixedProductToFamily (z₀ : UpperHalfPlane) :
    UpperHalfPlane × AdditiveTorus (parameterMap F z₀).1 →
      TotalSpace (fixedParameterMap F z₀) :=
  fun p ↦ Quotient.lift (fun v ↦ Quotient.mk _ (p.1, v))
    (fixedProductToFamily_respects F z₀ p.1) p.2

@[simp]
public theorem fixedFamilyToProduct_mk (z₀ : UpperHalfPlane)
    (p : UpperHalfPlane × ComplexTwoSpace) :
    fixedFamilyToProduct F z₀ (Quotient.mk _ p) = (p.1, Quotient.mk _ p.2) :=
  rfl

@[simp]
public theorem fixedProductToFamily_mk (z₀ z : UpperHalfPlane) (v : ComplexTwoSpace) :
    fixedProductToFamily F z₀ (z, Quotient.mk _ v) = Quotient.mk _ (z, v) :=
  rfl

public theorem fixedFamilyToProduct_continuous (z₀ : UpperHalfPlane) :
    Continuous (fixedFamilyToProduct F z₀) :=
  continuous_quot_lift (fixedFamilyCoverToProduct_respects F z₀)
    (continuous_fst.prodMk (continuous_quot_mk.comp continuous_snd))

public theorem fixedProductToFamily_continuous (z₀ : UpperHalfPlane) :
    Continuous (fixedProductToFamily F z₀) := by
  let _ : ProperlyDiscontinuousSMul (PeriodGroup (parameterMap F z₀).1) ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul
    (fullRankDomain (parameterMap F z₀))
  let q : ComplexTwoSpace → AdditiveTorus (parameterMap F z₀).1 := Quotient.mk _
  have hq : IsOpenQuotientMap (Prod.map (id : UpperHalfPlane → UpperHalfPlane) q) :=
    IsOpenQuotientMap.id.prodMap
      (MulAction.isOpenQuotientMap_quotientMk
        (Γ := PeriodGroup (parameterMap F z₀).1) (T := ComplexTwoSpace))
  apply hq.isQuotientMap.continuous_iff.mpr
  change Continuous (fun p : UpperHalfPlane × ComplexTwoSpace ↦
    Quotient.mk _ (p.1, p.2))
  exact continuous_quot_mk

/-- A constant period family is canonically the product of its base and fixed torus. -/
@[expose] public def fixedFamilyProductHomeomorph (z₀ : UpperHalfPlane) :
    TotalSpace (fixedParameterMap F z₀) ≃ₜ
      UpperHalfPlane × AdditiveTorus (parameterMap F z₀).1 where
  toFun := fixedFamilyToProduct F z₀
  invFun := fixedProductToFamily F z₀
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ p => rfl
  right_inv p := by
    rcases p with ⟨z, q⟩
    induction q using Quotient.inductionOn with
    | _ v => rfl
  continuous_toFun := fixedFamilyToProduct_continuous F z₀
  continuous_invFun := fixedProductToFamily_continuous F z₀

/-- Unconditional product trivialization of the full varying-lattice torus family. -/
@[expose] public def realPeriodProductHomeomorph (z₀ : UpperHalfPlane) :
    TotalSpace (parameterMap F) ≃ₜ
      UpperHalfPlane × AdditiveTorus (parameterMap F z₀).1 :=
  (realPeriodFamilyHomeomorph F z₀).trans (fixedFamilyProductHomeomorph F z₀)

/-- Whole-family product coordinates centered at the order-three elliptic point. -/
@[expose] public def orderThreeRealPeriodProductHomeomorph :
    TotalSpace (parameterMap F) ≃ₜ
      ComplexUnitDisc × AdditiveTorus (parameterMap F U.zOne).1 :=
  (realPeriodProductHomeomorph F U.zOne).trans
    (orderThreeCayleyHomeomorph.prodCongr
      (Homeomorph.refl (AdditiveTorus (parameterMap F U.zOne).1)))

/-- Whole-family product coordinates centered at the order-four elliptic point. -/
@[expose] public def orderFourRealPeriodProductHomeomorph :
    TotalSpace (parameterMap F) ≃ₜ
      ComplexUnitDisc × AdditiveTorus (parameterMap F U.zTwo).1 :=
  (realPeriodProductHomeomorph F U.zTwo).trans
    (orderFourCayleyHomeomorph.prodCongr
      (Homeomorph.refl (AdditiveTorus (parameterMap F U.zTwo).1)))

public theorem orderThreeRealPeriodProductHomeomorph_fst
    (q : TotalSpace (parameterMap F)) :
    (orderThreeRealPeriodProductHomeomorph F q).1 =
      orderThreeCayleyHomeomorph (familyTotalSpaceBase F q) := by
  induction q using Quotient.inductionOn with
  | _ p => rfl

public theorem orderFourRealPeriodProductHomeomorph_fst
    (q : TotalSpace (parameterMap F)) :
    (orderFourRealPeriodProductHomeomorph F q).1 =
      orderFourCayleyHomeomorph (familyTotalSpaceBase F q) := by
  induction q using Quotient.inductionOn with
  | _ p => rfl

/-- The order-three filling radius is exactly the radial coordinate in the product chart. -/
public theorem orderThreeFamilyRadius_eq_productNorm
    (q : TotalSpace (parameterMap F)) :
    orderThreeFamilyRadius F q =
      ‖((orderThreeRealPeriodProductHomeomorph F q).1 : ℂ)‖ := by
  rw [orderThreeFamilyRadius, orderThreeRealPeriodProductHomeomorph_fst]

/-- The order-four filling radius is exactly the radial coordinate in the product chart. -/
public theorem orderFourFamilyRadius_eq_productNorm
    (q : TotalSpace (parameterMap F)) :
    orderFourFamilyRadius F q =
      ‖((orderFourRealPeriodProductHomeomorph F q).1 : ℂ)‖ := by
  rw [orderFourFamilyRadius, orderFourRealPeriodProductHomeomorph_fst]

/-- Real-period coordinates conjugate the varying order-three deck transport to transport on the
fixed central fibre. -/
public theorem orderThree_movingToFixedCover_deckMap
    (p : UpperHalfPlane × ComplexTwoSpace) :
    movingToFixedCover F U.zOne (deckMap F g₁ p) =
      (U.sourceAction g₁ • p.1,
        periodTransport g₁ (parameterMap F U.zOne)
          (movingToFixedCover F U.zOne p).2) := by
  apply Prod.ext
  · rfl
  · change (fullRankDomain (parameterMap F U.zOne)).realEquiv
        (periodCoordinates (parameterMap F (U.sourceAction g₁ • p.1))
          (periodTransport g₁ (parameterMap F p.1) p.2)) = _
    have hparameter := parameterMap_equivariant F g₁
    change ∀ z, parameterMap F (U.sourceAction g₁ • z) =
      rhoParameters g₁ (parameterMap F z) at hparameter
    have hparam := hparameter p.1
    rw [hparam, periodCoordinates_transport]
    rw [periodTransport]
    change _ = (fullRankDomain (rhoParameters g₁ (parameterMap F U.zOne))).realEquiv _
    rw [parameterMap_zOne_fixed F]
    simp [movingToFixedCover]

/-- The analogous conjugacy for the order-four deck transport. -/
public theorem orderFour_movingToFixedCover_deckMap
    (p : UpperHalfPlane × ComplexTwoSpace) :
    movingToFixedCover F U.zTwo (deckMap F g₂ p) =
      (U.sourceAction g₂ • p.1,
        periodTransport g₂ (parameterMap F U.zTwo)
          (movingToFixedCover F U.zTwo p).2) := by
  apply Prod.ext
  · rfl
  · change (fullRankDomain (parameterMap F U.zTwo)).realEquiv
        (periodCoordinates (parameterMap F (U.sourceAction g₂ • p.1))
          (periodTransport g₂ (parameterMap F p.1) p.2)) = _
    have hparameter := parameterMap_equivariant F g₂
    change ∀ z, parameterMap F (U.sourceAction g₂ • z) =
      rhoParameters g₂ (parameterMap F z) at hparameter
    have hparam := hparameter p.1
    rw [hparam, periodCoordinates_transport]
    rw [periodTransport]
    change _ = (fullRankDomain (rhoParameters g₂ (parameterMap F U.zTwo))).realEquiv _
    rw [parameterMap_zTwo_fixed F]
    simp [movingToFixedCover]

end

end SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
