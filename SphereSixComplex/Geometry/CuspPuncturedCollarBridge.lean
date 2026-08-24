module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions
public import SphereSixComplex.Geometry.GlobalDeckSmoothness
public import SphereSixComplex.Geometry.EstablishedFuchsianCuspNeighborhood
public import SphereSixComplex.Geometry.RegularTorusFamily
public import SphereSixComplex.Geometry.FuchsianRegularTorusFamily
public import Mathlib.Analysis.Complex.CoveringMap

/-!
# The punctured cusp collar and the global torus family

This file compares the exponential coordinates used by the toric cusp filling with the
normalized period coordinates on the punctured global family.
-/

@[expose] public section

noncomputable section

open Matrix Topology

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions
open SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions.BoundedPolydiscRegions
open SphereSixComplex.Geometry.EstablishedFuchsianCuspNeighborhood
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

/-- The two nontrivial columns of the normalized period matrix. -/
public def firstPeriodCoefficients (lambda : ParameterLattice) : IntegerPeriods :=
  ![lambda 0, lambda 1, 0, 0]

/-- The two identity columns of the normalized period matrix. -/
public def identityPeriodCoefficients (n : ParameterLattice) : IntegerPeriods :=
  ![0, 0, n 0, n 1]

/-- First-block coefficients extracted from a four-dimensional period vector. -/
public def firstParameterCoefficients (n : IntegerPeriods) : ParameterLattice :=
  ![n 0, n 1]

/-- Identity-block coefficients extracted from a four-dimensional period vector. -/
public def identityParameterCoefficients (n : IntegerPeriods) : ParameterLattice :=
  ![n 2, n 3]

public theorem integerPeriods_decompose (n : IntegerPeriods) :
    n = firstPeriodCoefficients (firstParameterCoefficients n) +
      identityPeriodCoefficients (identityParameterCoefficients n) := by
  funext i
  fin_cases i <;>
    simp [firstPeriodCoefficients, identityPeriodCoefficients,
      firstParameterCoefficients, identityParameterCoefficients]

/-- Coordinatewise exponential from additive normalized coordinates to the dense torus. -/
public def denseCuspExponential (zeta : ComplexTwoSpace) (s : ℂ) : DenseTorus :=
  ![NormalizedFuchsianCuspCoordinate.exponentialUnit
      (2 * Real.pi * Complex.I * zeta 0),
    NormalizedFuchsianCuspCoordinate.exponentialUnit
      (2 * Real.pi * Complex.I * zeta 1),
    NormalizedFuchsianCuspCoordinate.exponentialUnit
      (2 * Real.pi * Complex.I * s)]

/-- Additive three-coordinate cover used by the explicit cusp exponential. -/
public abbrev AdditiveCuspCover := ComplexTwoSpace × ℂ

public def denseCuspExponentialCover (p : AdditiveCuspCover) : DenseTorus :=
  denseCuspExponential p.1 p.2

private theorem two_pi_mul_I_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

public def scaledExponentialUnit (z : ℂ) : ℂˣ :=
  NormalizedFuchsianCuspCoordinate.exponentialUnit
    (2 * Real.pi * Complex.I * z)

private theorem scaledExponentialUnit_eq (z : ℂ) :
    scaledExponentialUnit z =
      (unitsHomeomorphNeZero (G₀ := ℂ)).symm
        ⟨Complex.exp (2 * Real.pi * Complex.I * z), Complex.exp_ne_zero _⟩ := by
  let e := unitsHomeomorphNeZero (G₀ := ℂ)
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  rfl

private theorem scaledExponentialUnit_isQuotientMap :
    IsQuotientMap scaledExponentialUnit := by
  let e : ℂ ≃ₜ ℂ :=
    Homeomorph.smulOfNeZero (2 * Real.pi * Complex.I) two_pi_mul_I_ne_zero
  have he : IsQuotientMap e := e.isQuotientMap
  have hexp : IsQuotientMap
      (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) :=
    Complex.isAddQuotientCoveringMap_exp.toIsQuotientMap
  have hu : IsQuotientMap (unitsHomeomorphNeZero (G₀ := ℂ)).symm :=
    (unitsHomeomorphNeZero (G₀ := ℂ)).symm.isQuotientMap
  have hcomp := hu.comp (hexp.comp he)
  convert hcomp using 1
  funext z
  rw [scaledExponentialUnit_eq]
  rfl

private theorem scaledExponentialUnit_continuous :
    Continuous scaledExponentialUnit :=
  scaledExponentialUnit_isQuotientMap.continuous

private theorem scaledExponentialUnit_isOpenMap :
    IsOpenMap scaledExponentialUnit := by
  let e : ℂ ≃ₜ ℂ :=
    Homeomorph.smulOfNeZero (2 * Real.pi * Complex.I) two_pi_mul_I_ne_zero
  have hcomp : IsOpenMap
      ((unitsHomeomorphNeZero (G₀ := ℂ)).symm ∘
        (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) ∘ e) :=
    (unitsHomeomorphNeZero (G₀ := ℂ)).symm.isOpenMap.comp
      (Complex.isCoveringMap_exp.isOpenMap.comp e.isOpenMap)
  convert hcomp using 1
  funext z
  rw [scaledExponentialUnit_eq]
  rfl

private theorem scaledExponentialUnit_surjective :
    Function.Surjective scaledExponentialUnit :=
  scaledExponentialUnit_isQuotientMap.surjective

private def additiveCuspCoverProductHomeomorph :
    AdditiveCuspCover ≃ₜ ((ℂ × ℂ) × ℂ) where
  toFun p := ((p.1 0, p.1 1), p.2)
  invFun p := (![(p.1.1 : ℂ), p.1.2], p.2)
  left_inv p := by
    rcases p with ⟨zeta, s⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  right_inv p := by rcases p with ⟨⟨z₀, z₁⟩, s⟩; rfl
  continuous_toFun :=
    ((continuous_apply 0).comp continuous_fst).prodMk
      ((continuous_apply 1).comp continuous_fst) |>.prodMk continuous_snd
  continuous_invFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_fst.comp continuous_fst
      · exact continuous_snd.comp continuous_fst
    · exact continuous_snd

private def denseTorusProductHomeomorph :
    DenseTorus ≃ₜ (((ℂˣ) × ℂˣ) × ℂˣ) where
  toFun x := ((x 0, x 1), x 2)
  invFun p := ![p.1.1, p.1.2, p.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨x₀, x₁⟩, x₂⟩; rfl
  continuous_toFun :=
    (continuous_apply 0).prodMk (continuous_apply 1) |>.prodMk (continuous_apply 2)
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst.comp continuous_fst
    · exact continuous_snd.comp continuous_fst
    · exact continuous_snd

/-- The explicit coordinatewise exponential is a quotient map onto the dense algebraic torus. -/
public theorem denseCuspExponentialCover_isQuotientMap :
    IsQuotientMap denseCuspExponentialCover := by
  let f : ((ℂ × ℂ) × ℂ) → (((ℂˣ) × ℂˣ) × ℂˣ) :=
    Prod.map (Prod.map scaledExponentialUnit scaledExponentialUnit) scaledExponentialUnit
  have hfopen : IsOpenMap f :=
    (scaledExponentialUnit_isOpenMap.prodMap scaledExponentialUnit_isOpenMap).prodMap
      scaledExponentialUnit_isOpenMap
  have hfcont : Continuous f :=
    (scaledExponentialUnit_continuous.prodMap scaledExponentialUnit_continuous).prodMap
      scaledExponentialUnit_continuous
  have hfsurj : Function.Surjective f :=
    (scaledExponentialUnit_surjective.prodMap scaledExponentialUnit_surjective).prodMap
      scaledExponentialUnit_surjective
  have hfquot : IsQuotientMap f := hfopen.isQuotientMap hfcont hfsurj
  have hcomp := denseTorusProductHomeomorph.symm.isQuotientMap.comp
    (hfquot.comp additiveCuspCoverProductHomeomorph.isQuotientMap)
  convert hcomp using 1
  funext p
  rcases p with ⟨zeta, s⟩
  ext i
  fin_cases i <;> rfl

public theorem denseCuspExponentialCover_isOpenMap :
    IsOpenMap denseCuspExponentialCover := by
  let f : ((ℂ × ℂ) × ℂ) → (((ℂˣ) × ℂˣ) × ℂˣ) :=
    Prod.map (Prod.map scaledExponentialUnit scaledExponentialUnit) scaledExponentialUnit
  have hfopen : IsOpenMap f :=
    (scaledExponentialUnit_isOpenMap.prodMap scaledExponentialUnit_isOpenMap).prodMap
      scaledExponentialUnit_isOpenMap
  have hcomp := denseTorusProductHomeomorph.symm.isOpenMap.comp
    (hfopen.comp additiveCuspCoverProductHomeomorph.isOpenMap)
  convert hcomp using 1
  funext p
  rcases p with ⟨zeta, s⟩
  ext i
  fin_cases i <;> rfl

public theorem denseCuspExponentialCover_isOpenQuotientMap :
    IsOpenQuotientMap denseCuspExponentialCover :=
  ⟨denseCuspExponentialCover_isQuotientMap.surjective,
    denseCuspExponentialCover_isQuotientMap.continuous,
    denseCuspExponentialCover_isOpenMap⟩

/-- The quotient of additive normalized coordinates by the exact exponential-fibre relation is
canonically homeomorphic to the dense torus. -/
public noncomputable def additiveCuspQuotientHomeomorph :
    Quotient (Setoid.ker denseCuspExponentialCover) ≃ₜ DenseTorus := by
  let f : C(AdditiveCuspCover, DenseTorus) :=
    ⟨denseCuspExponentialCover, denseCuspExponentialCover_isQuotientMap.continuous⟩
  have hf : IsQuotientMap f := denseCuspExponentialCover_isQuotientMap
  exact hf.homeomorph

/-- The part of the dense torus lying over the punctured radius-`r` disc. -/
public def denseTorusCuspRegion (r : ℝ) : Set DenseTorus :=
  {x | ‖((x 2 : ℂˣ) : ℂ)‖ < r}

/-- The additive cover restricted to the preimage of a punctured torus disc. -/
public def additiveCuspRadiusCover (r : ℝ) : Set AdditiveCuspCover :=
  denseCuspExponentialCover ⁻¹' denseTorusCuspRegion r

public def denseCuspExponentialRadius (r : ℝ) :
    additiveCuspRadiusCover r → denseTorusCuspRegion r :=
  (denseTorusCuspRegion r).restrictPreimage denseCuspExponentialCover

public theorem denseCuspExponentialRadius_isOpenQuotientMap (r : ℝ) :
    IsOpenQuotientMap (denseCuspExponentialRadius r) :=
  denseCuspExponentialCover_isOpenQuotientMap.restrictPreimage _

public noncomputable def additiveCuspRadiusQuotientHomeomorph (r : ℝ) :
    Quotient (Setoid.ker (denseCuspExponentialRadius r)) ≃ₜ denseTorusCuspRegion r := by
  let f : C(additiveCuspRadiusCover r, denseTorusCuspRegion r) :=
    ⟨denseCuspExponentialRadius r,
      (denseCuspExponentialRadius_isOpenQuotientMap r).continuous⟩
  have hf : IsQuotientMap f :=
    (denseCuspExponentialRadius_isOpenQuotientMap r).isQuotientMap
  exact hf.homeomorph

public noncomputable def torusNonzeroHomeomorph (M : Model) :
    DenseTorus ≃ₜ {p : M.Carrier // M.t p ≠ 0} :=
  M.torus_openEmbedding.toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr M.torus_range)

public noncomputable def torusNonzeroRadiusHomeomorph (M : Model) (r : ℝ) :
    denseTorusCuspRegion r ≃ₜ
      {p : {q : M.Carrier // M.t q ≠ 0} // ‖M.t p‖ < r} :=
  (torusNonzeroHomeomorph M).subtype fun x ↦ by
    change ‖((x 2 : ℂˣ) : ℂ)‖ < r ↔
      ‖M.t (M.torusEmbedding x)‖ < r
    rw [M.t_torus]

public def nestedNonzeroRadiusHomeomorph (M : Model) (r : ℝ) :
    {p : {q : M.Carrier // M.t q ≠ 0} // ‖M.t p‖ < r} ≃ₜ
      {p : LocalCarrier M r // M.t p ≠ 0} where
  toFun p := ⟨⟨p.1.1, by
    rw [mem_cuspNeighborhood_iff, mem_ball_zero_iff]
    exact p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, by
    exact mem_ball_zero_iff.mp p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- Dense-torus coordinates identify a punctured toric cusp disc with the corresponding open
subdomain of `(C×)³`. -/
public noncomputable def torusPuncturedLocalHomeomorph (M : Model) (r : ℝ) :
    denseTorusCuspRegion r ≃ₜ {p : LocalCarrier M r // M.t p ≠ 0} :=
  (torusNonzeroRadiusHomeomorph M r).trans (nestedNonzeroRadiusHomeomorph M r)

/-- Additive normalized coordinates modulo their exact exponential fibres give the punctured
local toric carrier. -/
public noncomputable def additiveToPuncturedLocalHomeomorph (M : Model) (r : ℝ) :
    Quotient (Setoid.ker (denseCuspExponentialRadius r)) ≃ₜ
      {p : LocalCarrier M r // M.t p ≠ 0} :=
  (additiveCuspRadiusQuotientHomeomorph r).trans (torusPuncturedLocalHomeomorph M r)

@[simp]
public theorem denseCuspExponential_apply_zero (zeta : ComplexTwoSpace) (s : ℂ) :
    denseCuspExponential zeta s 0 =
      NormalizedFuchsianCuspCoordinate.exponentialUnit
        (2 * Real.pi * Complex.I * zeta 0) := rfl

@[simp]
public theorem denseCuspExponential_apply_one (zeta : ComplexTwoSpace) (s : ℂ) :
    denseCuspExponential zeta s 1 =
      NormalizedFuchsianCuspCoordinate.exponentialUnit
        (2 * Real.pi * Complex.I * zeta 1) := rfl

@[simp]
public theorem denseCuspExponential_apply_two (zeta : ComplexTwoSpace) (s : ℂ) :
    denseCuspExponential zeta s 2 =
      NormalizedFuchsianCuspCoordinate.exponentialUnit
        (2 * Real.pi * Complex.I * s) := rfl

/-- The third exponential coordinate is exactly the normalized cusp parameter. -/
public theorem denseCuspExponential_last (zeta : ComplexTwoSpace) (s : ℂ) :
    (((denseCuspExponential zeta s 2 : ℂˣ) : ℂ)) = cuspQ s := by
  rfl

public theorem norm_cuspQ (s : ℂ) :
    ‖cuspQ s‖ = Real.exp (-2 * Real.pi * s.im) := by
  rw [cuspQ, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

public theorem mem_cuspHalfPlane_of_norm_cuspQ_lt
    {H r : ℝ} {s : ℂ} (hr : r ≤ cuspRadius H) (hq : ‖cuspQ s‖ < r) :
    s ∈ cuspHalfPlane H := by
  have hexp : Real.exp (-2 * Real.pi * s.im) <
      Real.exp (-2 * Real.pi * H) := by
    rw [← norm_cuspQ, ← cuspRadius]
    exact hq.trans_le hr
  have hlinear := Real.exp_lt_exp.mp hexp
  have hpi : 0 < Real.pi := Real.pi_pos
  change H < s.im
  nlinarith

public theorem additiveCuspRadiusCover_halfPlane
    {H r : ℝ} (hr : r ≤ cuspRadius H) (p : additiveCuspRadiusCover r) :
    p.1.2 ∈ cuspHalfPlane H := by
  apply mem_cuspHalfPlane_of_norm_cuspQ_lt hr
  exact p.2

/-- The first two period columns evaluate to the `2 × 2` period block. -/
public theorem periodVector_firstPeriodCoefficients (x : Parameters)
    (lambda : ParameterLattice) :
    periodVector x (firstPeriodCoefficients lambda) =
      (periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) := by
  have hcoeff : (fun j ↦ ((firstPeriodCoefficients lambda j : ℤ) : ℂ)) =
      ![(lambda 0 : ℂ), (lambda 1 : ℂ), 0, 0] := by
    funext j
    fin_cases j <;> simp [firstPeriodCoefficients]
  have hlambda : (fun i ↦ (lambda i : ℂ)) =
      ![(lambda 0 : ℂ), (lambda 1 : ℂ)] := by
    funext i
    fin_cases i <;> rfl
  rw [periodVector, hcoeff, hlambda, periodBlock_mulVec]
  ext i
  fin_cases i <;> simp [periodMatrix, Matrix.mulVec]

/-- The identity period columns are ordinary integral translations in the two additive fibre
coordinates. -/
public theorem periodVector_identityPeriodCoefficients (x : Parameters)
    (n : ParameterLattice) :
    periodVector x (identityPeriodCoefficients n) = fun i ↦ (n i : ℂ) := by
  have hcoeff : (fun j ↦ ((identityPeriodCoefficients n j : ℤ) : ℂ)) =
      ![(0 : ℂ), 0, (n 0 : ℂ), (n 1 : ℂ)] := by
    funext j
    fin_cases j <;> simp [identityPeriodCoefficients]
  rw [periodVector, hcoeff]
  ext i
  fin_cases i <;> simp [periodMatrix, Matrix.mulVec]

public theorem exponentialUnit_add_int (z : ℂ) (n : ℤ) :
    NormalizedFuchsianCuspCoordinate.exponentialUnit
        (2 * Real.pi * Complex.I * (z + (n : ℂ))) =
      NormalizedFuchsianCuspCoordinate.exponentialUnit
        (2 * Real.pi * Complex.I * z) := by
  apply Units.ext
  simp only [NormalizedFuchsianCuspCoordinate.exponentialUnit, Units.val_mk0]
  rw [show 2 * Real.pi * Complex.I * (z + (n : ℂ)) =
    2 * Real.pi * Complex.I * z +
      (2 * Real.pi * Complex.I) * (n : ℂ) by ring,
    Complex.exp_add]
  rw [mul_comm (2 * Real.pi * Complex.I) (n : ℂ),
    Complex.exp_int_mul_two_pi_mul_I]
  simp

public theorem scaledExponentialUnit_eq_iff (z w : ℂ) :
    scaledExponentialUnit z = scaledExponentialUnit w ↔
      ∃ n : ℤ, z = w + n := by
  constructor
  · intro h
    have hval := congrArg Units.val h
    change Complex.exp (2 * Real.pi * Complex.I * z) =
      Complex.exp (2 * Real.pi * Complex.I * w) at hval
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hval
    refine ⟨n, ?_⟩
    have hzero : (2 * Real.pi * Complex.I) * (z - (w + (n : ℂ))) = 0 := by
      calc
        (2 * Real.pi * Complex.I) * (z - (w + (n : ℂ))) =
            2 * Real.pi * Complex.I * z -
              2 * Real.pi * Complex.I * w -
                (n : ℂ) * (2 * Real.pi * Complex.I) := by ring
        _ = 0 := by rw [hn]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left two_pi_mul_I_ne_zero)
  · rintro ⟨n, rfl⟩
    exact exponentialUnit_add_int w n

public theorem denseCuspExponentialCover_eq_iff (p q : AdditiveCuspCover) :
    denseCuspExponentialCover p = denseCuspExponentialCover q ↔
      ∃ n₀ n₁ n₂ : ℤ,
        p.1 0 = q.1 0 + n₀ ∧ p.1 1 = q.1 1 + n₁ ∧ p.2 = q.2 + n₂ := by
  constructor
  · intro h
    obtain ⟨n₀, hn₀⟩ := (scaledExponentialUnit_eq_iff (p.1 0) (q.1 0)).mp
      (congrFun h 0)
    obtain ⟨n₁, hn₁⟩ := (scaledExponentialUnit_eq_iff (p.1 1) (q.1 1)).mp
      (congrFun h 1)
    obtain ⟨n₂, hn₂⟩ := (scaledExponentialUnit_eq_iff p.2 q.2).mp
      (congrFun h 2)
    exact ⟨n₀, n₁, n₂, hn₀, hn₁, hn₂⟩
  · rintro ⟨n₀, n₁, n₂, hn₀, hn₁, hn₂⟩
    ext i
    fin_cases i
    · exact congrArg Units.val ((scaledExponentialUnit_eq_iff _ _).mpr ⟨n₀, hn₀⟩)
    · exact congrArg Units.val ((scaledExponentialUnit_eq_iff _ _).mpr ⟨n₁, hn₁⟩)
    · exact congrArg Units.val ((scaledExponentialUnit_eq_iff _ _).mpr ⟨n₂, hn₂⟩)

public theorem exponentialUnit_period_split (c z s : ℂ) (n : ℤ) :
    NormalizedFuchsianCuspCoordinate.exponentialUnit
        (2 * Real.pi * Complex.I * (s * (n : ℂ) + c + z)) =
      NormalizedFuchsianCuspCoordinate.exponentialUnit
          (2 * Real.pi * Complex.I * c) *
        (NormalizedFuchsianCuspCoordinate.exponentialUnit
            (2 * Real.pi * Complex.I * z) *
          NormalizedFuchsianCuspCoordinate.exponentialUnit
              (2 * Real.pi * Complex.I * s) ^ n) := by
  apply Units.ext
  change Complex.exp (2 * Real.pi * Complex.I * (s * (n : ℂ) + c + z)) =
    Complex.exp (2 * Real.pi * Complex.I * c) *
      (Complex.exp (2 * Real.pi * Complex.I * z) *
        (Units.coeHom ℂ)
          (NormalizedFuchsianCuspCoordinate.exponentialUnit
            (2 * Real.pi * Complex.I * s) ^ n))
  rw [map_zpow]
  change Complex.exp (2 * Real.pi * Complex.I * (s * (n : ℂ) + c + z)) =
    Complex.exp (2 * Real.pi * Complex.I * c) *
      (Complex.exp (2 * Real.pi * Complex.I * z) *
        Complex.exp (2 * Real.pi * Complex.I * s) ^ n)
  rw [← Complex.exp_int_mul]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

public theorem B₀Complex_mulVec_cast (lambda : ParameterLattice) :
    NormalizedFuchsianCuspCoordinate.B₀Complex.mulVec (fun i ↦ (lambda i : ℂ)) =
      fun i ↦ (shearVector lambda i : ℂ) := by
  funext i
  simpa [NormalizedFuchsianCuspCoordinate.B₀Complex, shearVector] using
    (RingHom.map_mulVec (Int.castRingHom ℂ) SphereSixComplex.LatticeData.B₀ lambda i).symm

/-- On the normalized cusp lift, the first period block is the integral shear term plus the
holomorphic correction term. -/
public theorem periodBlock_mulVec_cusp
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (lambda : ParameterLattice) :
    (periodBlock (periodValues
        (assembledFuchsianPeriodFunctions E D).tau
        (assembledFuchsianPeriodFunctions E D).mu
        (assembledFuchsianPeriodFunctions E D).beta (N.lift s))).mulVec
          (fun i ↦ (lambda i : ℂ)) =
      fun i ↦ s * (shearVector lambda i : ℂ) +
        (N.correctionMatrix (cuspQ s)).mulVec (fun j ↦ (lambda j : ℂ)) i := by
  rw [N.periodBlock_eq_smul_B₀_add_correction s hs]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, B₀Complex_mulVec_cast]
  rfl

/-- Integer translations in the additive fibre coordinates disappear under the exponential. -/
public theorem denseCuspExponential_add_int
    (zeta : ComplexTwoSpace) (s : ℂ) (n : ParameterLattice) :
    denseCuspExponential (zeta + fun i ↦ (n i : ℂ)) s =
      denseCuspExponential zeta s := by
  ext i
  fin_cases i
  · simpa [denseCuspExponential] using
      congrArg Units.val (exponentialUnit_add_int (zeta 0) (n 0))
  · simpa [denseCuspExponential] using
      congrArg Units.val (exponentialUnit_add_int (zeta 1) (n 1))
  · simp [denseCuspExponential]

/-- The normalized period translation becomes the phase-corrected integral toric shear after
coordinatewise exponentiation. -/
public theorem denseCuspExponential_periodBlock
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (zeta : ComplexTwoSpace)
    (lambda : ParameterLattice) :
    denseCuspExponential
        ((periodBlock (periodValues
            (assembledFuchsianPeriodFunctions E D).tau
            (assembledFuchsianPeriodFunctions E D).mu
            (assembledFuchsianPeriodFunctions E D).beta (N.lift s))).mulVec
              (fun i ↦ (lambda i : ℂ)) + zeta) s =
      phaseEmbedding (N.phaseCoefficient lambda (cuspQ s)) *
        denseTorusShear lambda (denseCuspExponential zeta s) := by
  rw [periodBlock_mulVec_cusp N s hs lambda]
  ext i
  fin_cases i
  · simpa [denseCuspExponential, phaseEmbedding,
      NormalizedFuchsianCuspCoordinate.phaseCoefficient, denseTorusShear,
      _root_.add_apply] using
      congrArg Units.val
        (exponentialUnit_period_split
          ((N.correctionMatrix (cuspQ s)).mulVec (fun j ↦ (lambda j : ℂ)) 0)
          (zeta 0) s (shearVector lambda 0))
  · simpa [denseCuspExponential, phaseEmbedding,
      NormalizedFuchsianCuspCoordinate.phaseCoefficient, denseTorusShear,
      _root_.add_apply] using
      congrArg Units.val
        (exponentialUnit_period_split
          ((N.correctionMatrix (cuspQ s)).mulVec (fun j ↦ (lambda j : ℂ)) 1)
          (zeta 1) s (shearVector lambda 1))
  · simp [denseCuspExponential, phaseEmbedding, denseTorusShear]

/-- The explicit exponential point in the punctured part of a local toric cusp disc. -/
public def localCuspExponentialPoint (M : Model) (r : ℝ)
    (zeta : ComplexTwoSpace) (s : ℂ) (hs : cuspQ s ∈ Metric.ball (0 : ℂ) r) :
    LocalCarrier M r :=
  ⟨M.torusEmbedding (denseCuspExponential zeta s), by
    change M.t (M.torusEmbedding (denseCuspExponential zeta s)) ∈ Metric.ball 0 r
    rw [M.t_torus, denseCuspExponential_last]
    exact hs⟩

@[simp]
public theorem localCuspExponentialPoint_coe (M : Model) (r : ℝ)
    (zeta : ComplexTwoSpace) (s : ℂ) (hs : cuspQ s ∈ Metric.ball (0 : ℂ) r) :
    (localCuspExponentialPoint M r zeta s hs : M.Carrier) =
      M.torusEmbedding (denseCuspExponential zeta s) :=
  rfl

@[simp]
public theorem localCuspExponentialPoint_t (M : Model) (r : ℝ)
    (zeta : ComplexTwoSpace) (s : ℂ) (hs : cuspQ s ∈ Metric.ball (0 : ℂ) r) :
    M.t (localCuspExponentialPoint M r zeta s hs) = cuspQ s := by
  rw [localCuspExponentialPoint_coe, M.t_torus, denseCuspExponential_last]

/-- Inclusion of a smaller toric cusp disc into a larger one. -/
public def localCarrierInclusion (M : Model) {r R : ℝ} (hrR : r ≤ R) :
    LocalCarrier M r → LocalCarrier M R :=
  fun p ↦ ⟨p, by
    rw [mem_cuspNeighborhood_iff, mem_ball_zero_iff]
    exact (mem_ball_zero_iff.mp p.property).trans_le hrR⟩

public theorem localCarrierInclusion_continuous (M : Model) {r R : ℝ} (hrR : r ≤ R) :
    Continuous (localCarrierInclusion M hrR) :=
  continuous_subtype_val.subtype_mk _

public theorem localCarrierInclusion_psiMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (hRradius : R ≤ cuspRadius N.height) (lambda : ParameterLattice)
    (p : LocalCarrier M r) :
    localCarrierInclusion M hrR
        ((CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
          N M r hr (hrR.trans hRradius)).psiMap lambda p) =
      (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M R hR hRradius).psiMap lambda (localCarrierInclusion M hrR p) := by
  apply Subtype.ext
  change (((CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M r hr (hrR.trans hRradius)).psiMap lambda p : LocalCarrier M r) : M.Carrier) =
    (((CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M R hR hRradius).psiMap lambda (localCarrierInclusion M hrR p) :
        LocalCarrier M R) : M.Carrier)
  rw [CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_coe,
    CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_coe]
  rfl

/-- Freeness and compact-overlap estimates restrict from a cusp disc to any smaller positive
disc. -/
public noncomputable def restrictActualLocalCuspQuotientWitness
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualLocalCuspQuotientWitness N M) (r : ℝ)
    (hr : 0 < r) (hrW : r ≤ W.radius) :
    ActualLocalCuspQuotientWitness N M where
  radius := r
  radius_pos := hr
  radius_le := hrW.trans W.radius_le
  fixedPoint := by
    constructor
    · intro lambda p hp hfixed
      apply W.fixedPoint.offCentral lambda (localCarrierInclusion M hrW p) hp
      rw [← localCarrierInclusion_psiMap N M hr W.radius_pos hrW W.radius_le]
      exact congrArg (localCarrierInclusion M hrW) hfixed
    · intro lambda p hp hfixed
      apply W.fixedPoint.central lambda (localCarrierInclusion M hrW p) hp
      rw [← localCarrierInclusion_psiMap N M hr W.radius_pos hrW W.radius_le]
      exact congrArg (localCarrierInclusion M hrW) hfixed
  compactOverlap := by
    intro K L hK hL
    let i := localCarrierInclusion M hrW
    have hKi : IsCompact (i '' K) := hK.image (localCarrierInclusion_continuous M hrW)
    have hLi : IsCompact (i '' L) := hL.image (localCarrierInclusion_continuous M hrW)
    apply (W.compactOverlap (i '' K) (i '' L) hKi hLi).subset
    rintro lambda ⟨y, ⟨x, hxK, hxy⟩, hyL⟩
    refine ⟨i y, ⟨i x, ⟨x, hxK, rfl⟩, ?_⟩, ⟨y, hyL, rfl⟩⟩
    rw [← localCarrierInclusion_psiMap N M hr W.radius_pos hrW W.radius_le,
      hxy]

/-- One common radius carrying both the actual toric quotient estimates and a precisely
invariant regular Fuchsian horodisc. -/
public structure ActualPuncturedCuspCollarWitness
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) where
  localWitness : ActualLocalCuspQuotientWitness N M
  region_open : IsOpen (normalizedCuspRegion N localWitness.radius)
  region_regular : normalizedCuspRegion N localWitness.radius ⊆
    {z | IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) z}
  orbitClosure_region_regular : closure (⋃ g : Delta,
      (fun z : UpperHalfPlane ↦
        E.modularParameter.toTriangleUniformization.sourceAction g • z) ''
          normalizedCuspRegion N localWitness.radius) ⊆
    {z | IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) z}
  translates_meet_only_parabolic : ∀ g : Delta,
    ((fun z : UpperHalfPlane ↦
        E.modularParameter.toTriangleUniformization.sourceAction g • z) ''
        normalizedCuspRegion N localWitness.radius ∩
          normalizedCuspRegion N localWitness.radius).Nonempty →
      ∃ k : ℤ, g = g₀ ^ k

/-- The standard separated-horodisc theorem can be shrunk to the already constructed toric
quotient radius, so no independent or incompatible radius is introduced. -/
public theorem exists_actualPuncturedCuspCollarWitness
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualLocalCuspQuotientWitness N M) :
    Nonempty (ActualPuncturedCuspCollarWitness N M) := by
  obtain ⟨H⟩ := EstablishedFuchsianCuspNeighborhood.Established.data
    N W.radius W.radius_pos
  let W' := restrictActualLocalCuspQuotientWitness W H.radius H.radius_pos H.radius_le_upper
  exact ⟨⟨W', H.region_open, H.region_regular, H.orbitClosure_region_regular,
    H.translates_meet_only_parabolic⟩⟩

namespace ActualPuncturedCuspCollarWitness

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

public theorem lift_regular (W : ActualPuncturedCuspCollarWitness N M)
    {s : ℂ} (hs : s ∈ cuspHalfPlane N.height)
    (hq : ‖cuspQ s‖ < W.localWitness.radius) :
    IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift s) := by
  apply W.region_regular
  exact ⟨s, ⟨hs, hq⟩, rfl⟩

public theorem closure_region_regular (W : ActualPuncturedCuspCollarWitness N M) :
    closure (normalizedCuspRegion N W.localWitness.radius) ⊆
      {z | IsRegularBasePoint
        (U := E.modularParameter.toTriangleUniformization) z} := by
  have hsub : normalizedCuspRegion N W.localWitness.radius ⊆ ⋃ g : Delta,
      (fun z : UpperHalfPlane ↦
        E.modularParameter.toTriangleUniformization.sourceAction g • z) ''
          normalizedCuspRegion N W.localWitness.radius := by
    apply Set.subset_iUnion_of_subset (1 : Delta)
    intro z hz
    exact ⟨z, hz, by simp⟩
  intro z hz
  exact W.orbitClosure_region_regular (closure_mono hsub hz)

end ActualPuncturedCuspCollarWitness

/-- The open vector-bundle region lying over the selected normalized horodisc. -/
public abbrev regularCuspBundleRegion
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :=
  {p : RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace //
    p.1.1 ∈ normalizedCuspRegion N W.localWitness.radius}

/-- Normalized additive coordinates are homeomorphic to the regular vector-bundle region over
the chosen horodisc. -/
public noncomputable def additiveCuspBundleHomeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    additiveCuspRadiusCover W.localWitness.radius ≃ₜ regularCuspBundleRegion W where
  toFun p := ⟨(⟨N.lift p.1.2,
      W.lift_regular
        (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2⟩, p.1.1),
    ⟨p.1.2,
      ⟨additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p, p.2⟩, rfl⟩⟩
  invFun p := ⟨(p.1.2,
      (((assembledFuchsianPeriodFunctions E D).tau p.1.1.1 : UpperHalfPlane) : ℂ)), by
    change ‖cuspQ
      (((assembledFuchsianPeriodFunctions E D).tau p.1.1.1 : UpperHalfPlane) : ℂ)‖ <
        W.localWitness.radius
    obtain ⟨s, ⟨hs, hq⟩, hlift⟩ := p.2
    have htau : (((assembledFuchsianPeriodFunctions E D).tau p.1.1.1 :
        UpperHalfPlane) : ℂ) = s := by
      rw [← hlift]
      exact N.lift_tau s hs
    simpa only [htau] using hq⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact N.lift_tau p.1.2
        (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change N.lift
        (((assembledFuchsianPeriodFunctions E D).tau p.1.1.1 : UpperHalfPlane) : ℂ) =
          p.1.1.1
      obtain ⟨s, ⟨hs, hq⟩, hlift⟩ := p.2
      have htau : (((assembledFuchsianPeriodFunctions E D).tau p.1.1.1 :
          UpperHalfPlane) : ℂ) = s := by
        rw [← hlift]
        exact N.lift_tau s hs
      rw [htau, hlift]
    · rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hlift : Continuous (fun p : additiveCuspRadiusCover W.localWitness.radius ↦
        N.lift p.1.2) :=
      N.lift_holomorphic.continuousOn.comp_continuous
        (continuous_snd.comp continuous_subtype_val)
        (fun p ↦ additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p)
    exact (hlift.subtype_mk _).prodMk
      (continuous_fst.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_snd.comp continuous_subtype_val).prodMk
      (UpperHalfPlane.continuous_coe.comp
        ((assembledFuchsianPeriodFunctions E D).tau_holomorphic.continuous.comp
          (continuous_subtype_val.comp
            (continuous_fst.comp continuous_subtype_val))))

public theorem additiveCuspBundleMap_isOpenEmbedding
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenEmbedding (fun p : additiveCuspRadiusCover W.localWitness.radius ↦
      (additiveCuspBundleHomeomorph W p).1) := by
  have hopen : IsOpen
      {p : RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace |
        p.1.1 ∈ normalizedCuspRegion N W.localWitness.radius} :=
    W.region_open.preimage (continuous_subtype_val.comp continuous_fst)
  exact hopen.isOpenEmbedding_subtypeVal.comp
    (additiveCuspBundleHomeomorph W).isOpenEmbedding

/-- The open part of the regular varying torus family lying over the selected normalized
horodisc. -/
public def regularCuspFamilyRegion
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Set (RegularTotalSpace (assembledFuchsianPeriodFunctions E D)) :=
  {x | (regularTotalSpaceBase (assembledFuchsianPeriodFunctions E D) x : UpperHalfPlane) ∈
    normalizedCuspRegion N W.localWitness.radius}

public theorem regularCuspFamilyRegion_isOpen
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpen (regularCuspFamilyRegion W) := by
  exact W.region_open.preimage
    (continuous_subtype_val.comp
      (regularTotalSpaceBase_continuous (assembledFuchsianPeriodFunctions E D)))

/-- The cusp collar inside the actual `PuncturedGlobalFamily`, defined as the image of the
selected regular horodisc. -/
public def puncturedGlobalCuspCollar
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Set (PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D)) :=
  let _ := regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
  quotientProjection '' regularCuspFamilyRegion W

/-- The actual global cusp collar is open. -/
public theorem puncturedGlobalCuspCollar_isOpen
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpen (puncturedGlobalCuspCollar W) := by
  let _ : MulAction Delta
      (RegularTotalSpace (assembledFuchsianPeriodFunctions E D)) :=
    regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let _ : ContinuousConstSMul Delta
      (RegularTotalSpace (assembledFuchsianPeriodFunctions E D)) :=
    regularFamilyDeckAction_continuousConstSMul
      (assembledFuchsianPeriodFunctions E D) hproper
  let q : RegularTotalSpace (assembledFuchsianPeriodFunctions E D) →
      PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) := quotientProjection
  have hq : IsOpenMap q := by
    dsimp only [q]
    rw [quotientProjection.eq_def]
    exact isOpenMap_quotient_mk'_mul
  exact hq _ (regularCuspFamilyRegion_isOpen W)

/-- The additive first-period translation is exactly the actual local cusp action under the
explicit exponential map. -/
public theorem localCuspExponentialPoint_period_equivariant
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (hr : 0 < r) (hradius : r ≤ cuspRadius N.height)
    (s : ℂ) (hs : s ∈ cuspHalfPlane N.height)
    (hsr : cuspQ s ∈ Metric.ball (0 : ℂ) r)
    (zeta : ComplexTwoSpace) (lambda : ParameterLattice) :
    let C := CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M r hr hradius
    C.psiMap lambda (localCuspExponentialPoint M r zeta s hsr) =
      localCuspExponentialPoint M r
        ((periodBlock (periodValues
            (assembledFuchsianPeriodFunctions E D).tau
            (assembledFuchsianPeriodFunctions E D).mu
            (assembledFuchsianPeriodFunctions E D).beta (N.lift s))).mulVec
              (fun i ↦ (lambda i : ℂ)) + zeta) s hsr := by
  dsimp only
  apply Subtype.ext
  rw [CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_coe]
  rw [localCuspExponentialPoint_coe, localCuspExponentialPoint_coe]
  rw [CuspToricPhaseAction.ToricModel.phaseAction_apply, M.fanShear_torus,
    M.torusAction_torus]
  rw [M.t_torus, denseCuspExponential_last]
  change M.torusEmbedding
      (phaseEmbedding (N.phaseCoefficient lambda (cuspQ s)) *
        denseTorusShear lambda (denseCuspExponential zeta s)) = _
  exact congrArg M.torusEmbedding (denseCuspExponential_periodBlock N s hs zeta lambda).symm

/-- A normalized cusp coordinate in the regular additive vector-bundle cover. -/
public def regularCuspBundlePoint
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hregular : IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift s))
    (zeta : ComplexTwoSpace) :
    RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace :=
  (⟨N.lift s, hregular⟩, zeta)

/-- The corresponding point of the normalized varying torus family. -/
public noncomputable def regularCuspFamilyPoint
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hregular : IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift s))
    (zeta : ComplexTwoSpace) :
    RegularTotalSpace (assembledFuchsianPeriodFunctions E D) :=
  Quotient.mk _ (regularCuspBundlePoint N s hregular zeta)

/-- Integral period translations give the same point in the varying torus fibre. -/
public theorem regularCuspFamilyPoint_period
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hregular : IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift s))
    (zeta : ComplexTwoSpace) (n : IntegerPeriods) :
    regularCuspFamilyPoint N s hregular
        (periodVector (periodValues
            (assembledFuchsianPeriodFunctions E D).tau
            (assembledFuchsianPeriodFunctions E D).mu
            (assembledFuchsianPeriodFunctions E D).beta (N.lift s)) n + zeta) =
      regularCuspFamilyPoint N s hregular zeta := by
  apply Quotient.sound
  change MulAction.orbitRel
    (FamilyPeriodGroup (regularParameterMap (assembledFuchsianPeriodFunctions E D))) _
      (regularCuspBundlePoint N s hregular
        (periodVector (periodValues
            (assembledFuchsianPeriodFunctions E D).tau
            (assembledFuchsianPeriodFunctions E D).mu
            (assembledFuchsianPeriodFunctions E D).beta (N.lift s)) n + zeta))
      (regularCuspBundlePoint N s hregular zeta)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨Multiplicative.ofAdd n, ?_⟩
  apply Prod.ext
  · rfl
  · rfl

/-- The normalized additive cusp coordinate mapped into the actual global punctured family. -/
public noncomputable def puncturedGlobalCuspPoint
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hregular : IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift s))
    (zeta : ComplexTwoSpace) :
    PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) :=
  Quotient.mk _ (regularCuspFamilyPoint N s hregular zeta)

/-- Translation by one normalized cusp period is the parabolic deck transformation and hence
disappears in the global triangle-group quotient. -/
public theorem puncturedGlobalCuspPoint_shift
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height)
    (hregular : IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift s))
    (hregularShift : IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift (s - 1)))
    (zeta : ComplexTwoSpace) :
    puncturedGlobalCuspPoint N (s - 1) hregularShift zeta =
      puncturedGlobalCuspPoint N s hregular zeta := by
  let _ : MulAction Delta
      (RegularTotalSpace (assembledFuchsianPeriodFunctions E D)) :=
    regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
  apply Quotient.sound
  change MulAction.orbitRel Delta _
    (regularCuspFamilyPoint N (s - 1) hregularShift zeta)
    (regularCuspFamilyPoint N s hregular zeta)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨g₀, ?_⟩
  change regularFamilyDeckMap (assembledFuchsianPeriodFunctions E D) g₀
      (Quotient.mk _ (regularCuspBundlePoint N s hregular zeta)) =
    Quotient.mk _ (regularCuspBundlePoint N (s - 1) hregularShift zeta)
  rw [regularFamilyDeckMap_mk]
  apply Quotient.sound
  change MulAction.orbitRel
    (FamilyPeriodGroup (regularParameterMap (assembledFuchsianPeriodFunctions E D))) _
      (regularDeckMap (assembledFuchsianPeriodFunctions E D) g₀
        (regularCuspBundlePoint N s hregular zeta))
      (regularCuspBundlePoint N (s - 1) hregularShift zeta)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨1, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    simpa [regularCuspBundlePoint, regularDeckMap] using N.lift_shift s hs
  · simp [regularCuspBundlePoint, regularDeckMap, periodTransport_gZero]

/-- The explicit normalized additive coordinate mapped to the actual global family, using the
regularity supplied by the selected cusp collar witness. -/
public noncomputable def actualPuncturedGlobalCuspPoint
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (zeta : ComplexTwoSpace) :
    PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) :=
  puncturedGlobalCuspPoint N s (W.lift_regular hs hq) zeta

public theorem actualPuncturedGlobalCuspPoint_mem_collar
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (zeta : ComplexTwoSpace) :
    actualPuncturedGlobalCuspPoint W s hs hq zeta ∈
      puncturedGlobalCuspCollar W := by
  let _ : MulAction Delta
      (RegularTotalSpace (assembledFuchsianPeriodFunctions E D)) :=
    regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
  refine ⟨regularCuspFamilyPoint N s (W.lift_regular hs hq) zeta, ?_, rfl⟩
  change ((regularTotalSpaceBase (assembledFuchsianPeriodFunctions E D)
    (regularCuspFamilyPoint N s (W.lift_regular hs hq) zeta) :
      RegularBase (U := E.modularParameter.toTriangleUniformization)) : UpperHalfPlane) ∈
        normalizedCuspRegion N W.localWitness.radius
  rw [regularCuspFamilyPoint.eq_def, regularTotalSpaceBase_mk]
  exact ⟨s, ⟨hs, hq⟩, rfl⟩

public theorem cuspQ_add_int (s : ℂ) (n : ℤ) :
    cuspQ (s + n) = cuspQ s := by
  exact congrArg Units.val (exponentialUnit_add_int s n)

public theorem cuspHalfPlane_add_int {H : ℝ} {s : ℂ}
    (hs : s ∈ cuspHalfPlane H) (n : ℤ) : s + n ∈ cuspHalfPlane H := by
  change H < (s + (n : ℂ)).im
  simpa [cuspHalfPlane] using hs

/-- Iterating the normalized shift identifies every integral logarithm translate with the
corresponding power of the parabolic generator. -/
public theorem lift_sub_int
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (k : ℤ) :
    N.lift (s - k) =
      E.modularParameter.toTriangleUniformization.sourceAction (g₀ ^ k) • N.lift s := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hsPrev : s - (n : ℤ) ∈ cuspHalfPlane N.height := by
        simpa [sub_eq_add_neg] using cuspHalfPlane_add_int hs (-(n : ℤ))
      have hcalc : N.lift (s - ((n : ℂ) + 1)) =
          E.modularParameter.toTriangleUniformization.sourceAction
              (g₀ ^ ((n : ℤ) + 1)) • N.lift s := by
        calc
        N.lift (s - ((n : ℂ) + 1)) = N.lift ((s - (n : ℂ)) - 1) := by
          congr 1
          ring
        _ = E.modularParameter.toTriangleUniformization.sourceAction g₀ •
            N.lift (s - (n : ℤ)) := N.lift_shift _ hsPrev
        _ = E.modularParameter.toTriangleUniformization.sourceAction g₀ •
            (E.modularParameter.toTriangleUniformization.sourceAction (g₀ ^ (n : ℤ)) •
              N.lift s) :=
          congrArg _ ih
        _ = E.modularParameter.toTriangleUniformization.sourceAction
              (g₀ ^ ((n : ℤ) + 1)) • N.lift s := by
          rw [show g₀ ^ ((n : ℤ) + 1) = g₀ * g₀ ^ (n : ℤ) by
            calc
              g₀ ^ ((n : ℤ) + 1) = g₀ ^ (1 + (n : ℤ)) := by congr 1; omega
              _ = g₀ ^ (1 : ℤ) * g₀ ^ (n : ℤ) :=
                _root_.zpow_add g₀ 1 (n : ℤ)
              _ = g₀ * g₀ ^ (n : ℤ) := by rw [zpow_one]]
          simp [map_mul, mul_smul]
      simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hcalc

  | pred n ih =>
      have hsNext : s - (-(n : ℤ) - 1) ∈ cuspHalfPlane N.height := by
        convert cuspHalfPlane_add_int hs ((n : ℤ) + 1) using 1
        push_cast
        ring
      have hshift : N.lift (s - ((-(n : ℤ) : ℤ) : ℂ)) =
          E.modularParameter.toTriangleUniformization.sourceAction g₀ •
            N.lift (s - ((-(n : ℤ) - 1 : ℤ) : ℂ)) := by
        have h := N.lift_shift (s - (-(n : ℤ) - 1)) hsNext
        have heq : s - (-(n : ℂ) - 1) - 1 = s - (-(n : ℂ)) := by ring
        push_cast at h
        rw [heq] at h
        simpa only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one] using h
      have hback : N.lift (s - (-(n : ℤ) - 1)) =
          E.modularParameter.toTriangleUniformization.sourceAction g₀⁻¹ •
            N.lift (s - (-(n : ℤ))) := by
        have h := congrArg (fun z ↦
          E.modularParameter.toTriangleUniformization.sourceAction g₀⁻¹ • z) hshift
        simpa [map_inv, inv_smul_smul] using h.symm
      have hcalc : N.lift (s - (((-(n : ℤ) - 1 : ℤ) : ℂ))) =
          E.modularParameter.toTriangleUniformization.sourceAction
              (g₀ ^ (-(n : ℤ) - 1)) • N.lift s := by
        calc
        N.lift (s - (((-(n : ℤ) - 1 : ℤ) : ℂ))) =
            E.modularParameter.toTriangleUniformization.sourceAction g₀⁻¹ •
              N.lift (s - (-(n : ℤ))) := by
          simpa only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one] using hback
        _ = E.modularParameter.toTriangleUniformization.sourceAction g₀⁻¹ •
            (E.modularParameter.toTriangleUniformization.sourceAction
              (g₀ ^ (-(n : ℤ))) • N.lift s) := by
          apply congrArg _
          simpa only [Int.cast_neg, Int.cast_natCast] using ih
        _ = E.modularParameter.toTriangleUniformization.sourceAction
              (g₀ ^ (-(n : ℤ) - 1)) • N.lift s := by
          rw [show g₀ ^ (-(n : ℤ) - 1) = g₀⁻¹ * g₀ ^ (-(n : ℤ)) by
            rw [show -(n : ℤ) - 1 = -1 + -(n : ℤ) by ring,
              _root_.zpow_add]
            simp]
          simp [map_mul, mul_smul]
      simpa only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one] using hcalc

/-- Canonical fibre transport is trivial on the whole parabolic cyclic subgroup. -/
public theorem periodTransport_gZero_zpow (k : ℤ) (x : PeriodDomain) :
    periodTransport (g₀ ^ k) x = 1 := by
  have hinv : ∀ y : PeriodDomain, periodTransport g₀⁻¹ y = 1 := by
    intro y
    have h := periodTransport_mul g₀ g₀⁻¹ y
    rw [mul_inv_cancel, periodTransport_one, periodTransport_gZero] at h
    simpa using h.symm
  induction k using Int.induction_on generalizing x with
  | zero => exact periodTransport_one x
  | succ n ih =>
      rw [_root_.zpow_add_one, periodTransport_mul, ih,
        periodTransport_gZero, mul_one]
  | pred n ih =>
      rw [show g₀ ^ (-(n : ℤ) - 1) = g₀ ^ (-(n : ℤ)) * g₀⁻¹ by
        rw [show -(n : ℤ) - 1 = -(n : ℤ) + -1 by ring,
          _root_.zpow_add]
        simp]
      rw [periodTransport_mul, ih, hinv, mul_one]

/-- All integral choices of the logarithm of the cusp parameter define the same global-family
point. -/
public theorem actualPuncturedGlobalCuspPoint_add_int
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (zeta : ComplexTwoSpace) (n : ℤ)
    (hsn : s + n ∈ cuspHalfPlane N.height)
    (hqn : ‖cuspQ (s + n)‖ < W.localWitness.radius) :
    actualPuncturedGlobalCuspPoint W (s + n) hsn hqn zeta =
      actualPuncturedGlobalCuspPoint W s hs hq zeta := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hn : s + (((n : ℤ) + 1 : ℤ) : ℂ) - 1 = s + (n : ℂ) := by
        push_cast
        ring
      have hsPrev : s + (n : ℂ) ∈ cuspHalfPlane N.height :=
        cuspHalfPlane_add_int hs n
      have hqPrev : ‖cuspQ (s + (n : ℂ))‖ < W.localWitness.radius := by
        have hc := cuspQ_add_int s (n : ℤ)
        exact congrArg norm hc ▸ hq
      have hsShift : s + (((n : ℤ) + 1 : ℤ) : ℂ) - 1 ∈
          cuspHalfPlane N.height := hn.symm ▸ hsPrev
      have hqShift : ‖cuspQ (s + (((n : ℤ) + 1 : ℤ) : ℂ) - 1)‖ <
          W.localWitness.radius := hn.symm ▸ hqPrev
      have hshift := puncturedGlobalCuspPoint_shift N
        (s + (((n : ℤ) + 1 : ℤ) : ℂ)) hsn
        (W.lift_regular hsn hqn)
        (W.lift_regular hsShift hqShift) zeta
      have hstep :
          actualPuncturedGlobalCuspPoint W
              (s + (((n : ℤ) + 1 : ℤ) : ℂ)) hsn hqn zeta =
            actualPuncturedGlobalCuspPoint W (s + (n : ℂ)) hsPrev hqPrev zeta := by
        change puncturedGlobalCuspPoint N _ _ _ = puncturedGlobalCuspPoint N _ _ _
        simpa only [hn] using hshift.symm
      exact hstep.trans (ih hsPrev hqPrev)
  | pred n ih =>
      have hn : s + ((-(n : ℤ) : ℤ) : ℂ) - 1 =
          s + ((-(n : ℤ) - 1 : ℤ) : ℂ) := by
        push_cast
        ring
      have hsCurrent : s + ((-(n : ℤ) : ℤ) : ℂ) ∈ cuspHalfPlane N.height :=
        cuspHalfPlane_add_int hs (-(n : ℤ))
      have hqCurrent : ‖cuspQ (s + ((-(n : ℤ) : ℤ) : ℂ))‖ <
          W.localWitness.radius := by
        have hc := cuspQ_add_int s (-(n : ℤ))
        exact congrArg norm hc ▸ hq
      have hsShift : s + ((-(n : ℤ) : ℤ) : ℂ) - 1 ∈
          cuspHalfPlane N.height := hn.symm ▸ hsn
      have hqShift : ‖cuspQ (s + ((-(n : ℤ) : ℤ) : ℂ) - 1)‖ <
          W.localWitness.radius := hn.symm ▸ hqn
      have hshift := puncturedGlobalCuspPoint_shift N
        (s + ((-(n : ℤ) : ℤ) : ℂ)) hsCurrent
        (W.lift_regular hsCurrent hqCurrent)
        (W.lift_regular hsShift hqShift) zeta
      have hstep :
          actualPuncturedGlobalCuspPoint W
              (s + ((-(n : ℤ) - 1 : ℤ) : ℂ)) hsn hqn zeta =
            actualPuncturedGlobalCuspPoint W
              (s + ((-(n : ℤ) : ℤ) : ℂ)) hsCurrent hqCurrent zeta := by
        change puncturedGlobalCuspPoint N _ _ _ = puncturedGlobalCuspPoint N _ _ _
        simpa only [hn] using hshift
      exact hstep.trans (ih hsCurrent hqCurrent)

public theorem actualPuncturedGlobalCuspPoint_add_fibre_int
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (zeta : ComplexTwoSpace) (n : ParameterLattice) :
    actualPuncturedGlobalCuspPoint W s hs hq
        (zeta + fun i ↦ (n i : ℂ)) =
      actualPuncturedGlobalCuspPoint W s hs hq zeta := by
  change Quotient.mk _
      (regularCuspFamilyPoint N s (W.lift_regular hs hq)
        (zeta + fun i ↦ (n i : ℂ))) =
    Quotient.mk _ (regularCuspFamilyPoint N s (W.lift_regular hs hq) zeta)
  apply congrArg (Quotient.mk _)
  simpa [periodVector_identityPeriodCoefficients, add_comm] using
    regularCuspFamilyPoint_period N s (W.lift_regular hs hq) zeta
      (identityPeriodCoefficients n)

public theorem actualPuncturedGlobalCuspPoint_congr
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) {s s' : ℂ}
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (hs' : s' ∈ cuspHalfPlane N.height) (hq' : ‖cuspQ s'‖ < W.localWitness.radius)
    (zeta : ComplexTwoSpace) (h : s = s') :
    actualPuncturedGlobalCuspPoint W s hs hq zeta =
      actualPuncturedGlobalCuspPoint W s' hs' hq' zeta := by
  subst s'
  rfl

public theorem actualPuncturedGlobalCuspPoint_periodBlock
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (zeta : ComplexTwoSpace) (lambda : ParameterLattice) :
    actualPuncturedGlobalCuspPoint W s hs hq
        ((periodBlock (periodValues
            (assembledFuchsianPeriodFunctions E D).tau
            (assembledFuchsianPeriodFunctions E D).mu
            (assembledFuchsianPeriodFunctions E D).beta (N.lift s))).mulVec
              (fun i ↦ (lambda i : ℂ)) + zeta) =
      actualPuncturedGlobalCuspPoint W s hs hq zeta := by
  change Quotient.mk _
      (regularCuspFamilyPoint N s (W.lift_regular hs hq)
        ((periodBlock (periodValues
            (assembledFuchsianPeriodFunctions E D).tau
            (assembledFuchsianPeriodFunctions E D).mu
            (assembledFuchsianPeriodFunctions E D).beta (N.lift s))).mulVec
              (fun i ↦ (lambda i : ℂ)) + zeta)) =
    Quotient.mk _ (regularCuspFamilyPoint N s (W.lift_regular hs hq) zeta)
  apply congrArg (Quotient.mk _)
  simpa [periodVector_firstPeriodCoefficients] using
    regularCuspFamilyPoint_period N s (W.lift_regular hs hq) zeta
      (firstPeriodCoefficients lambda)

/-- The normalized additive cover map into the actual global collar. -/
public noncomputable def additiveCuspCoverToGlobal
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    additiveCuspRadiusCover W.localWitness.radius →
      PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) :=
  fun p ↦ actualPuncturedGlobalCuspPoint W p.1.2
    (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2 p.1.1

/-- The additive cusp map is exactly the composite of the two defining family quotients on the
normalized regular bundle chart. -/
public theorem additiveCuspCoverToGlobal_eq_quotientProjections
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    letI := regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
    additiveCuspCoverToGlobal W p =
      (quotientProjection : RegularTotalSpace (assembledFuchsianPeriodFunctions E D) →
        PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D))
        ((projection
          (regularParameterMap (assembledFuchsianPeriodFunctions E D)) :
            RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace →
              RegularTotalSpace (assembledFuchsianPeriodFunctions E D))
          ((additiveCuspBundleHomeomorph W p).1)) := by
  let _ := regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
  unfold additiveCuspCoverToGlobal actualPuncturedGlobalCuspPoint
    puncturedGlobalCuspPoint regularCuspFamilyPoint
  rw [TorusFamily.projection.eq_def, quotientProjection.eq_def]
  rfl

public theorem additiveCuspCoverToGlobal_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (additiveCuspCoverToGlobal W) := by
  let S := additiveCuspRadiusCover W.localWitness.radius
  have hlift : Continuous (fun p : S ↦ N.lift p.1.2) :=
    N.lift_holomorphic.continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val)
      (fun p ↦ additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p)
  have hbase : Continuous (fun p : S ↦
      (⟨N.lift p.1.2,
        W.lift_regular
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2⟩ :
        RegularBase (U := E.modularParameter.toTriangleUniformization))) :=
    hlift.subtype_mk _
  have hbundle : Continuous (fun p : S ↦
      (regularCuspBundlePoint N p.1.2
        (W.lift_regular
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2) p.1.1)) :=
    hbase.prodMk (continuous_fst.comp continuous_subtype_val)
  change Continuous (fun p : S ↦ Quotient.mk _ (Quotient.mk _
    (regularCuspBundlePoint N p.1.2
      (W.lift_regular
        (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2) p.1.1)))
  exact continuous_quot_mk.comp (continuous_quot_mk.comp hbundle)

public theorem additiveCuspCoverToGlobal_isOpenMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenMap (additiveCuspCoverToGlobal W) := by
  let F := assembledFuchsianPeriodFunctions E D
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let _ := familyContinuousConstSMul (regularParameterMap F)
    (fun a ↦ (periodSection_contMDiff F a 0).continuous.comp continuous_subtype_val)
  let _ := regularFamilyDeckAction F
  let _ : ContinuousConstSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_continuousConstSMul F hproper
  let _ : Setoid (RegularBase (U := E.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :=
    MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _
  let _ : Setoid (RegularTotalSpace F) :=
    MulAction.orbitRel Delta _
  let q₁ : RegularBase (U := E.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace → RegularTotalSpace F := quotientProjection
  let q₂ : RegularTotalSpace F → PuncturedGlobalFamily F := quotientProjection
  have hq₁ : IsOpenMap q₁ := by
    dsimp only [q₁]
    rw [quotientProjection.eq_def]
    change IsOpenMap (Quotient.mk' : _ →
      Quotient (MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _))
    exact isOpenMap_quotient_mk'_mul
  have hq₂ : IsOpenMap q₂ := by
    dsimp only [q₂]
    rw [quotientProjection.eq_def]
    change IsOpenMap (Quotient.mk' : _ →
      Quotient (MulAction.orbitRel Delta (RegularTotalSpace F)))
    exact isOpenMap_quotient_mk'_mul
  have hopen := hq₂.comp (hq₁.comp (additiveCuspBundleMap_isOpenEmbedding W).isOpenMap)
  convert hopen using 1
  funext p
  rfl

public theorem additiveCuspCoverToGlobal_respects
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p q : additiveCuspRadiusCover W.localWitness.radius)
    (h : Setoid.ker (denseCuspExponentialRadius W.localWitness.radius) p q) :
    additiveCuspCoverToGlobal W p = additiveCuspCoverToGlobal W q := by
  have hdense : denseCuspExponentialCover p.1 = denseCuspExponentialCover q.1 :=
    congrArg Subtype.val h
  obtain ⟨n₀, n₁, n₂, hn₀, hn₁, hn₂⟩ :=
    (denseCuspExponentialCover_eq_iff p.1 q.1).mp hdense
  let n : ParameterLattice := ![n₀, n₁]
  have hzeta : p.1.1 = q.1.1 + fun i ↦ (n i : ℂ) := by
    funext i
    fin_cases i
    · exact hn₀
    · exact hn₁
  have hsQ : q.1.2 ∈ cuspHalfPlane N.height :=
    additiveCuspRadiusCover_halfPlane W.localWitness.radius_le q
  have hqQ : ‖cuspQ q.1.2‖ < W.localWitness.radius := q.2
  have hsAdd : q.1.2 + n₂ ∈ cuspHalfPlane N.height :=
    cuspHalfPlane_add_int hsQ n₂
  have hqAdd : ‖cuspQ (q.1.2 + n₂)‖ < W.localWitness.radius := by
    have hc := cuspQ_add_int q.1.2 n₂
    exact congrArg norm hc ▸ hqQ
  calc
    additiveCuspCoverToGlobal W p =
        actualPuncturedGlobalCuspPoint W p.1.2
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2 q.1.1 := by
      rw [additiveCuspCoverToGlobal, hzeta]
      exact actualPuncturedGlobalCuspPoint_add_fibre_int W _ _ _ _ n
    _ = actualPuncturedGlobalCuspPoint W (q.1.2 + n₂) hsAdd hqAdd q.1.1 :=
      actualPuncturedGlobalCuspPoint_congr W _ _ _ _ _ hn₂
    _ = actualPuncturedGlobalCuspPoint W q.1.2 hsQ hqQ q.1.1 :=
      actualPuncturedGlobalCuspPoint_add_int W q.1.2 hsQ hqQ q.1.1 n₂ _ _
    _ = additiveCuspCoverToGlobal W q := rfl

/-- Descent of the normalized additive cover through its exact exponential-fibre relation. -/
public noncomputable def additiveCuspQuotientToGlobal
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Quotient (Setoid.ker (denseCuspExponentialRadius W.localWitness.radius)) →
      PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) :=
  Quotient.lift (additiveCuspCoverToGlobal W) (additiveCuspCoverToGlobal_respects W)

public theorem additiveCuspQuotientToGlobal_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (additiveCuspQuotientToGlobal W) :=
  continuous_quot_lift (additiveCuspCoverToGlobal_respects W)
    (additiveCuspCoverToGlobal_continuous W)

public theorem additiveCuspQuotientToGlobal_isOpenMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenMap (additiveCuspQuotientToGlobal W) := by
  apply IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective
  convert additiveCuspCoverToGlobal_isOpenMap W using 1
  funext p
  rfl

@[simp]
public theorem additiveCuspQuotientToGlobal_mk
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    additiveCuspQuotientToGlobal W (Quotient.mk _ p) =
      additiveCuspCoverToGlobal W p :=
  rfl

public theorem additiveToPuncturedLocalHomeomorph_mk
    (M : Model) (r : ℝ) (p : additiveCuspRadiusCover r) :
    ((additiveToPuncturedLocalHomeomorph M r (Quotient.mk _ p)).1 :
      LocalCarrier M r) =
      localCuspExponentialPoint M r p.1.1 p.1.2
        (mem_ball_zero_iff.mpr p.2) := by
  apply Subtype.ext
  rfl

/-- Before dividing by the phase-corrected parameter-lattice action, the punctured local toric
carrier maps continuously to the global cusp collar. -/
public noncomputable def puncturedLocalCuspPrequotientMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} →
      PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) :=
  additiveCuspQuotientToGlobal W ∘
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius).symm

public theorem puncturedLocalCuspPrequotientMap_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (puncturedLocalCuspPrequotientMap W) :=
  (additiveCuspQuotientToGlobal_continuous W).comp
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius).symm.continuous

public theorem puncturedLocalCuspPrequotientMap_isOpenMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenMap (puncturedLocalCuspPrequotientMap W) :=
  (additiveCuspQuotientToGlobal_isOpenMap W).comp
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius).symm.isOpenMap

/-- The actual phase-corrected action restricted to the punctured local carrier. -/
public noncomputable def puncturedPsiMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (lambda : ParameterLattice) :
    {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} →
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
  fun p ↦ ⟨
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le).psiMap
        lambda p.1,
    by
      rw [CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_preserves_t]
      exact p.2⟩

/-- The prequotient map is invariant under the actual phase-corrected parameter-lattice
action. -/
public theorem puncturedLocalCuspPrequotientMap_psiMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (lambda : ParameterLattice)
    (p : {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0}) :
    puncturedLocalCuspPrequotientMap W (puncturedPsiMap W lambda p) =
      puncturedLocalCuspPrequotientMap W p := by
  let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
  obtain ⟨q, rfl⟩ := e.surjective p
  induction q using Quotient.inductionOn with
  | _ a =>
    let zeta' :=
      (periodBlock (periodValues
        (assembledFuchsianPeriodFunctions E D).tau
        (assembledFuchsianPeriodFunctions E D).mu
        (assembledFuchsianPeriodFunctions E D).beta (N.lift a.1.2))).mulVec
          (fun i ↦ (lambda i : ℂ)) + a.1.1
    let a' : additiveCuspRadiusCover W.localWitness.radius :=
      ⟨(zeta', a.1.2), by exact a.2⟩
    have hlocal : puncturedPsiMap W lambda (e (Quotient.mk _ a)) =
        e (Quotient.mk _ a') := by
      apply Subtype.ext
      change
        (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
            N M W.localWitness.radius W.localWitness.radius_pos
              W.localWitness.radius_le).psiMap lambda (e (Quotient.mk _ a)).1 =
          (e (Quotient.mk _ a')).1
      rw [show ((e (Quotient.mk _ a)).1 : LocalCarrier M W.localWitness.radius) =
          localCuspExponentialPoint M W.localWitness.radius a.1.1 a.1.2
            (mem_ball_zero_iff.mpr a.2) from
        additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius a,
        show ((e (Quotient.mk _ a')).1 : LocalCarrier M W.localWitness.radius) =
          localCuspExponentialPoint M W.localWitness.radius a'.1.1 a'.1.2
            (mem_ball_zero_iff.mpr a'.2) from
        additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius a']
      exact localCuspExponentialPoint_period_equivariant N M
        W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
        a.1.2 (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a)
        (mem_ball_zero_iff.mpr a.2) a.1.1 lambda
    rw [hlocal]
    dsimp only [puncturedLocalCuspPrequotientMap, Function.comp_apply, e]
    rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
    rw [additiveCuspQuotientToGlobal_mk, additiveCuspQuotientToGlobal_mk]
    exact actualPuncturedGlobalCuspPoint_periodBlock W a.1.2
      (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a) a.2 a.1.1 lambda

/-- The actual local cusp action on the complement of the central fibre. -/
@[instance_reducible] public noncomputable def puncturedPsiAction
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    MulAction (Multiplicative ParameterLattice)
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} where
  smul lambda p := puncturedPsiMap W (Multiplicative.toAdd lambda) p
  one_smul p := by
    apply Subtype.ext
    exact CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_zero _ _
  mul_smul lambda mu p := by
    apply Subtype.ext
    exact CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_add
      _ (Multiplicative.toAdd lambda) (Multiplicative.toAdd mu) p.1

/-- The orbit relation of the phase-corrected action on the punctured local carrier. -/
public noncomputable def puncturedPsiOrbitRel
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Setoid {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
  letI := puncturedPsiAction W
  MulAction.orbitRel (Multiplicative ParameterLattice) _

/-- The punctured part of the actual local cusp quotient. -/
public noncomputable abbrev puncturedLocalCuspQuotient
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :=
  Quotient (puncturedPsiOrbitRel W)

/-- The actual phase-corrected action on the full local toric cusp, including its central
fibre. -/
@[instance_reducible] public noncomputable def actualLocalPsiAction
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) where
  smul lambda p :=
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le).psiMap
        (Multiplicative.toAdd lambda) p
  one_smul p :=
    CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_zero _ p
  mul_smul lambda mu p :=
    CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_add _
      (Multiplicative.toAdd lambda) (Multiplicative.toAdd mu) p

public noncomputable def actualLocalPsiOrbitRel
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Setoid (LocalCarrier M W.localWitness.radius) :=
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  letI := (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  MulAction.orbitRel (Multiplicative ParameterLattice) _

/-- The full actual local cusp filling at the common quantitative radius. -/
public noncomputable abbrev actualLocalCuspFilling
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :=
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  letI := (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  MulAction.orbitRel.Quotient (Multiplicative ParameterLattice)
    (LocalCarrier M W.localWitness.radius)

/-- Inclusion of the punctured collar quotient into the full local cusp filling. -/
public noncomputable def puncturedLocalCuspToFilling
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    puncturedLocalCuspQuotient W → actualLocalCuspFilling W :=
  Quotient.lift (fun p ↦ Quotient.mk _ p.1) (by
    intro p q h
    let _ : MulAction (Multiplicative ParameterLattice)
        {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} := puncturedPsiAction W
    change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q at h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨lambda, hlambda⟩ := h
    apply Quotient.sound
    let C :=
      CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
        N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
    let _ : MulAction (Multiplicative ParameterLattice)
        (LocalCarrier M W.localWitness.radius) :=
      (C.toCuspActionData W.localWitness.fixedPoint).psiAction
    change MulAction.orbitRel (Multiplicative ParameterLattice) _ p.1 q.1
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨lambda, ?_⟩
    change puncturedPsiMap W (Multiplicative.toAdd lambda) q = p at hlambda
    rw [show lambda = Multiplicative.ofAdd (Multiplicative.toAdd lambda) from rfl,
      (C.toCuspActionData W.localWitness.fixedPoint).psi_smul,
      ← C.psiMap_eq_generic W.localWitness.fixedPoint]
    exact congrArg Subtype.val hlambda)

@[simp]
public theorem puncturedLocalCuspToFilling_mk
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0}) :
    puncturedLocalCuspToFilling W (Quotient.mk _ p) = Quotient.mk _ p.1 :=
  rfl

public theorem puncturedLocalCuspToFilling_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (puncturedLocalCuspToFilling W) :=
  continuous_quot_lift _ (continuous_quot_mk.comp continuous_subtype_val)

public theorem puncturedLocalCuspToFilling_injective
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Function.Injective (puncturedLocalCuspToFilling W) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ p =>
    induction y using Quotient.inductionOn with
    | _ q =>
      apply Quotient.sound
      have hrel := Quotient.exact hxy
      let C :=
        CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
          N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
      let _ : MulAction (Multiplicative ParameterLattice)
          (LocalCarrier M W.localWitness.radius) :=
        (C.toCuspActionData W.localWitness.fixedPoint).psiAction
      change MulAction.orbitRel (Multiplicative ParameterLattice) _ p.1 q.1 at hrel
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
      obtain ⟨lambda, hlambda⟩ := hrel
      rw [show lambda = Multiplicative.ofAdd (Multiplicative.toAdd lambda) from rfl,
        (C.toCuspActionData W.localWitness.fixedPoint).psi_smul] at hlambda
      let _ : MulAction (Multiplicative ParameterLattice)
          {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} := puncturedPsiAction W
      change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨lambda, ?_⟩
      apply Subtype.ext
      exact (C.psiMap_eq_generic W.localWitness.fixedPoint _ _).trans hlambda

public theorem puncturedLocalCuspToFilling_isOpenMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenMap (puncturedLocalCuspToFilling W) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) := ⟨by
    intro lambda
    rw [show lambda = Multiplicative.ofAdd (Multiplicative.toAdd lambda) from rfl]
    change Continuous ((C.toCuspActionData W.localWitness.fixedPoint).psiMap
      (Multiplicative.toAdd lambda))
    exact (C.genericPsiMap_holomorphic W.localWitness.fixedPoint _).continuous⟩
  let _ : Setoid (LocalCarrier M W.localWitness.radius) :=
    MulAction.orbitRel (Multiplicative ParameterLattice) _
  have ht : Continuous (fun p : LocalCarrier M W.localWitness.radius ↦ M.t p) :=
    M.t_holomorphic.continuous.comp continuous_subtype_val
  have hopen : IsOpen {p : LocalCarrier M W.localWitness.radius | M.t p ≠ 0} :=
    isOpen_compl_singleton.preimage ht
  have hpre : IsOpenMap (fun p :
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} ↦
        (Quotient.mk _ p.1 : actualLocalCuspFilling W)) := by
    have hquot : IsOpenMap (Quotient.mk' : LocalCarrier M W.localWitness.radius →
        actualLocalCuspFilling W) := isOpenMap_quotient_mk'_mul
    exact hquot.comp hopen.isOpenMap_subtype_val
  apply IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective
  convert hpre using 1
  funext p
  rfl

public theorem puncturedLocalCuspToFilling_isOpenEmbedding
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenEmbedding (puncturedLocalCuspToFilling W) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (puncturedLocalCuspToFilling_continuous W)
    (puncturedLocalCuspToFilling_injective W)
    (puncturedLocalCuspToFilling_isOpenMap W)

/-- The punctured collar in the full local cusp filling. -/
public def actualLocalCuspFillingCollar
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Set (actualLocalCuspFilling W) :=
  Set.range (puncturedLocalCuspToFilling W)

public theorem actualLocalCuspFillingCollar_isOpen
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpen (actualLocalCuspFillingCollar W) :=
  (puncturedLocalCuspToFilling_isOpenEmbedding W).isOpen_range

/-- The quotient atlas on the full local cusp filling. -/
@[instance_reducible]
public noncomputable def actualLocalCuspFillingCharts
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    ChartedSpace ComplexModel (actualLocalCuspFilling W) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  let hf := W.localWitness.quotient_isQuotientCoveringMap
  exact hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective

public theorem actualLocalCuspFilling_isManifold
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := actualLocalCuspFillingCharts W
    IsManifold (modelWithCornersSelf ℂ ComplexModel)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (actualLocalCuspFilling W) := by
  let _ := actualLocalCuspFillingCharts W
  exact W.localWitness.quotient_isManifold

public theorem actualLocalCuspFilling_projection_isLocalDiffeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := actualLocalCuspFillingCharts W
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Quotient.mk _ : LocalCarrier M W.localWitness.radius →
        actualLocalCuspFilling W) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  let _ : LocallyCompactSpace M.Carrier :=
    ChartedSpace.locallyCompactSpace ComplexModel M.Carrier
  let _ : LocallyCompactSpace (LocalCarrier M W.localWitness.radius) :=
    (cuspNeighborhood M W.localWitness.radius).isOpen.locallyCompactSpace
  let hf := W.localWitness.quotient_isQuotientCoveringMap
  let hdeck : ∀ gamma : Multiplicative ParameterLattice,
      ContMDiff (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : LocalCarrier M W.localWitness.radius ↦ gamma • p) := by
    intro gamma
    convert C.genericPsiMap_holomorphic W.localWitness.fixedPoint
      (Multiplicative.toAdd gamma) using 1
    funext p
    exact (C.toCuspActionData W.localWitness.fixedPoint).psi_smul
      (Multiplicative.toAdd gamma) p
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    ⟨fun gamma ↦ (hdeck gamma).continuous⟩
  let _ := actualLocalCuspFillingCharts W
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (actualLocalCuspFilling W) := actualLocalCuspFilling_isManifold W
  exact CuspFilling.quotient_projection_isLocalDiffeomorph
    (modelWithCornersSelf ℂ ComplexModel) hf hdeck

/-- The punctured local quotient map into the actual global family. -/
public noncomputable def puncturedLocalCuspQuotientMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    puncturedLocalCuspQuotient W →
      PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) :=
  Quotient.lift (puncturedLocalCuspPrequotientMap W) (by
    intro p q h
    let _ := puncturedPsiAction W
    change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q at h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨lambda, hlambda⟩ := h
    change puncturedPsiMap W (Multiplicative.toAdd lambda) q = p at hlambda
    rw [← hlambda]
    exact puncturedLocalCuspPrequotientMap_psiMap W _ q)

@[simp]
public theorem puncturedLocalCuspQuotientMap_mk
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0}) :
    puncturedLocalCuspQuotientMap W (Quotient.mk _ p) =
      puncturedLocalCuspPrequotientMap W p :=
  rfl

public theorem puncturedLocalCuspQuotientMap_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (puncturedLocalCuspQuotientMap W) :=
  continuous_quot_lift _ (puncturedLocalCuspPrequotientMap_continuous W)

public theorem puncturedLocalCuspQuotientMap_isOpenMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenMap (puncturedLocalCuspQuotientMap W) := by
  apply IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective
  convert puncturedLocalCuspPrequotientMap_isOpenMap W using 1
  funext p
  rfl

private theorem additiveCuspRepresentatives_deck_data
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : additiveCuspRadiusCover W.localWitness.radius)
    (h : additiveCuspCoverToGlobal W a = additiveCuspCoverToGlobal W b) :
    ∃ k : ℤ, N.lift (b.1.2 - k) = N.lift a.1.2 ∧
      regularFamilyDeckMap (assembledFuchsianPeriodFunctions E D) (g₀ ^ k)
          (regularCuspFamilyPoint N b.1.2
            (W.lift_regular
              (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) b.2) b.1.1) =
        regularCuspFamilyPoint N a.1.2
          (W.lift_regular
            (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a) a.2) a.1.1 := by
  let F := assembledFuchsianPeriodFunctions E D
  let _ := regularFamilyDeckAction F
  have horbit := Quotient.exact h
  change MulAction.orbitRel Delta (RegularTotalSpace F) _ _ at horbit
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
  obtain ⟨g, hg⟩ := horbit
  change regularFamilyDeckMap F g
      (regularCuspFamilyPoint N b.1.2
        (W.lift_regular
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) b.2) b.1.1) =
    regularCuspFamilyPoint N a.1.2
      (W.lift_regular
        (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a) a.2) a.1.1 at hg
  have hbase := congrArg (regularTotalSpaceBase F) hg
  simp only [regularCuspFamilyPoint] at hbase
  have hmeet :
      ((E.modularParameter.toTriangleUniformization.sourceAction g • ·) ''
          normalizedCuspRegion N W.localWitness.radius ∩
        normalizedCuspRegion N W.localWitness.radius).Nonempty := by
    refine ⟨N.lift a.1.2, ?_, ?_⟩
    · refine ⟨N.lift b.1.2, ⟨b.1.2, ⟨?_, b.2⟩, rfl⟩, ?_⟩
      · exact additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b
      · exact congrArg Subtype.val hbase
    · exact ⟨a.1.2,
        ⟨additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a, a.2⟩, rfl⟩
  obtain ⟨k, rfl⟩ := W.translates_meet_only_parabolic g hmeet
  refine ⟨k, ?_, hg⟩
  exact (lift_sub_int N b.1.2
    (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) k).trans
      (congrArg Subtype.val hbase)

private theorem additiveCuspRepresentatives_period_data
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : additiveCuspRadiusCover W.localWitness.radius)
    (h : additiveCuspCoverToGlobal W a = additiveCuspCoverToGlobal W b) :
    ∃ k : ℤ, a.1.2 = b.1.2 - k ∧ ∃ n : IntegerPeriods,
      periodVector (periodValues
          (assembledFuchsianPeriodFunctions E D).tau
          (assembledFuchsianPeriodFunctions E D).mu
          (assembledFuchsianPeriodFunctions E D).beta (N.lift a.1.2)) n + a.1.1 = b.1.1 := by
  obtain ⟨k, hlift, hdeck⟩ := additiveCuspRepresentatives_deck_data W a b h
  have hsSub : b.1.2 - k ∈ cuspHalfPlane N.height := by
    simpa [sub_eq_add_neg] using cuspHalfPlane_add_int
      (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) (-k)
  have hs : a.1.2 = b.1.2 - k := by
    calc
      a.1.2 = (((assembledFuchsianPeriodFunctions E D).tau (N.lift a.1.2) :
          UpperHalfPlane) : ℂ) :=
        (N.lift_tau a.1.2
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a)).symm
      _ = (((assembledFuchsianPeriodFunctions E D).tau (N.lift (b.1.2 - k)) :
          UpperHalfPlane) : ℂ) := congrArg (fun z ↦
        (((assembledFuchsianPeriodFunctions E D).tau z : UpperHalfPlane) : ℂ)) hlift.symm
      _ = b.1.2 - k := N.lift_tau (b.1.2 - k) hsSub
  let F := assembledFuchsianPeriodFunctions E D
  have hinner := Quotient.exact hdeck
  change MulAction.orbitRel
      (FamilyPeriodGroup (regularParameterMap F)) _
      (regularDeckMap F (g₀ ^ k)
        (regularCuspBundlePoint N b.1.2
          (W.lift_regular
            (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) b.2) b.1.1))
      (regularCuspBundlePoint N a.1.2
        (W.lift_regular
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a) a.2) a.1.1) at hinner
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hinner
  obtain ⟨n, hn⟩ := hinner
  have hsnd := congrArg Prod.snd hn
  rw [family_smul_snd] at hsnd
  change periodVector (regularParameterMap F _).1 n.coeff + a.1.1 =
    periodTransport (g₀ ^ k) _ b.1.1 at hsnd
  rw [periodTransport_gZero_zpow] at hsnd
  refine ⟨k, hs, n.coeff, ?_⟩
  simpa [F, regularParameterMap, regularCuspBundlePoint,
    AnalyticTorusFamily.parameterMap] using hsnd

private theorem additiveCuspRepresentatives_psiOrbit
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : additiveCuspRadiusCover W.localWitness.radius)
    (h : additiveCuspCoverToGlobal W a = additiveCuspCoverToGlobal W b) :
    puncturedPsiOrbitRel W
      (additiveToPuncturedLocalHomeomorph M W.localWitness.radius (Quotient.mk _ b))
      (additiveToPuncturedLocalHomeomorph M W.localWitness.radius (Quotient.mk _ a)) := by
  obtain ⟨k, hs, n, hn⟩ := additiveCuspRepresentatives_period_data W a b h
  let lambda := firstParameterCoefficients n
  let m := identityParameterCoefficients n
  let x := periodValues
    (assembledFuchsianPeriodFunctions E D).tau
    (assembledFuchsianPeriodFunctions E D).mu
    (assembledFuchsianPeriodFunctions E D).beta (N.lift a.1.2)
  have hv : periodVector x n =
      (periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) + fun i ↦ (m i : ℂ) := by
    rw [integerPeriods_decompose n, periodVector_add,
      periodVector_firstPeriodCoefficients, periodVector_identityPeriodCoefficients]
  have hz0 : (periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) 0 + a.1.1 0 =
      b.1.1 0 + (-(m 0) : ℤ) := by
    have hi := congrFun hn 0
    rw [hv] at hi
    change (periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) 0 +
      (m 0 : ℂ) + a.1.1 0 = b.1.1 0 at hi
    push_cast
    linear_combination hi
  have hz1 : (periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) 1 + a.1.1 1 =
      b.1.1 1 + (-(m 1) : ℤ) := by
    have hi := congrFun hn 1
    rw [hv] at hi
    change (periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) 1 +
      (m 1 : ℂ) + a.1.1 1 = b.1.1 1 at hi
    push_cast
    linear_combination hi
  have hs' : a.1.2 = b.1.2 + (-k : ℤ) := by
    rw [hs]
    push_cast
    ring
  have hdense : denseCuspExponential
        ((periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) + a.1.1) a.1.2 =
      denseCuspExponential b.1.1 b.1.2 := by
    ext i
    fin_cases i
    · exact congrArg Units.val
        ((scaledExponentialUnit_eq_iff _ _).mpr ⟨-(m 0), hz0⟩)
    · exact congrArg Units.val
        ((scaledExponentialUnit_eq_iff _ _).mpr ⟨-(m 1), hz1⟩)
    · exact congrArg Units.val
        ((scaledExponentialUnit_eq_iff _ _).mpr ⟨-k, hs'⟩)
  let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
  have hlocal :
      (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
          N M W.localWitness.radius W.localWitness.radius_pos
            W.localWitness.radius_le).psiMap lambda (e (Quotient.mk _ a)).1 =
        (e (Quotient.mk _ b)).1 := by
    rw [show ((e (Quotient.mk _ a)).1 : LocalCarrier M W.localWitness.radius) =
        localCuspExponentialPoint M W.localWitness.radius a.1.1 a.1.2
          (mem_ball_zero_iff.mpr a.2) from
      additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius a,
      show ((e (Quotient.mk _ b)).1 : LocalCarrier M W.localWitness.radius) =
        localCuspExponentialPoint M W.localWitness.radius b.1.1 b.1.2
          (mem_ball_zero_iff.mpr b.2) from
      additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius b]
    rw [localCuspExponentialPoint_period_equivariant N M
      W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
      a.1.2 (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a)
      (mem_ball_zero_iff.mpr a.2) a.1.1 lambda]
    apply Subtype.ext
    rw [localCuspExponentialPoint_coe, localCuspExponentialPoint_coe]
    exact congrArg M.torusEmbedding hdense
  let _ := puncturedPsiAction W
  change MulAction.orbitRel (Multiplicative ParameterLattice) _ _ _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨Multiplicative.ofAdd lambda, ?_⟩
  apply Subtype.ext
  exact hlocal

public theorem puncturedLocalCuspQuotientMap_injective
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Function.Injective (puncturedLocalCuspQuotientMap W) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ p =>
    induction y using Quotient.inductionOn with
    | _ q =>
      let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      obtain ⟨u, rfl⟩ := e.surjective p
      obtain ⟨v, rfl⟩ := e.surjective q
      induction u using Quotient.inductionOn with
      | _ a =>
        induction v using Quotient.inductionOn with
        | _ b =>
          apply Quotient.sound
          apply additiveCuspRepresentatives_psiOrbit W b a
          rw [puncturedLocalCuspQuotientMap_mk,
            puncturedLocalCuspQuotientMap_mk] at hxy
          dsimp only [puncturedLocalCuspPrequotientMap, Function.comp_apply, e] at hxy
          rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply,
            additiveCuspQuotientToGlobal_mk, additiveCuspQuotientToGlobal_mk] at hxy
          exact hxy.symm

public theorem puncturedLocalCuspQuotientMap_isOpenEmbedding
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenEmbedding (puncturedLocalCuspQuotientMap W) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (puncturedLocalCuspQuotientMap_continuous W)
    (puncturedLocalCuspQuotientMap_injective W)
    (puncturedLocalCuspQuotientMap_isOpenMap W)

public theorem puncturedLocalCuspPrequotientMap_range
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Set.range (puncturedLocalCuspPrequotientMap W) =
      puncturedGlobalCuspCollar W := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
    let q := e.symm p
    have hp : p = e q := (e.apply_symm_apply p).symm
    rw [hp]
    induction q using Quotient.inductionOn with
    | _ a =>
      dsimp only [puncturedLocalCuspPrequotientMap, Function.comp_apply, e]
      rw [Homeomorph.symm_apply_apply, additiveCuspQuotientToGlobal_mk]
      exact actualPuncturedGlobalCuspPoint_mem_collar W a.1.2
        (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a) a.2 a.1.1
  · rintro ⟨x, hx, rfl⟩
    induction x using Quotient.inductionOn with
    | _ p =>
      rcases p with ⟨⟨b, hb⟩, zeta⟩
      change b ∈ normalizedCuspRegion N W.localWitness.radius at hx
      obtain ⟨s, ⟨hs, hq⟩, hlift⟩ := hx
      let a : additiveCuspRadiusCover W.localWitness.radius := ⟨(zeta, s), hq⟩
      let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      refine ⟨e (Quotient.mk _ a), ?_⟩
      dsimp only [puncturedLocalCuspPrequotientMap, Function.comp_apply, e]
      rw [Homeomorph.symm_apply_apply, additiveCuspQuotientToGlobal_mk]
      change puncturedGlobalCuspPoint N s _ zeta =
        Quotient.mk _ (Quotient.mk _ ((⟨b, hb⟩ : RegularBase) , zeta))
      subst b
      rfl

public theorem puncturedLocalCuspQuotientMap_range
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Set.range (puncturedLocalCuspQuotientMap W) =
      puncturedGlobalCuspCollar W := by
  rw [← puncturedLocalCuspPrequotientMap_range W]
  apply Set.Subset.antisymm
  · rintro y ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | _ p => exact ⟨p, rfl⟩
  · rintro y ⟨p, rfl⟩
    exact ⟨Quotient.mk _ p, rfl⟩

public theorem puncturedLocalCarrier_nonempty
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Nonempty {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} := by
  let a : ℂ := ((W.localWitness.radius / 2 : ℝ) : ℂ)
  have ha : a ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (div_ne_zero (ne_of_gt W.localWitness.radius_pos) (by norm_num))
  let x : DenseTorus := fun i ↦ if i = 2 then Units.mk0 a ha else 1
  have hx2 : ((x 2 : ℂˣ) : ℂ) = a := by simp [x]
  have ht : M.t (M.torusEmbedding x) = a := (M.t_torus x).trans hx2
  have hnorm : ‖M.t (M.torusEmbedding x)‖ < W.localWitness.radius := by
    rw [ht]
    change ‖((W.localWitness.radius / 2 : ℝ) : ℂ)‖ < W.localWitness.radius
    have hhalfpos : 0 < W.localWitness.radius / 2 :=
      div_pos W.localWitness.radius_pos (by norm_num)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhalfpos]
    linarith [W.localWitness.radius_pos]
  let p : LocalCarrier M W.localWitness.radius :=
    ⟨M.torusEmbedding x, mem_ball_zero_iff.mpr hnorm⟩
  exact ⟨⟨p, by simpa [p, ht] using ha⟩⟩

/-- The topological cusp collar identification, as an ambient open partial homeomorphism from
the punctured global family to the local toric filling. -/
public noncomputable def actualPuncturedCuspCollarOpenPartialHomeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    OpenPartialHomeomorph
      (PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D))
      (actualLocalCuspFilling W) := by
  let _ : Nonempty {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
    puncturedLocalCarrier_nonempty W
  let _ : Nonempty (puncturedLocalCuspQuotient W) :=
    ⟨Quotient.mk _ (puncturedLocalCarrier_nonempty W).some⟩
  exact
    (puncturedLocalCuspQuotientMap_isOpenEmbedding W).toOpenPartialHomeomorph.symm.trans
      (puncturedLocalCuspToFilling_isOpenEmbedding W).toOpenPartialHomeomorph

public theorem actualPuncturedCuspCollarOpenPartialHomeomorph_source
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    (actualPuncturedCuspCollarOpenPartialHomeomorph W).source =
      puncturedGlobalCuspCollar W := by
  let _ : Nonempty {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
    puncturedLocalCarrier_nonempty W
  let _ : Nonempty (puncturedLocalCuspQuotient W) :=
    ⟨Quotient.mk _ (puncturedLocalCarrier_nonempty W).some⟩
  simp only [actualPuncturedCuspCollarOpenPartialHomeomorph,
    OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target,
    Set.preimage_univ, Set.inter_univ,
    puncturedLocalCuspQuotientMap_range]

public theorem actualPuncturedCuspCollarOpenPartialHomeomorph_target
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    (actualPuncturedCuspCollarOpenPartialHomeomorph W).target =
      actualLocalCuspFillingCollar W := by
  let _ : Nonempty {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
    puncturedLocalCarrier_nonempty W
  let _ : Nonempty (puncturedLocalCuspQuotient W) :=
    ⟨Quotient.mk _ (puncturedLocalCarrier_nonempty W).some⟩
  simp only [actualPuncturedCuspCollarOpenPartialHomeomorph,
    OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.symm_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_source,
    Set.preimage_univ, Set.inter_univ, actualLocalCuspFillingCollar]

public theorem actualPuncturedCuspCollarOpenPartialHomeomorph_apply
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (q : puncturedLocalCuspQuotient W) :
    actualPuncturedCuspCollarOpenPartialHomeomorph W
        (puncturedLocalCuspQuotientMap W q) =
      puncturedLocalCuspToFilling W q := by
  let _ : Nonempty {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
    puncturedLocalCarrier_nonempty W
  let _ : Nonempty (puncturedLocalCuspQuotient W) :=
    ⟨Quotient.mk _ (puncturedLocalCarrier_nonempty W).some⟩
  rw [actualPuncturedCuspCollarOpenPartialHomeomorph,
    OpenPartialHomeomorph.trans_apply,
    (puncturedLocalCuspQuotientMap_isOpenEmbedding W).toOpenPartialHomeomorph_left_inv]
  exact congrFun
    ((puncturedLocalCuspToFilling_isOpenEmbedding W).toOpenPartialHomeomorph_apply) q

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
