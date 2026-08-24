module

public import SphereSixComplex.Geometry.CuspToricPhaseAction
public import SphereSixComplex.Periods.FuchsianPeriodAssembly
import all SphereSixComplex.LatticeData
import all SphereSixComplex.Periods.Functions
import all SphereSixComplex.Periods.Matrix

/-!
# The normalized cusp expansion of the Fuchsian period block

This file isolates the normalization absent from the current Fuchsian modular-parameter API and
derives the local expansion `Z(s) = s B₀ + C(q)` from the exact cusp transformation laws.  The
only established analytic input is the general one-variable theorem that a bounded periodic
holomorphic function on a half-plane descends to, and extends across the origin of, the
exponential quotient disc.

The paper uses `s = τ - h(t_c)` and `exp (2 π i s) = t_c`.  The structure
`NormalizedFuchsianCuspCoordinate` records precisely the still-missing choice of this coordinate.
In this module its normalization is `s = τ`; consequently the correction matrix has upper-right
entry zero.  Recovering the paper's nonzero `h(t_c)` entry requires adding that coordinate change
to the Fuchsian uniformization, rather than changing the descent argument below.
-/

@[expose] public section

noncomputable section

open Matrix UpperHalfPlane
open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.CuspPeriodExpansion

open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup

/-- The half-plane above height `H`. -/
public def cuspHalfPlane (H : ℝ) : Set ℂ :=
  {s | H < s.im}

/-- The exponential cusp coordinate. -/
public def cuspQ (s : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * s)

/-- The radius of the exponential image of the half-plane above `H`. -/
public def cuspRadius (H : ℝ) : ℝ :=
  Real.exp (-2 * Real.pi * H)

public theorem cuspRadius_pos (H : ℝ) : 0 < cuspRadius H := by
  exact Real.exp_pos _

/-- Norm-boundedness for a complex-valued function on a subset of the complex plane. -/
public def NormBoundedOn (f : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ s ∈ S, ‖f s‖ ≤ A

/-- The exact result of descending a bounded periodic holomorphic function through `cuspQ`. -/
public structure HolomorphicCuspDescent (H : ℝ) (f : ℂ → ℂ) where
  extension : ℂ → ℂ
  extension_holomorphic :
    DifferentiableOn ℂ extension (Metric.ball 0 (cuspRadius H))
  factorization : ∀ s ∈ cuspHalfPlane H, extension (cuspQ s) = f s
  unique : ∀ g : ℂ → ℂ,
    DifferentiableOn ℂ g (Metric.ball 0 (cuspRadius H)) →
    (∀ s ∈ cuspHalfPlane H, g (cuspQ s) = f s) →
    Set.EqOn g extension (Metric.ball 0 (cuspRadius H))

namespace Established

/-- The classical removable-singularity theorem for the exponential quotient of a half-plane.
This is a general one-variable analytic theorem, independent of the period family and of the
paper's toric construction. -/
public axiom periodicBoundedHolomorphicCuspDescent
    (H : ℝ) (f : ℂ → ℂ)
    (holomorphic : DifferentiableOn ℂ f (cuspHalfPlane H))
    (periodic : ∀ s ∈ cuspHalfPlane H, f (s - 1) = f s)
    (bounded : NormBoundedOn f (cuspHalfPlane H)) :
    Nonempty (HolomorphicCuspDescent H f)

end Established

/-- The missing P1-type normalization for the actual assembled Fuchsian period functions.
The lift is a holomorphic inverse to `τ` on a half-plane, lands in the source cusp, and intertwines
translation by `-1` with the exact Fuchsian cusp generator. -/
public structure NormalizedFuchsianCuspCoordinate
    (E : EstablishedFuchsianModularParameter) (D : FuchsianPeriodLocalData E) where
  height : ℝ
  lift : ℂ → UpperHalfPlane
  lift_holomorphic : MDiff[cuspHalfPlane height] lift
  lift_tau : ∀ s ∈ cuspHalfPlane height,
    (((assembledFuchsianPeriodFunctions E D).tau (lift s) : UpperHalfPlane) : ℂ) = s
  lift_mem_cusp : ∀ s ∈ cuspHalfPlane height, lift s ∈ fuchsianCuspRegion
  lift_shift : ∀ s ∈ cuspHalfPlane height,
    lift (s - 1) =
      E.modularParameter.toTriangleUniformization.sourceAction g₀ • lift s

namespace NormalizedFuchsianCuspCoordinate

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D)

/-- The invariant `μ` coefficient pulled back to the normalized cusp half-plane. -/
public def muAlong (s : ℂ) : ℂ :=
  (assembledFuchsianPeriodFunctions E D).mu (N.lift s)

/-- The invariant bounded combination `b = β + τ` on the normalized cusp half-plane. -/
public def bAlong (s : ℂ) : ℂ :=
  (assembledFuchsianPeriodFunctions E D).beta (N.lift s) +
    (assembledFuchsianPeriodFunctions E D).tau (N.lift s)

public theorem muAlong_holomorphic :
    DifferentiableOn ℂ N.muAlong (cuspHalfPlane N.height) := by
  rw [← mdifferentiableOn_iff_differentiableOn]
  change MDiff[cuspHalfPlane N.height]
    ((assembledFuchsianPeriodFunctions E D).mu ∘ N.lift)
  exact
    (assembledFuchsianPeriodFunctions E D).mu_holomorphic.comp_mdifferentiableOn
      N.lift_holomorphic

public theorem bAlong_holomorphic :
    DifferentiableOn ℂ N.bAlong (cuspHalfPlane N.height) := by
  rw [← mdifferentiableOn_iff_differentiableOn]
  have htau : MDiff (fun z : UpperHalfPlane ↦
      (((assembledFuchsianPeriodFunctions E D).tau z : UpperHalfPlane) : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.comp
      (assembledFuchsianPeriodFunctions E D).tau_holomorphic
  change MDiff[cuspHalfPlane N.height]
    (((assembledFuchsianPeriodFunctions E D).beta + fun z : UpperHalfPlane ↦
      (((assembledFuchsianPeriodFunctions E D).tau z : UpperHalfPlane) : ℂ)) ∘ N.lift)
  exact
    ((assembledFuchsianPeriodFunctions E D).beta_holomorphic.add htau).comp_mdifferentiableOn
      N.lift_holomorphic

public theorem muAlong_periodic (s : ℂ) (hs : s ∈ cuspHalfPlane N.height) :
    N.muAlong (s - 1) = N.muAlong s := by
  rw [muAlong, muAlong, N.lift_shift s hs]
  exact (assembledFuchsianPeriodFunctions E D).mu_transform_cusp (N.lift s)

public theorem bAlong_periodic (s : ℂ) (hs : s ∈ cuspHalfPlane N.height) :
    N.bAlong (s - 1) = N.bAlong s := by
  rw [bAlong, bAlong, N.lift_shift s hs]
  rw [(assembledFuchsianPeriodFunctions E D).beta_transform_cusp,
    (assembledFuchsianPeriodFunctions E D).tau_transform_cusp]
  ring

public theorem muAlong_bounded :
    NormBoundedOn N.muAlong (cuspHalfPlane N.height) := by
  obtain ⟨A, hA, hbound⟩ :=
    (assembledFuchsianPeriodFunctions E D).mu_cusp_bounded
  exact ⟨A, hA, fun s hs ↦ hbound (N.lift s) (N.lift_mem_cusp s hs)⟩

public theorem bAlong_bounded :
    NormBoundedOn N.bAlong (cuspHalfPlane N.height) := by
  obtain ⟨A, hA, hbound⟩ :=
    (assembledFuchsianPeriodFunctions E D).beta_add_tau_cusp_bounded
  exact ⟨A, hA, fun s hs ↦ hbound (N.lift s) (N.lift_mem_cusp s hs)⟩

/-- The selected holomorphic extension of `μ` across the cusp point `q = 0`. -/
public noncomputable def muDescent : HolomorphicCuspDescent N.height N.muAlong :=
  Classical.choice (Established.periodicBoundedHolomorphicCuspDescent N.height N.muAlong
    N.muAlong_holomorphic N.muAlong_periodic N.muAlong_bounded)

/-- The selected holomorphic extension of `β + τ` across the cusp point `q = 0`. -/
public noncomputable def bDescent : HolomorphicCuspDescent N.height N.bAlong :=
  Classical.choice (Established.periodicBoundedHolomorphicCuspDescent N.height N.bAlong
    N.bAlong_holomorphic N.bAlong_periodic N.bAlong_bounded)

/-- The correction matrix in the normalization `s = τ`. -/
public noncomputable def correctionMatrix (q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![6 * N.muDescent.extension q, 0;
    N.bDescent.extension q, N.muDescent.extension q]

@[simp]
public theorem correctionMatrix_zero_zero (q : ℂ) :
    N.correctionMatrix q 0 0 = 6 * N.muDescent.extension q :=
  rfl

@[simp]
public theorem correctionMatrix_zero_one (q : ℂ) : N.correctionMatrix q 0 1 = 0 :=
  rfl

@[simp]
public theorem correctionMatrix_one_zero (q : ℂ) :
    N.correctionMatrix q 1 0 = N.bDescent.extension q :=
  rfl

@[simp]
public theorem correctionMatrix_one_one (q : ℂ) :
    N.correctionMatrix q 1 1 = N.muDescent.extension q :=
  rfl

/-- Every entry of the correction matrix is holomorphic on the cusp disc. -/
public theorem correctionMatrix_entry_holomorphic (i j : Fin 2) :
    DifferentiableOn ℂ (fun q ↦ N.correctionMatrix q i j)
      (Metric.ball 0 (cuspRadius N.height)) := by
  fin_cases i <;> fin_cases j
  · exact N.muDescent.extension_holomorphic.const_mul 6
  · exact differentiableOn_const 0
  · exact N.bDescent.extension_holomorphic
  · exact N.muDescent.extension_holomorphic

/-- Holomorphicity implies boundedness of each correction-matrix entry on every strictly smaller
closed subdisc. -/
public theorem correctionMatrix_entry_bounded_on_closedBall
    (i j : Fin 2) {r : ℝ} (hr : r < cuspRadius N.height) :
    Bornology.IsBounded
      ((fun q ↦ N.correctionMatrix q i j) '' Metric.closedBall (0 : ℂ) r) := by
  have hsubset : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball 0 (cuspRadius N.height) := by
    intro q hq
    exact lt_of_le_of_lt hq hr
  exact ((ProperSpace.isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
    ((N.correctionMatrix_entry_holomorphic i j).mono hsubset).continuousOn).isBounded

/-- The complex form of the integral cusp shear. -/
public def B₀Complex : Matrix (Fin 2) (Fin 2) ℂ :=
  B₀.map (Int.castRingHom ℂ)

public theorem B₀Complex_eq : B₀Complex = !![(0 : ℂ), 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [B₀Complex, B₀]

/-- The exact period-block expansion on the normalized cusp lift. -/
public theorem periodBlock_eq_smul_B₀_add_correction
    (s : ℂ) (hs : s ∈ cuspHalfPlane N.height) :
    periodBlock (periodValues
        (assembledFuchsianPeriodFunctions E D).tau
        (assembledFuchsianPeriodFunctions E D).mu
        (assembledFuchsianPeriodFunctions E D).beta (N.lift s)) =
      s • B₀Complex + N.correctionMatrix (cuspQ s) := by
  rw [B₀Complex_eq]
  have hmu := N.muDescent.factorization s hs
  have hb := N.bDescent.factorization s hs
  have htau := N.lift_tau s hs
  simp only [muAlong] at hmu
  simp only [bAlong] at hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [periodBlock, periodValues, correctionMatrix, hmu, hb, htau]

/-- The nonzero exponential regarded as a complex unit. -/
public def exponentialUnit (z : ℂ) : ℂˣ :=
  Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)

/-- The paper's local phase coefficient `c_λ(q) = exp (2 π i C(q) λ)`. -/
public noncomputable def phaseCoefficient
    (lambda : CuspFilling.ParameterLattice) (q : ℂ) : Phase :=
  fun i ↦ exponentialUnit
    (2 * Real.pi * Complex.I *
      (N.correctionMatrix q).mulVec (fun j ↦ (lambda j : ℂ)) i)

@[simp]
public theorem phaseCoefficient_zero (q : ℂ) : N.phaseCoefficient 0 q = 1 := by
  ext i
  fin_cases i <;> simp [phaseCoefficient, exponentialUnit, Matrix.mulVec]

@[simp]
public theorem phaseCoefficient_add
    (lambda mu : CuspFilling.ParameterLattice) (q : ℂ) :
    N.phaseCoefficient (lambda + mu) q =
      N.phaseCoefficient lambda q * N.phaseCoefficient mu q := by
  ext i
  change Complex.exp
      (2 * Real.pi * Complex.I *
        (N.correctionMatrix q).mulVec (fun j ↦ ((lambda + mu) j : ℂ)) i) =
    Complex.exp
        (2 * Real.pi * Complex.I *
          (N.correctionMatrix q).mulVec (fun j ↦ (lambda j : ℂ)) i) *
      Complex.exp
        (2 * Real.pi * Complex.I *
          (N.correctionMatrix q).mulVec (fun j ↦ (mu j : ℂ)) i)
  have hv : (fun j ↦ ((lambda + mu) j : ℂ)) =
      (fun j ↦ (lambda j : ℂ)) + fun j ↦ (mu j : ℂ) := by
    funext j
    simp
  rw [hv, Matrix.mulVec_add, Pi.add_apply, mul_add, Complex.exp_add]

/-- The phase coefficients are holomorphic on the open cusp disc. -/
public theorem phaseCoefficient_holomorphicOn
    (lambda : CuspFilling.ParameterLattice) (i : Fin 2) :
    MDiff[Metric.ball 0 (cuspRadius N.height)]
      (fun q ↦ (N.phaseCoefficient lambda q i : ℂ)) := by
  have hmul : DifferentiableOn ℂ
      (fun q ↦ (N.correctionMatrix q).mulVec (fun j ↦ (lambda j : ℂ)) i)
      (Metric.ball 0 (cuspRadius N.height)) := by
    change DifferentiableOn ℂ
      (fun q ↦ ∑ j, N.correctionMatrix q i j * (lambda j : ℂ))
      (Metric.ball 0 (cuspRadius N.height))
    simpa using (DifferentiableOn.fun_sum (u := Finset.univ) fun j _ ↦
      (N.correctionMatrix_entry_holomorphic i j).mul_const (lambda j : ℂ))
  have harg := hmul.const_mul (2 * Real.pi * Complex.I)
  have hargMD : MDiff[Metric.ball 0 (cuspRadius N.height)]
      (fun q ↦ 2 * Real.pi * Complex.I *
        (N.correctionMatrix q).mulVec (fun j ↦ (lambda j : ℂ)) i) :=
    mdifferentiableOn_iff_differentiableOn.mpr harg
  have hexpMD : MDiff (Complex.exp : ℂ → ℂ) :=
    mdifferentiable_iff_differentiable.mpr Complex.differentiable_exp
  change MDiff[Metric.ball 0 (cuspRadius N.height)]
    (Complex.exp ∘ fun q ↦ 2 * Real.pi * Complex.I *
      (N.correctionMatrix q).mulVec (fun j ↦ (lambda j : ℂ)) i)
  exact hexpMD.comp_mdifferentiableOn hargMD

/-- Coherent local phase data on the cusp disc. -/
public structure LocalHolomorphicPhaseCoefficients where
  phase : CuspFilling.ParameterLattice → ℂ → Phase
  phase_zero : ∀ q, phase 0 q = 1
  phase_add : ∀ lambda mu q, phase (lambda + mu) q = phase lambda q * phase mu q
  coefficient_holomorphicOn : ∀ lambda i,
    MDiff[Metric.ball 0 (cuspRadius N.height)]
      (fun q ↦ (phase lambda q i : ℂ))

/-- The correction matrix produces the exact local phase package. -/
public noncomputable def localHolomorphicPhaseCoefficients :
    N.LocalHolomorphicPhaseCoefficients where
  phase := N.phaseCoefficient
  phase_zero := N.phaseCoefficient_zero
  phase_add := N.phaseCoefficient_add
  coefficient_holomorphicOn := N.phaseCoefficient_holomorphicOn

/-- The bridge to the older global interface is valid only when the local coefficients happen to
extend holomorphically to all of `ℂ`, together with the corresponding holomorphic toric twist.
Neither global premise follows from bounded cusp descent. -/
public noncomputable def toExactHolomorphicPhaseCoefficients
    (M : StandardInfiniteA2ToricModel.Model)
    (global_holomorphic : ∀ lambda i,
      Differentiable ℂ (fun q ↦ (N.phaseCoefficient lambda q i : ℂ)))
    (twist_holomorphic : ∀ lambda,
      ContMDiff (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel) ∞
        (fun p : M.Carrier ↦ CuspToricPhaseAction.ToricModel.phaseAction M
          (N.phaseCoefficient lambda (M.t p)) p)) :
    ExactHolomorphicPhaseCoefficients M where
  phase := N.phaseCoefficient
  phase_zero := N.phaseCoefficient_zero
  phase_add := N.phaseCoefficient_add
  coefficient_holomorphic := global_holomorphic
  twist_holomorphic := twist_holomorphic

end NormalizedFuchsianCuspCoordinate

end SphereSixComplex.Geometry.CuspPeriodExpansion
