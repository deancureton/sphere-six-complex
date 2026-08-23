module

public import SphereSixComplex.LatticeData
import all SphereSixComplex.LatticeData

/-!
# Period-matrix algebra

The matrix in Definition 3.3 and the algebraic consequences of the generator transformation
laws from Definition 3.1.
-/

open Matrix

namespace SphereSixComplex.Periods

open LatticeData

public structure Parameters where
  tau : ℂ
  mu : ℂ
  beta : ℂ

public def periodBlock (x : Parameters) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![6 * x.mu, x.tau; x.beta, x.mu]

public def periodMatrix (x : Parameters) : Matrix (Fin 2) (Fin 4) ℂ :=
  !![6 * x.mu, x.tau, 1, 0; x.beta, x.mu, 0, 1]

public noncomputable def transformOne (x : Parameters) : Parameters where
  tau := (x.tau - 1) / x.tau
  mu := (1 - x.mu) / x.tau
  beta := x.beta + 2 - 6 * (1 - x.mu) ^ 2 / x.tau

public noncomputable def transformTwo (x : Parameters) : Parameters where
  tau := -1 / x.tau
  mu := 1 + x.mu / x.tau
  beta := x.beta - 3 - 6 * x.mu ^ 2 / x.tau

public def transformCusp (x : Parameters) : Parameters where
  tau := x.tau - 1
  mu := x.mu
  beta := x.beta + 1

public noncomputable def rightOne (x : Parameters) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-1 / x.tau, 0; (1 - x.mu) / x.tau, 1]

public noncomputable def rightTwo (x : Parameters) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / x.tau, 0; -x.mu / x.tau, 1]

public def A₁Complex : Matrix (Fin 4) (Fin 4) ℂ := A₁.map (Int.castRingHom ℂ)

public def A₂Complex : Matrix (Fin 4) (Fin 4) ℂ := A₂.map (Int.castRingHom ℂ)

public def M₀Complex : Matrix (Fin 4) (Fin 4) ℂ := M₀.map (Int.castRingHom ℂ)

public theorem A₁_eq_explicit : A₁ =
    !![(1 : ℤ), 0, 0, 0; 6, 0, 1, 0; -6, -1, -1, 0; -2, 1, 0, 1] := by
  exact SphereSixComplex.LatticeData.A₁.eq_def

public theorem A₂_eq_explicit : A₂ =
    !![(1 : ℤ), 0, 0, 0; 0, 0, -1, 0; -6, 1, 0, 0; 3, 0, 1, 1] := by
  exact SphereSixComplex.LatticeData.A₂.eq_def

public theorem M₀_eq_explicit : M₀ =
    !![(1 : ℤ), 0, 0, 0; 0, 1, 0, 0; 0, 1, 1, 0; -1, 0, 0, 1] := by
  exact SphereSixComplex.LatticeData.M₀.eq_def

public theorem A₁Complex_eq : A₁Complex =
    !![(1 : ℂ), 0, 0, 0; 6, 0, 1, 0; -6, -1, -1, 0; -2, 1, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A₁Complex, A₁_eq_explicit]

public theorem A₂Complex_eq : A₂Complex =
    !![(1 : ℂ), 0, 0, 0; 0, 0, -1, 0; -6, 1, 0, 0; 3, 0, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A₂Complex, A₂_eq_explicit]

public theorem M₀Complex_eq : M₀Complex =
    !![(1 : ℂ), 0, 0, 0; 0, 1, 0, 0; 0, 1, 1, 0; -1, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [M₀Complex, M₀_eq_explicit]

public theorem generatorOne_equivariance (x : Parameters) (htau : x.tau ≠ 0) :
    periodMatrix (transformOne x) * A₁Complex = rightOne x * periodMatrix x := by
  rw [A₁Complex_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [periodMatrix, transformOne, rightOne, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring

public theorem generatorTwo_equivariance (x : Parameters) (htau : x.tau ≠ 0) :
    periodMatrix (transformTwo x) * A₂Complex = rightTwo x * periodMatrix x := by
  rw [A₂Complex_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [periodMatrix, transformTwo, rightTwo, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring

public theorem cusp_equivariance (x : Parameters) :
    periodMatrix (transformCusp x) * M₀Complex = periodMatrix x := by
  rw [M₀Complex_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [periodMatrix, transformCusp, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem rightOne_det (x : Parameters) : (rightOne x).det = -1 / x.tau := by
  rw [Matrix.det_fin_two]
  simp [rightOne]

public theorem rightTwo_det (x : Parameters) : (rightTwo x).det = 1 / x.tau := by
  rw [Matrix.det_fin_two]
  simp [rightTwo]

public theorem rightOne_isUnit_det (x : Parameters) (htau : x.tau ≠ 0) :
    IsUnit (rightOne x).det := by
  rw [rightOne_det]
  exact isUnit_iff_ne_zero.mpr (div_ne_zero (by norm_num) htau)

public theorem rightTwo_isUnit_det (x : Parameters) (htau : x.tau ≠ 0) :
    IsUnit (rightTwo x).det := by
  rw [rightTwo_det]
  exact isUnit_iff_ne_zero.mpr (div_ne_zero (by norm_num) htau)

end SphereSixComplex.Periods
