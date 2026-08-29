module

public import SphereSixComplex.Topology.IntegralHomologyEuler
public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasisProof

/-!
# A homological model of the standard four-torus

The standard `n`-torus is an iterated mapping torus of the identity.  The Wang splitting therefore
computes all of its integral homology groups, without requiring a product construction in
Mathlib's CW-complex API.  Specializing to `n = 4` supplies the finiteness, dimension bound, and
Euler characteristic used by the Section 7 consumers.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex

namespace StandardTorusHomology

/-- Reindex finite free coordinates along an equality of their ranks. -/
public def finArrowCastAddEquiv {a b : ℕ} (h : a = b) :
    (Fin a → ℤ) ≃+ (Fin b → ℤ) := by
  subst h
  exact AddEquiv.refl _

/-- Integral homology of the standard `n`-torus in every degree.  The recursive step is the Wang
splitting for the identity mapping torus, and Pascal's identity gives the binomial rank. -/
public noncomputable def stdTorusHomology : (n k : ℕ) →
    IntegralSingularHomology k (StdTorus n) ≃+ (Fin (n.choose k) → ℤ)
  | 0, 0 =>
      (stdTorusHomologyZero 0).trans (finArrowCastAddEquiv rfl)
  | 0, k + 1 => by
      haveI := subsingleton_homology_stdTorusZero (k + 1) (Nat.succ_ne_zero k)
      have hchoose : 0 = Nat.choose 0 (k + 1) := by simp
      exact (addEquivOfSubsingleton :
        IntegralSingularHomology (k + 1) (StdTorus 0) ≃+ (Fin 0 → ℤ)).trans
          (finArrowCastAddEquiv hchoose)
  | n + 1, 0 =>
      (stdTorusHomologyZero (n + 1)).trans (finArrowCastAddEquiv rfl)
  | n + 1, k + 1 => by
      let e :=
        (integralSingularHomologyEquiv (k + 1)
          (stdTorusMappingTorusHomeomorph n)).symm.trans
            (reflMappingTorusHomologySplit k (n.choose (k + 1)) (n.choose k)
              (stdTorusHomology n (k + 1)) (stdTorusHomology n k))
      have h : n.choose (k + 1) + n.choose k = (n + 1).choose (k + 1) := by
        rw [Nat.choose_succ_succ']
        omega
      exact e.trans (finArrowCastAddEquiv h)

/-- Every integral homology group of a standard torus is finitely generated. -/
public theorem finite_homology_stdTorus (n k : ℕ) :
    Module.Finite ℤ (IntegralSingularHomology k (StdTorus n)) := by
  let _ : Module.Finite ℤ (Fin (n.choose k) → ℤ) := inferInstance
  exact Module.Finite.equiv (stdTorusHomology n k).symm.toIntLinearEquiv

/-- The standard `n`-torus has no homology above degree `n`. -/
public theorem subsingleton_homology_stdTorus_of_lt (n k : ℕ) (h : n < k) :
    Subsingleton (IntegralSingularHomology k (StdTorus n)) := by
  let e := stdTorusHomology n k
  constructor
  intro x y
  apply e.injective
  funext i
  have hz : n.choose k = 0 := Nat.choose_eq_zero_of_lt h
  exact Fin.elim0 (hz ▸ i)

/-- Homological finiteness through degree six for the standard four-torus. -/
public theorem stdTorusFour_integralHomologyFiniteSix :
    IntegralHomologyFiniteSix (StdTorus 4) where
  finiteHomology := finite_homology_stdTorus 4
  homologyAboveDimension k hk :=
    subsingleton_homology_stdTorus_of_lt 4 k (by omega)

/-- The fifth integral homology of the standard four-torus vanishes. -/
public theorem subsingleton_homology_five_stdTorusFour :
    Subsingleton (IntegralSingularHomology 5 (StdTorus 4)) :=
  subsingleton_homology_stdTorus_of_lt 4 5 (by omega)

/-- The sixth integral homology of the standard four-torus vanishes. -/
public theorem subsingleton_homology_six_stdTorusFour :
    Subsingleton (IntegralSingularHomology 6 (StdTorus 4)) :=
  subsingleton_homology_stdTorus_of_lt 4 6 (by omega)

/-- The alternating integral homology rank sum of the standard four-torus is zero. -/
public theorem stdTorusFour_euler_eq_zero :
    integralHomologyEulerCharacteristicSix (StdTorus 4) = 0 := by
  unfold integralHomologyEulerCharacteristicSix
  rw [(stdTorusHomology 4 0).toIntLinearEquiv.finrank_eq,
    (stdTorusHomology 4 1).toIntLinearEquiv.finrank_eq,
    (stdTorusHomology 4 2).toIntLinearEquiv.finrank_eq,
    (stdTorusHomology 4 3).toIntLinearEquiv.finrank_eq,
    (stdTorusHomology 4 4).toIntLinearEquiv.finrank_eq,
    (stdTorusHomology 4 5).toIntLinearEquiv.finrank_eq,
    (stdTorusHomology 4 6).toIntLinearEquiv.finrank_eq]
  norm_num [Nat.choose]

end StandardTorusHomology

/-- The homological replacement for a four-torus cell model.  A single all-degree binomial-rank
calculation implies all finiteness, vanishing, and Euler-characteristic consequences needed by
the current consumers. -/
public structure FourTorusHomologicalModel (X : Type) [TopologicalSpace X] where
  homologyEquiv : ∀ k : ℕ,
    IntegralSingularHomology k X ≃+ (Fin (Nat.choose 4 k) → ℤ)

namespace FourTorusHomologicalModel

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Transport the homological model across a homeomorphism. -/
public noncomputable def homeomorph (M : FourTorusHomologicalModel X) (e : Y ≃ₜ X) :
    FourTorusHomologicalModel Y where
  homologyEquiv k := (integralSingularHomologyEquiv k e).trans (M.homologyEquiv k)

/-- Every homology group in a four-torus homological model is finitely generated. -/
public theorem finiteHomology (M : FourTorusHomologicalModel X) (k : ℕ) :
    Module.Finite ℤ (IntegralSingularHomology k X) := by
  let _ : Module.Finite ℤ (Fin (Nat.choose 4 k) → ℤ) := inferInstance
  exact Module.Finite.equiv (M.homologyEquiv k).symm.toIntLinearEquiv

/-- Homology vanishes above degree four. -/
public theorem subsingleton_homology_of_four_lt (M : FourTorusHomologicalModel X)
    (k : ℕ) (hk : 4 < k) : Subsingleton (IntegralSingularHomology k X) := by
  let e := M.homologyEquiv k
  constructor
  intro x y
  apply e.injective
  funext i
  have hz : Nat.choose 4 k = 0 := Nat.choose_eq_zero_of_lt hk
  exact Fin.elim0 (hz ▸ i)

/-- The package expected by consumers that only need finite homology through dimension six. -/
public theorem integralHomologyFiniteSix (M : FourTorusHomologicalModel X) :
    IntegralHomologyFiniteSix X where
  finiteHomology := M.finiteHomology
  homologyAboveDimension k hk := M.subsingleton_homology_of_four_lt k (by omega)

public theorem subsingleton_homology_five (M : FourTorusHomologicalModel X) :
    Subsingleton (IntegralSingularHomology 5 X) :=
  M.subsingleton_homology_of_four_lt 5 (by omega)

public theorem subsingleton_homology_six (M : FourTorusHomologicalModel X) :
    Subsingleton (IntegralSingularHomology 6 X) :=
  M.subsingleton_homology_of_four_lt 6 (by omega)

/-- The homological model directly computes the truncated Euler characteristic. -/
public theorem euler_eq_zero (M : FourTorusHomologicalModel X) :
    integralHomologyEulerCharacteristicSix X = 0 := by
  unfold integralHomologyEulerCharacteristicSix
  rw [(M.homologyEquiv 0).toIntLinearEquiv.finrank_eq,
    (M.homologyEquiv 1).toIntLinearEquiv.finrank_eq,
    (M.homologyEquiv 2).toIntLinearEquiv.finrank_eq,
    (M.homologyEquiv 3).toIntLinearEquiv.finrank_eq,
    (M.homologyEquiv 4).toIntLinearEquiv.finrank_eq,
    (M.homologyEquiv 5).toIntLinearEquiv.finrank_eq,
    (M.homologyEquiv 6).toIntLinearEquiv.finrank_eq]
  norm_num [Nat.choose]

end FourTorusHomologicalModel

namespace EstablishedFiniteCWTopology

open Geometry Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open SphereSixComplex.Periods

/-- A full-rank complex two-torus has the four-torus homological model, proved from its explicit
homeomorphism with the iterated identity mapping torus. -/
public noncomputable def additiveTorusFourTorusHomologicalModel
    (p : Parameters) (h : FullRank p) : FourTorusHomologicalModel (AdditiveTorus p) where
  homologyEquiv k :=
    (integralSingularHomologyEquiv k
      (StandardTorusHomology.additiveTorusStdHomeomorph p h)).trans
        (StandardTorusHomology.stdTorusHomology 4 k)

public theorem additiveTorus_integralHomologyFiniteSix (p : Parameters) (h : FullRank p) :
    IntegralHomologyFiniteSix (AdditiveTorus p) :=
  (additiveTorusFourTorusHomologicalModel p h).integralHomologyFiniteSix

public theorem additiveTorus_subsingleton_homology_five (p : Parameters) (h : FullRank p) :
    Subsingleton (IntegralSingularHomology 5 (AdditiveTorus p)) :=
  (additiveTorusFourTorusHomologicalModel p h).subsingleton_homology_five

public theorem additiveTorus_subsingleton_homology_six (p : Parameters) (h : FullRank p) :
    Subsingleton (IntegralSingularHomology 6 (AdditiveTorus p)) :=
  (additiveTorusFourTorusHomologicalModel p h).subsingleton_homology_six

public theorem additiveTorus_euler_eq_zero (p : Parameters) (h : FullRank p) :
    integralHomologyEulerCharacteristicSix (AdditiveTorus p) = 0 :=
  (additiveTorusFourTorusHomologicalModel p h).euler_eq_zero

end EstablishedFiniteCWTopology

end SphereSixComplex

end

end
