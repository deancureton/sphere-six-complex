module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainMaps
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexMaps
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexBoundary
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.ULift
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Augmentation
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology Module
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def integralSingularSimplexSubinterval {n : ℕ} (j k : ℕ) (hjk : j + k ≤ n)
    (σ : integralSingularSimplex n X) : integralSingularSimplex k X :=
  (TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.subinterval j k hjk).op σ

private theorem integralSingularSimplexSubinterval_natural {n : ℕ}
    (j k : ℕ) (hjk : j + k ≤ n) (f : ContinuousMap X Y)
    (σ : integralSingularSimplex n X) :
    integralSingularSimplexMap k f (integralSingularSimplexSubinterval j k hjk σ) =
      integralSingularSimplexSubinterval j k hjk (integralSingularSimplexMap n f σ) :=
  congrArg (fun h : integralSingularSimplex n X ⟶ integralSingularSimplex k Y => h σ)
    ((TopCat.toSSet.map (TopCat.ofHom f)).naturality
    (SimplexCategory.subinterval j k hjk).op)

def integralSingularCapProduct (k m : ℕ) :
    integralSingularCochain k X →ₗ[ℤ]
      (integralSingularChains X).X (k + m) →ₗ[ℤ] (integralSingularChains X).X m :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun φ => (integralSingularChainBasis (k + m) X).constr ℕ (fun σ =>
        (φ (integralSimplexChain k
          (integralSingularSimplexSubinterval 0 k (by omega) σ))).down •
            integralSimplexChain m (integralSingularSimplexSubinterval k m le_rfl σ))
      map_zero' := by
        apply (integralSingularChainBasis (k + m) X).ext
        intro σ
        simp only [Basis.constr_basis, LinearMap.zero_apply, ULift.zero_down, zero_zsmul]
      map_add' := fun φ ψ => by
        apply (integralSingularChainBasis (k + m) X).ext
        intro σ
        simp only [Basis.constr_basis, LinearMap.add_apply, ULift.add_down]
        exact add_zsmul _ _ _ }

private theorem integralSingularCapProduct_apply_simplex (k m : ℕ)
    (φ : integralSingularCochain k X) (σ : integralSingularSimplex (k + m) X) :
    integralSingularCapProduct k m φ (integralSimplexChain (k + m) σ) =
      (φ (integralSimplexChain k
        (integralSingularSimplexSubinterval 0 k (by omega) σ))).down •
        integralSimplexChain m (integralSingularSimplexSubinterval k m le_rfl σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis (k + m) X).constr_basis ℕ _ σ

theorem integralSingularCapProduct_simplex (k m : ℕ)
    (φ : integralSingularCochain k X) (σ : integralSingularSimplex (k + m) X) :
    integralSingularCapProduct k m φ (integralSimplexChain (k + m) σ) =
      (φ (integralSimplexChain k ((TopCat.toSSet.obj (TopCat.of X)).map
        (SimplexCategory.subinterval 0 k (by omega)).op σ))).down •
          integralSimplexChain m ((TopCat.toSSet.obj (TopCat.of X)).map
            (SimplexCategory.subinterval k m le_rfl).op σ) := by
  simpa only [integralSingularSimplexSubinterval] using
    integralSingularCapProduct_apply_simplex k m φ σ

theorem integralSingularCapProduct_natural (k m : ℕ) (f : ContinuousMap X Y)
    (φ : integralSingularCochain k Y) :
    ((integralSingularChainMap f).f m).hom.comp
        (integralSingularCapProduct k m (integralSingularCochainPullback k f φ)) =
      (integralSingularCapProduct k m φ).comp ((integralSingularChainMap f).f (k + m)).hom := by
  apply (integralSingularChainBasis (k + m) X).ext
  intro σ
  simp only [LinearMap.comp_apply, integralSingularChainBasis_apply,
    integralSingularCapProduct_apply_simplex, map_zsmul, integralSimplexChain_map]
  rw [← integralSingularSimplexSubinterval_natural]
  congr 1
  change (φ ((integralSingularChainMap f).f k
    (integralSimplexChain k (integralSingularSimplexSubinterval 0 k (by omega) σ)))).down = _
  rw [integralSimplexChain_map, integralSingularSimplexSubinterval_natural]

private theorem simplex_subinterval_front_face_le (k m : ℕ) (i : Fin (k + m + 2))
    (hi : i.val ≤ k) :
    SimplexCategory.subinterval 0 k (show 0 + k ≤ k + m by omega) ≫ SimplexCategory.δ i =
      SimplexCategory.δ (⟨i.val, by omega⟩ : Fin (k + 2)) ≫
        SimplexCategory.subinterval 0 (k + 1) (show 0 + (k + 1) ≤ k + m + 1 by omega) := by
  ext j
  have hj : j.val < k + 1 := j.isLt
  change (i.succAbove ⟨j.val, by omega⟩).val =
    ((⟨i.val, by omega⟩ : Fin (k + 2)).succAbove j).val
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, apply_ite Fin.val, Fin.val_succ]

private theorem simplex_subinterval_front_face_lt (k m : ℕ) (i : Fin (k + m + 2))
    (hi : k < i.val) :
    SimplexCategory.subinterval 0 k (show 0 + k ≤ k + m by omega) ≫ SimplexCategory.δ i =
      SimplexCategory.subinterval 0 k (show 0 + k ≤ k + m + 1 by omega) := by
  ext j
  have hj : j.val < k + 1 := j.isLt
  change (i.succAbove ⟨j.val, by omega⟩).val = j.val
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

private theorem simplex_subinterval_back_face_le (k m : ℕ) (i : Fin (k + m + 2))
    (hi : i.val ≤ k) :
    SimplexCategory.subinterval k m (show k + m ≤ k + m by omega) ≫ SimplexCategory.δ i =
      SimplexCategory.subinterval (k + 1) m (show k + 1 + m ≤ k + m + 1 by omega) := by
  ext j
  have hj : j.val < m + 1 := j.isLt
  change (i.succAbove ⟨j.val + k, by omega⟩).val = j.val + (k + 1)
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

private theorem simplex_subinterval_back_face_lt (k m : ℕ) (i : Fin (k + m + 2))
    (hi : k < i.val) :
    SimplexCategory.subinterval k m (show k + m ≤ k + m by omega) ≫ SimplexCategory.δ i =
      SimplexCategory.δ (⟨i.val - k, by omega⟩ : Fin (m + 2)) ≫
        SimplexCategory.subinterval k (m + 1) (show k + (m + 1) ≤ k + m + 1 by omega) := by
  ext j
  have hj : j.val < m + 1 := j.isLt
  change (i.succAbove ⟨j.val + k, by omega⟩).val =
    ((⟨i.val - k, by omega⟩ : Fin (m + 2)).succAbove j).val + k
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

private theorem integralSingularSimplexSubinterval_front_face_le
    (k m : ℕ) (i : Fin (k + m + 2)) (hi : i.val ≤ k)
    (σ : integralSingularSimplex (k + m + 1) X) :
    integralSingularSimplexSubinterval 0 k (by omega)
        ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ (⟨i.val, by omega⟩ : Fin (k + 2))
        (integralSingularSimplexSubinterval 0 (k + 1) (by omega) σ) := by
  have h := congrArg (fun θ : ⦋k⦌ ⟶ ⦋k + m + 1⦌ =>
    (TopCat.toSSet.obj (TopCat.of X)).map θ.op σ)
    (simplex_subinterval_front_face_le k m i hi)
  simpa only [integralSingularSimplexSubinterval, SimplicialObject.δ,
    op_comp, Functor.map_comp, types_comp_apply] using h

private theorem integralSingularSimplexSubinterval_front_face_lt
    (k m : ℕ) (i : Fin (k + m + 2)) (hi : k < i.val)
    (σ : integralSingularSimplex (k + m + 1) X) :
    integralSingularSimplexSubinterval 0 k (by omega)
        ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) =
      integralSingularSimplexSubinterval 0 k (by omega) σ := by
  have h := congrArg (fun θ : ⦋k⦌ ⟶ ⦋k + m + 1⦌ =>
    (TopCat.toSSet.obj (TopCat.of X)).map θ.op σ)
    (simplex_subinterval_front_face_lt k m i hi)
  simpa only [integralSingularSimplexSubinterval, SimplicialObject.δ,
    op_comp, Functor.map_comp, types_comp_apply] using h

private theorem integralSingularSimplexSubinterval_back_face_le
    (k m : ℕ) (i : Fin (k + m + 2)) (hi : i.val ≤ k)
    (σ : integralSingularSimplex (k + m + 1) X) :
    integralSingularSimplexSubinterval k m le_rfl
        ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) =
      integralSingularSimplexSubinterval (k + 1) m (by omega) σ := by
  have h := congrArg (fun θ : ⦋m⦌ ⟶ ⦋k + m + 1⦌ =>
    (TopCat.toSSet.obj (TopCat.of X)).map θ.op σ)
    (simplex_subinterval_back_face_le k m i hi)
  simpa only [integralSingularSimplexSubinterval, SimplicialObject.δ,
    op_comp, Functor.map_comp, types_comp_apply] using h

private theorem integralSingularSimplexSubinterval_back_face_lt
    (k m : ℕ) (i : Fin (k + m + 2)) (hi : k < i.val)
    (σ : integralSingularSimplex (k + m + 1) X) :
    integralSingularSimplexSubinterval k m le_rfl
        ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ (⟨i.val - k, by omega⟩ : Fin (m + 2))
        (integralSingularSimplexSubinterval k (m + 1) (by omega) σ) := by
  have h := congrArg (fun θ : ⦋m⦌ ⟶ ⦋k + m + 1⦌ =>
    (TopCat.toSSet.obj (TopCat.of X)).map θ.op σ)
    (simplex_subinterval_back_face_lt k m i hi)
  simpa only [integralSingularSimplexSubinterval, SimplicialObject.δ,
    op_comp, Functor.map_comp, types_comp_apply] using h

private theorem sum_fin_front_back {A : Type*} [AddCommMonoid A]
    (k m : ℕ) (F : Fin (k + m + 2) → A) :
    ∑ i, F i = (∑ i : Fin (k + 1), F ⟨i.val, by omega⟩) +
      ∑ j : Fin (m + 1), F ⟨k + 1 + j.val, by omega⟩ := by
  calc
    ∑ i, F i = ∑ i : Fin ((k + 1) + (m + 1)), F (i.cast (by omega)) :=
      (Fin.sum_congr' F (by omega)).symm
    _ = _ := by rw [Fin.sum_univ_add]; rfl

private theorem integralSingularCapProduct_boundary_simplex_split (k m : ℕ)
    (φ : integralSingularCochain k X) (σ : integralSingularSimplex (k + m + 1) X) :
    integralSingularCapProduct k m φ
        ((integralSingularChains X).d (k + m + 1) (k + m)
          (integralSimplexChain (k + m + 1) σ)) =
      (∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val •
        ((φ (integralSimplexChain k ((TopCat.toSSet.obj (TopCat.of X)).δ i.castSucc
          (integralSingularSimplexSubinterval 0 (k + 1) (by omega) σ)))).down •
            integralSimplexChain m (integralSingularSimplexSubinterval (k + 1) m (by omega) σ))) +
      ∑ j : Fin (m + 1), (-1 : ℤ) ^ (k + 1 + j.val) •
        ((φ (integralSimplexChain k
          (integralSingularSimplexSubinterval 0 k (by omega) σ))).down •
            integralSimplexChain m ((TopCat.toSSet.obj (TopCat.of X)).δ j.succ
              (integralSingularSimplexSubinterval k (m + 1) (by omega) σ))) := by
  rw [integralSimplexChain_boundary, map_sum]
  simp_rw [map_zsmul, integralSingularCapProduct_apply_simplex]
  rw [sum_fin_front_back k m]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [integralSingularSimplexSubinterval_front_face_le k m _ (by change i.val ≤ k; omega),
      integralSingularSimplexSubinterval_back_face_le k m _ (by change i.val ≤ k; omega)]
    rfl
  · apply Finset.sum_congr rfl
    intro j _
    rw [integralSingularSimplexSubinterval_front_face_lt k m _ (by
      change k < k + 1 + j.val
      omega), integralSingularSimplexSubinterval_back_face_lt k m _ (by
      change k < k + 1 + j.val
      omega)]
    congr 3
    apply congrArg (fun i : Fin (m + 2) =>
      (TopCat.toSSet.obj (TopCat.of X)).δ i
        (integralSingularSimplexSubinterval k (m + 1) (by omega) σ))
    apply Fin.ext
    change k + 1 + j.val - k = j.val + 1
    omega

private theorem signed_cap_boundary_sum {A : Type*} [AddCommGroup A]
    (k m : ℕ) (r : Fin (k + 2) → ℤ) (B : Fin (m + 2) → A) :
    (∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • (r i.castSucc • B 0)) +
        (∑ j : Fin (m + 1), (-1 : ℤ) ^ (k + 1 + j.val) •
          (r (Fin.last (k + 1)) • B j.succ)) =
      (∑ i : Fin (k + 2), (-1 : ℤ) ^ i.val * r i) • B 0 +
        (-1 : ℤ) ^ k • (r (Fin.last (k + 1)) •
          ∑ j : Fin (m + 2), (-1 : ℤ) ^ j.val • B j) := by
  have hlow : (∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • (r i.castSucc • B 0)) =
      (∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val * r i.castSucc) • B 0 := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_smul _ _ _
  have hhigh : (∑ j : Fin (m + 1), (-1 : ℤ) ^ (k + 1 + j.val) •
        (r (Fin.last (k + 1)) • B j.succ)) =
      (-1 : ℤ) ^ k • (r (Fin.last (k + 1)) •
        ∑ j : Fin (m + 1), (-1 : ℤ) ^ (j.val + 1) • B j.succ) := by
    rw [Finset.smul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [smul_smul]
    congr 1
    rw [pow_add, pow_succ, pow_succ]
    ring
  rw [hlow, hhigh, Fin.sum_univ_castSucc (fun i : Fin (k + 2) =>
    (-1 : ℤ) ^ i.val * r i), Fin.sum_univ_succ (fun j : Fin (m + 2) =>
      (-1 : ℤ) ^ j.val • B j)]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, Fin.val_succ, pow_zero,
    one_smul, add_smul, smul_add, smul_smul, pow_succ, mul_neg, mul_one, neg_mul, neg_smul]
  abel

private theorem integralSingularSimplexSubinterval_front_last (k m : ℕ)
    (σ : integralSingularSimplex (k + m + 1) X) :
    (TopCat.toSSet.obj (TopCat.of X)).δ (Fin.last (k + 1))
        (integralSingularSimplexSubinterval 0 (k + 1) (by omega) σ) =
      integralSingularSimplexSubinterval 0 k (by omega) σ := by
  have h : SimplexCategory.δ (Fin.last (k + 1)) ≫
      SimplexCategory.subinterval 0 (k + 1) (show 0 + (k + 1) ≤ k + m + 1 by omega) =
        SimplexCategory.subinterval 0 k (show 0 + k ≤ k + m + 1 by omega) := by
    ext j
    change ((Fin.last (k + 1)).succAbove j).val + 0 = j.val + 0
    rw [Fin.succAbove_last, Fin.val_castSucc]
  have hm := congrArg (fun θ : ⦋k⦌ ⟶ ⦋k + m + 1⦌ =>
    (TopCat.toSSet.obj (TopCat.of X)).map θ.op σ) h
  simpa only [integralSingularSimplexSubinterval, SimplicialObject.δ,
    op_comp, Functor.map_comp, types_comp_apply] using hm

private theorem integralSingularSimplexSubinterval_back_first (k m : ℕ)
    (σ : integralSingularSimplex (k + m + 1) X) :
    (TopCat.toSSet.obj (TopCat.of X)).δ (0 : Fin (m + 2))
        (integralSingularSimplexSubinterval k (m + 1) (by omega) σ) =
      integralSingularSimplexSubinterval (k + 1) m (by omega) σ := by
  have h : SimplexCategory.δ (0 : Fin (m + 2)) ≫
      SimplexCategory.subinterval k (m + 1) (show k + (m + 1) ≤ k + m + 1 by omega) =
        SimplexCategory.subinterval (k + 1) m (show (k + 1) + m ≤ k + m + 1 by omega) := by
    ext j
    change ((0 : Fin (m + 2)).succAbove j).val + k = j.val + (k + 1)
    rw [Fin.succAbove_zero, Fin.val_succ]
    omega
  have hm := congrArg (fun θ : ⦋m⦌ ⟶ ⦋k + m + 1⦌ =>
    (TopCat.toSSet.obj (TopCat.of X)).map θ.op σ) h
  simpa only [integralSingularSimplexSubinterval, SimplicialObject.δ,
    op_comp, Functor.map_comp, types_comp_apply] using hm

private theorem integralSingularCoboundary_simplex_down (k : ℕ)
    (φ : integralSingularCochain k X) (σ : integralSingularSimplex (k + 1) X) :
    (integralSingularCoboundary X k (k + 1) φ (integralSimplexChain (k + 1) σ)).down =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ i.val *
        (φ (integralSimplexChain k ((TopCat.toSSet.obj (TopCat.of X)).δ i σ))).down := by
  let ψ : (integralSingularChains X).X k →ₗ[ℤ] ℤ :=
    (ULift.moduleEquiv : integralSingularCoefficients ≃ₗ[ℤ] ℤ).toLinearMap.comp φ
  change ψ ((integralSingularChains X).d (k + 1) k (integralSimplexChain (k + 1) σ)) = _
  rw [integralSimplexChain_boundary, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ψ (((-1 : ℤ) ^ i.val) • integralSimplexChain k
    ((TopCat.toSSet.obj (TopCat.of X)).δ i σ)) =
      (-1 : ℤ) ^ i.val * ψ (integralSimplexChain k
        ((TopCat.toSSet.obj (TopCat.of X)).δ i σ))
  simpa only [smul_eq_mul] using map_zsmul ψ ((-1 : ℤ) ^ i.val)
    (integralSimplexChain k ((TopCat.toSSet.obj (TopCat.of X)).δ i σ))

private theorem integralSingularCapProduct_boundary_simplex (k m : ℕ)
    (φ : integralSingularCochain k X) (σ : integralSingularSimplex (k + m + 1) X) :
    integralSingularCapProduct k m φ
        ((integralSingularChains X).d (k + m + 1) (k + m)
          (integralSimplexChain (k + m + 1) σ)) =
      (integralSingularCoboundary X k (k + 1) φ
        (integralSimplexChain (k + 1)
          (integralSingularSimplexSubinterval 0 (k + 1) (by omega) σ))).down •
            integralSimplexChain m (integralSingularSimplexSubinterval (k + 1) m (by omega) σ) +
        (-1 : ℤ) ^ k • ((integralSingularChains X).d (m + 1) m
          (integralSingularCapProduct k (m + 1) φ
            (integralSimplexChain (k + m + 1) σ))) := by
  let r (i : Fin (k + 2)) : ℤ := (φ (integralSimplexChain k
    ((TopCat.toSSet.obj (TopCat.of X)).δ i
      (integralSingularSimplexSubinterval 0 (k + 1) (by omega) σ)))).down
  let B (j : Fin (m + 2)) : (integralSingularChains X).X m := integralSimplexChain m
    ((TopCat.toSSet.obj (TopCat.of X)).δ j
      (integralSingularSimplexSubinterval k (m + 1) (by omega) σ))
  rw [integralSingularCapProduct_boundary_simplex_split,
    integralSingularCoboundary_simplex_down]
  have hc := integralSingularCapProduct_apply_simplex k (m + 1) φ σ
  change integralSingularCapProduct k (m + 1) φ (integralSimplexChain (k + m + 1) σ) = _ at hc
  rw [hc, map_zsmul, integralSimplexChain_boundary]
  simpa only [r, B, integralSingularSimplexSubinterval_front_last,
    integralSingularSimplexSubinterval_back_first] using signed_cap_boundary_sum k m r B

private theorem integralSimplexChain_XIsoOfEq {p q : ℕ} (hpq : p = q)
    (σ : integralSingularSimplex p X) :
    ((integralSingularChains X).XIsoOfEq hpq).hom (integralSimplexChain p σ) =
      integralSimplexChain q (hpq ▸ σ) := by
  subst q
  rfl

private theorem integralSingularSimplexSubinterval_cast {p q : ℕ} (hpq : p = q)
    (j k : ℕ) (hjk : j + k ≤ q) (σ : integralSingularSimplex p X) :
    integralSingularSimplexSubinterval j k hjk (hpq ▸ σ) =
      integralSingularSimplexSubinterval j k (by omega) σ := by
  subst q
  rfl

private theorem integralSingularCapProduct_XIsoOfEq_simplex (k m : ℕ)
    (φ : integralSingularCochain (k + 1) X)
    (σ : integralSingularSimplex (k + m + 1) X) :
    integralSingularCapProduct (k + 1) m φ
        (((integralSingularChains X).XIsoOfEq
          (show k + m + 1 = (k + 1) + m by omega)).hom
            (integralSimplexChain (k + m + 1) σ)) =
      (φ (integralSimplexChain (k + 1)
        (integralSingularSimplexSubinterval 0 (k + 1) (by omega) σ))).down •
          integralSimplexChain m (integralSingularSimplexSubinterval (k + 1) m (by omega) σ) := by
  rw [integralSimplexChain_XIsoOfEq, integralSingularCapProduct_apply_simplex,
    integralSingularSimplexSubinterval_cast, integralSingularSimplexSubinterval_cast]

theorem integralSingularCapProduct_boundary (k m : ℕ)
    (φ : integralSingularCochain k X) :
    (integralSingularCapProduct k m φ).comp
        ((integralSingularChains X).d (k + m + 1) (k + m)).hom =
      (integralSingularCapProduct (k + 1) m (integralSingularCoboundary X k (k + 1) φ)).comp
          (((integralSingularChains X).XIsoOfEq
            (show k + m + 1 = (k + 1) + m by omega)).hom.hom) +
        (-1 : ℤ) ^ k • (((integralSingularChains X).d (m + 1) m).hom.comp
          (integralSingularCapProduct k (m + 1) φ)) := by
  apply (integralSingularChainBasis (k + m + 1) X).ext
  intro σ
  simp only [LinearMap.comp_apply, LinearMap.add_apply,
    integralSingularChainBasis_apply, integralSingularCapProduct_XIsoOfEq_simplex]
  exact integralSingularCapProduct_boundary_simplex k m φ σ

private theorem integralSingularSimplexSubinterval_full (n : ℕ)
    (σ : integralSingularSimplex n X) :
    integralSingularSimplexSubinterval 0 n (by omega) σ = σ := by
  have h : SimplexCategory.subinterval 0 n (show 0 + n ≤ n by omega) = 𝟙 ⦋n⦌ := by
    ext j
    rfl
  simp only [integralSingularSimplexSubinterval, h, op_id]
  exact congrArg (fun f : integralSingularSimplex n X ⟶ integralSingularSimplex n X => f σ)
    ((TopCat.toSSet.obj (TopCat.of X)).map_id (Opposite.op ⦋n⦌))

private theorem integralSingularSimplexSubinterval_full_of_eq {p q : ℕ} (hpq : p = q)
    (σ : integralSingularSimplex p X) :
    integralSingularSimplexSubinterval 0 q (by omega) σ = hpq ▸ σ := by
  subst q
  exact integralSingularSimplexSubinterval_full p σ

theorem integralSingularCapProduct_augmentation (m : ℕ) :
    integralSingularCapProduct 0 m
        ((ULift.moduleEquiv : integralSingularCoefficients ≃ₗ[ℤ] ℤ).symm.toLinearMap.comp
          integralSingularAugmentation) =
      (((integralSingularChains X).XIsoOfEq (Nat.zero_add m)).hom.hom) := by
  apply (integralSingularChainBasis (0 + m) X).ext
  intro σ
  simp only [integralSingularChainBasis_apply, integralSingularCapProduct_apply_simplex,
    integralSimplexChain_XIsoOfEq]
  have hφ : (((ULift.moduleEquiv : integralSingularCoefficients ≃ₗ[ℤ] ℤ).symm.toLinearMap.comp
      integralSingularAugmentation) (integralSimplexChain 0
        (integralSingularSimplexSubinterval 0 0 (by omega) σ))).down = 1 := by
    change integralSingularAugmentation (integralSimplexChain 0 _) = 1
    exact integralSingularAugmentation_simplex _
  rw [hφ, one_smul, integralSingularSimplexSubinterval_full_of_eq (Nat.zero_add m)]

theorem integralSingularCapProduct_boundary_eq_zero (k m : ℕ)
    (φ : integralSingularCochain k X) (hφ : integralSingularCoboundary X k (k + 1) φ = 0)
    (c : (integralSingularChains X).X (k + m + 1))
    (hc : (integralSingularChains X).d (k + m + 1) (k + m) c = 0) :
    (integralSingularChains X).d (m + 1) m (integralSingularCapProduct k (m + 1) φ c) = 0 := by
  have h := congrArg (fun f : (integralSingularChains X).X (k + m + 1) →ₗ[ℤ]
    (integralSingularChains X).X m => f c) (integralSingularCapProduct_boundary k m φ)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, hφ, hc, map_zero,
    LinearMap.zero_apply, zero_add] at h
  have heval := map_zsmul
    (LinearMap.applyₗ (R := ℤ) (M₂ := (integralSingularChains X).X m) c)
    ((-1 : ℤ) ^ k) (((integralSingularChains X).d (m + 1) m).hom.comp
      (integralSingularCapProduct k (m + 1) φ))
  change ((-1 : ℤ) ^ k • (((integralSingularChains X).d (m + 1) m).hom.comp
    (integralSingularCapProduct k (m + 1) φ))) c =
      (-1 : ℤ) ^ k • (integralSingularChains X).d (m + 1) m
        (integralSingularCapProduct k (m + 1) φ c) at heval
  have hz := heval.symm.trans h.symm
  rcases Nat.even_or_odd k with hk | hk
  · simpa only [hk.neg_one_pow, one_zsmul] using hz
  · simpa only [hk.neg_one_pow, neg_one_zsmul, neg_eq_zero] using hz

end DifferentialGeometry.Topology

end
