module

public import DifferentialGeometry.Topology.Homology.SingularPair
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

open CategoryTheory Limits AlgebraicTopology Convexity
open scoped Simplicial

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

abbrev Δ (n : ℕ) : Type := StdSimplex ℝ (Fin (n + 1))

abbrev wt {n : ℕ} (t : Δ n) : Fin (n + 1) → ℝ := t.weights

lemma weights_iConvexComb' {I J : Type*} (w : StdSimplex ℝ I) (f : I → StdSimplex ℝ J) :
    (iConvexComb w f).weights = w.weights.sum (fun i r => r • (f i).weights) := by
  simp [iConvexComb, StdSimplex.weights_sConvexComb, Finsupp.sum_mapDomain_index, add_smul]

lemma weights_affineMapMk_apply {m n : ℕ} (v : Fin (m + 1) → Δ n) (t : Δ m)
    (j : Fin (n + 1)) :
    (StdSimplex.affineMapMk v t).weights j = ∑ i, t.weights i * (v i).weights j := by
  rw [StdSimplex.affineMapMk_apply, weights_iConvexComb',
    Finsupp.sum_fintype _ _ (by simp)]
  simp

lemma continuous_affineMapMk {m n : ℕ} (v : Fin (m + 1) → Δ n) :
    Continuous (StdSimplex.affineMapMk (R := ℝ) v) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
  refine continuous_pi fun j => ?_
  simp only [Function.comp_def, weights_affineMapMk_apply]
  fun_prop

def affineSimplex {m n : ℕ} (v : Fin (m + 1) → Δ n) : C(Δ m, Δ n) :=
  ⟨StdSimplex.affineMapMk v, continuous_affineMapMk v⟩

@[simp] lemma affineSimplex_apply {m n : ℕ} (v : Fin (m + 1) → Δ n) (t : Δ m) :
    affineSimplex v t = StdSimplex.affineMapMk v t := rfl

lemma affineSimplex_single_apply {m n : ℕ} (v : Fin (m + 1) → Δ n) (i : Fin (m + 1)) :
    affineSimplex v (.single i) = v i := by simp

lemma affineSimplex_single {n : ℕ} :
    affineSimplex (fun i : Fin (n + 1) => (StdSimplex.single i : Δ n)) = .id _ := by
  ext t : 1
  simp [StdSimplex.affineMapMk_apply]

lemma affineSimplex_comp_map {k m n : ℕ} (v : Fin (m + 1) → Δ n)
    (f : Fin (k + 1) → Fin (m + 1)) :
    (affineSimplex v).comp ⟨StdSimplex.map f, StdSimplex.continuous_map ℝ f⟩ =
      affineSimplex (v ∘ f) := by
  ext t : 1
  simp [StdSimplex.affineMapMk_apply, iConvexComb_map, Function.comp_def]

lemma affineSimplex_comp_affineSimplex {k m n : ℕ} (v : Fin (m + 1) → Δ n)
    (w : Fin (k + 1) → Δ m) :
    (affineSimplex v).comp (affineSimplex w) = affineSimplex (affineSimplex v ∘ w) := by
  ext t : 1
  change (StdSimplex.affineMapMk v).comp (StdSimplex.affineMapMk w) t = _
  rw [StdSimplex.comp_affineMapMk]
  rfl

lemma affineSimplex_single_comp {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    affineSimplex (fun i => (StdSimplex.single (f i) : Δ n)) =
      ⟨StdSimplex.map f, StdSimplex.continuous_map ℝ f⟩ := by
  ext t : 1
  simp only [affineSimplex_apply, ContinuousMap.coe_mk, StdSimplex.affineMapMk_apply]
  rw [← iConvexComb_map t f StdSimplex.single]
  exact StdSimplex.iConvexComb_single _

lemma toSSetObjEquiv_symm_δ {X : TopCat.{u}} {n : ℕ} (f : C(Δ (n + 1), X)) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ i ((X.toSSetObjEquiv _).symm f) =
      (X.toSSetObjEquiv _).symm (f.comp (affineSimplex fun j => .single (i.succAbove j))) := by
  rw [affineSimplex_single_comp]
  rfl

def bary {m n : ℕ} (v : Fin (m + 1) → Δ n) : Δ n :=
  iConvexComb (StdSimplex.barycenter (K := ℝ) (M := Fin (m + 1))) v

lemma affineSimplex_bary {k m n : ℕ} (u : Fin (m + 1) → Δ n) (v : Fin (k + 1) → Δ m) :
    affineSimplex u (bary v) = bary (affineSimplex u ∘ v) := by
  simp only [affineSimplex_apply, bary]
  exact (StdSimplex.affineMapMk u).isAffineMap.map_iConvexComb _ _

lemma bary_const {m n : ℕ} (b : Δ n) : bary (fun _ : Fin (m + 1) => b) = b := by
  simp [bary]

lemma weights_bary {m n : ℕ} (v : Fin (m + 1) → Δ n) (j : Fin (n + 1)) :
    (bary v).weights j = ∑ i, ((m : ℝ) + 1)⁻¹ * (v i).weights j := by
  rw [bary, weights_iConvexComb', Finsupp.sum_fintype _ _ (by simp)]
  simp [StdSimplex.weights_barycenter_apply]

abbrev cone {m n : ℕ} (b : Δ n) (v : Fin m → Δ n) : Fin (m + 1) → Δ n := Fin.cons b v

lemma cone_comp_succAbove_zero {m n : ℕ} (b : Δ n) (v : Fin m → Δ n) :
    cone b v ∘ (0 : Fin (m + 1)).succAbove = v := by
  funext j; simp [cone]

lemma cone_comp_succAbove_succ {m n : ℕ} (b : Δ n) (v : Fin (m + 1) → Δ n) (i : Fin (m + 1)) :
    cone b v ∘ i.succ.succAbove = cone b (v ∘ i.succAbove) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [cone]
  · simp [cone, Fin.succ_succAbove_succ]

lemma cone_fin_zero {n : ℕ} (b : Δ n) (v : Fin 0 → Δ n) : cone b v = fun _ => b := by
  funext j
  obtain rfl : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt)
  rfl

lemma comp_cone {m n n' : ℕ} (u : Δ n → Δ n') (b : Δ n) (v : Fin m → Δ n) :
    u ∘ cone b v = cone (u b) (u ∘ v) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [cone]

abbrev AffChain (k n : ℕ) : Type := (Fin (k + 1) → Δ n) →₀ ℤ

namespace AffChain

def push {n n' : ℕ} (u : Δ n → Δ n') (k : ℕ) : AffChain k n →ₗ[ℤ] AffChain k n' :=
  Finsupp.lmapDomain ℤ ℤ (fun w => u ∘ w)

def coneL {n : ℕ} (b : Δ n) (k : ℕ) : AffChain k n →ₗ[ℤ] AffChain (k + 1) n :=
  Finsupp.lmapDomain ℤ ℤ (cone b)

def face {n : ℕ} (k : ℕ) (i : Fin (k + 2)) : AffChain (k + 1) n →ₗ[ℤ] AffChain k n :=
  Finsupp.lmapDomain ℤ ℤ (fun w => w ∘ i.succAbove)

def bd {n : ℕ} (k : ℕ) : AffChain (k + 1) n →ₗ[ℤ] AffChain k n :=
  ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • face k i

def eps {n : ℕ} : AffChain 0 n →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ (fun _ => 1)

@[simp] lemma push_single {n n' : ℕ} (u : Δ n → Δ n') {k : ℕ} (w : Fin (k + 1) → Δ n)
    (z : ℤ) :
    push u k (Finsupp.single w z) = Finsupp.single (u ∘ w) z := by
  simp [push]

@[simp] lemma coneL_single {n : ℕ} (b : Δ n) {k : ℕ} (w : Fin (k + 1) → Δ n) (z : ℤ) :
    coneL b k (Finsupp.single w z) = Finsupp.single (cone b w) z := by
  simp [coneL]

@[simp] lemma face_single {n : ℕ} {k : ℕ} (i : Fin (k + 2)) (w : Fin (k + 2) → Δ n)
    (z : ℤ) :
    face k i (Finsupp.single w z) = Finsupp.single (w ∘ i.succAbove) z := by
  simp [face]

lemma bd_single {n : ℕ} {k : ℕ} (w : Fin (k + 2) → Δ n) (z : ℤ) :
    bd k (Finsupp.single w z) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (w ∘ i.succAbove) z := by
  simp only [bd, LinearMap.sum_apply, LinearMap.smul_apply, face_single]

@[simp] lemma eps_single {n : ℕ} (w : Fin 1 → Δ n) (z : ℤ) :
    eps (Finsupp.single w z) = z := by
  simp [eps]

lemma push_comp_push {n n' n'' : ℕ} (u : Δ n → Δ n') (u' : Δ n' → Δ n'') (k : ℕ) :
    (push u' k).comp (push u k) = push (u' ∘ u) k := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, push_single, Function.comp_assoc]

lemma push_id {n : ℕ} (k : ℕ) : push (id : Δ n → Δ n) k = LinearMap.id := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, push_single, Function.id_comp,
    LinearMap.id_apply]

lemma push_comp_coneL {n n' : ℕ} (u : Δ n → Δ n') (b : Δ n) (k : ℕ) :
    (push u (k + 1)).comp (coneL b k) = (coneL (u b) k).comp (push u k) := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, push_single, coneL_single, comp_cone]

lemma push_comp_face {n n' : ℕ} (u : Δ n → Δ n') (k : ℕ) (i : Fin (k + 2)) :
    (push u k).comp (face k i) = (face k i).comp (push u (k + 1)) := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, push_single, face_single,
    Function.comp_assoc]

lemma push_comp_bd {n n' : ℕ} (u : Δ n → Δ n') (k : ℕ) :
    (push u k).comp (bd k) = (bd k).comp (push u (k + 1)) := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, push_single, bd_single, map_sum,
    map_zsmul, Function.comp_assoc]

lemma eps_comp_push {n n' : ℕ} (u : Δ n → Δ n') :
    eps.comp (push u 0) = eps := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, push_single, eps_single]

lemma eps_comp_bd {n : ℕ} : eps.comp (bd 0 : AffChain 1 n →ₗ[ℤ] AffChain 0 n) = 0 := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, bd_single, map_sum, map_zsmul,
    eps_single, LinearMap.zero_comp, LinearMap.zero_apply]
  simp

lemma face_comp_coneL_zero {n : ℕ} (b : Δ n) (k : ℕ) :
    (face k 0).comp (coneL b k) = LinearMap.id := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, coneL_single, face_single,
    cone_comp_succAbove_zero, LinearMap.id_apply]

lemma face_comp_coneL_succ {n : ℕ} (b : Δ n) (k : ℕ) (i : Fin (k + 2)) :
    (face (k + 1) i.succ).comp (coneL b (k + 1)) = (coneL b k).comp (face k i) := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, coneL_single, face_single,
    cone_comp_succAbove_succ]

lemma bd_comp_coneL {n : ℕ} (b : Δ n) (k : ℕ) :
    (bd (k + 1)).comp (coneL b (k + 1)) = LinearMap.id - (coneL b k).comp (bd k) := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
    LinearMap.id_apply, coneL_single, bd_single, map_sum, map_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, cone_comp_succAbove_zero,
    cone_comp_succAbove_succ, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib]
  abel

lemma bd_coneL_zero {n : ℕ} (b : Δ n) (c : AffChain 0 n) :
    bd 0 (coneL b 0 c) = c - eps c • Finsupp.single (fun _ => b) 1 := by
  have : (bd 0).comp (coneL b 0) =
      LinearMap.id - (Finsupp.lsingle (fun _ => b)).comp (eps (n := n)) := by
    ext w : 2
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
      LinearMap.id_apply, coneL_single, bd_single, eps_single]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, cone_comp_succAbove_zero,
      cone_comp_succAbove_succ, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero, cone_fin_zero, sub_eq_add_neg]
  have h := LinearMap.congr_fun this c
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    Finsupp.lsingle_apply] at h
  rw [h, Finsupp.smul_single, smul_eq_mul, mul_one]

lemma neg_one_pow_succAbove_predAbove {k : ℕ} (i : Fin (k + 3)) (j : Fin (k + 2)) :
    (-1 : ℤ) ^ ((i.succAbove j : Fin (k + 3)) : ℕ) *
      (-1) ^ ((j.predAbove i : Fin (k + 2)) : ℕ) = -((-1) ^ (i : ℕ) * (-1) ^ (j : ℕ)) := by
  have key : (i.succAbove j : ℕ) + (j.predAbove i : ℕ) + 1 = i + j ∨
      (i.succAbove j : ℕ) + (j.predAbove i : ℕ) = i + j + 1 := by
    simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
      Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
    split_ifs <;> omega
  rw [← pow_add, ← pow_add]
  rcases key with h | h
  · rw [← h, pow_succ]; ring
  · rw [h, pow_succ]; ring

lemma bd_comp_bd {n : ℕ} (k : ℕ) :
    (bd k).comp (bd (k + 1) : AffChain (k + 2) n →ₗ[ℤ] _) = 0 := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_comp,
    LinearMap.zero_apply, bd_single, map_sum, map_zsmul, Finset.smul_sum, smul_smul,
    Function.comp_assoc]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  refine Finset.sum_ninvolution (fun p => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_
    (fun _ => Finset.mem_univ _) ?_
  · rintro ⟨i, j⟩
    have hf : w ∘ (i.succAbove j).succAbove ∘ (j.predAbove i).succAbove =
        w ∘ i.succAbove ∘ j.succAbove := by
      funext l
      simp only [Function.comp_apply, Fin.succAbove_succAbove_succAbove_predAbove]
    simp only [hf, neg_one_pow_succAbove_predAbove, neg_smul, add_neg_cancel]
  · rintro ⟨i, j⟩ - h
    exact Fin.succAbove_ne i j (congrArg Prod.fst h)
  · rintro ⟨i, j⟩
    exact Prod.ext (Fin.succAbove_succAbove_predAbove i j) (Fin.predAbove_predAbove_succAbove i j)

end AffChain

abbrev sing {X : TopCat.{u}} {k : ℕ} (f : C(Δ k, X)) : (TopCat.toSSet.obj X) _⦋k⦌ :=
  (X.toSSetObjEquiv _).symm f

abbrev affSing {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) {k : ℕ} (w : Fin (k + 1) → Δ m) :
    (TopCat.toSSet.obj X) _⦋k⦌ :=
  sing (σ.comp (affineSimplex w))

lemma δ_sing {X : TopCat.{u}} {k : ℕ} (f : C(Δ (k + 1), X)) (i : Fin (k + 2)) :
    (TopCat.toSSet.obj X).δ i (sing f) =
      sing (f.comp (affineSimplex fun j => .single (i.succAbove j))) :=
  toSSetObjEquiv_symm_δ f i

lemma δ_affSing {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) {k : ℕ} (w : Fin (k + 2) → Δ m)
    (i : Fin (k + 2)) :
    (TopCat.toSSet.obj X).δ i (affSing σ w) = affSing σ (w ∘ i.succAbove) := by
  change (TopCat.toSSet.obj X).δ i (sing (σ.comp (affineSimplex w))) =
    sing (σ.comp (affineSimplex (w ∘ i.succAbove)))
  rw [δ_sing, ContinuousMap.comp_assoc, affineSimplex_comp_affineSimplex]
  congr 3
  funext j
  simp

@[simp] lemma rightComp_apply_eq {V : Type*} [Category V] [Preadditive V] (P : V) {Q S : V}
    (g : Q ⟶ S) (f : P ⟶ Q) : Preadditive.rightComp P g f = f ≫ g := rfl

lemma affSing_comp {X : TopCat.{u}} {m m' : ℕ} (σ : C(Δ m, X)) (v : Fin (m' + 1) → Δ m)
    {k : ℕ} (w : Fin (k + 1) → Δ m') :
    affSing (σ.comp (affineSimplex v)) w = affSing σ (affineSimplex v ∘ w) := by
  change sing ((σ.comp (affineSimplex v)).comp (affineSimplex w)) =
    sing (σ.comp (affineSimplex (affineSimplex v ∘ w)))
  rw [ContinuousMap.comp_assoc, affineSimplex_comp_affineSimplex]

lemma toSSet_map_app_sing {X Y : TopCat.{u}} (f : X ⟶ Y) {k : ℕ} (g : C(Δ k, X)) :
    (TopCat.toSSet.map f).app _ (sing g) = sing (f.hom.comp g) :=
  rfl

variable (R : ModuleCat.{u} ℤ)

abbrev simplicialChains (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (TopCat.toSSet.obj X).chainComplex R

example (X : TopCat.{u}) : simplicialChains R X = singularChains R X := rfl

lemma singularChainFunctor_map_eq {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (singularChainFunctor R).map f = SSet.chainComplexMap (TopCat.toSSet.map f) R := rfl

def toChain {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) (k : ℕ) :
    AffChain k m →+ (R ⟶ (simplicialChains R X).X k) :=
  Finsupp.liftAddHom fun w => zmultiplesHom _ ((TopCat.toSSet.obj X).ιChainComplex (affSing σ w))

@[simp] lemma toChain_single {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) {k : ℕ}
    (w : Fin (k + 1) → Δ m) (z : ℤ) :
    toChain R σ k (Finsupp.single w z) =
      z • (TopCat.toSSet.obj X).ιChainComplex (affSing σ w) := by
  simp [toChain]

lemma toChain_apply {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) {k : ℕ} (c : AffChain k m) :
    toChain R σ k c =
      c.sum fun w z => z • (TopCat.toSSet.obj X).ιChainComplex (affSing σ w) := by
  rw [toChain, Finsupp.liftAddHom_apply]
  rfl

lemma toChain_bd {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) (k : ℕ) (c : AffChain (k + 1) m) :
    toChain R σ k (AffChain.bd k c) = toChain R σ (k + 1) c ≫ (simplicialChains R X).d (k + 1) k := by
  suffices (toChain R σ k).comp (AffChain.bd k).toAddMonoidHom =
      (Preadditive.rightComp R ((simplicialChains R X).d (k + 1) k)).comp (toChain R σ (k + 1)) from
    DFunLike.congr_fun this c
  ext w : 2
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, LinearMap.toAddMonoidHom_coe,
    AffChain.bd_single, map_sum, map_zsmul, toChain_single, one_smul, rightComp_apply_eq,
    SSet.ιChainComplex_d, δ_affSing]

lemma toChain_push {X : TopCat.{u}} {m m' : ℕ} (σ : C(Δ m, X)) (v : Fin (m' + 1) → Δ m)
    (k : ℕ) (c : AffChain k m') :
    toChain R σ k (AffChain.push (affineSimplex v) k c) =
      toChain R (σ.comp (affineSimplex v)) k c := by
  suffices (toChain R σ k).comp (AffChain.push (affineSimplex v) k).toAddMonoidHom =
      toChain R (σ.comp (affineSimplex v)) k from DFunLike.congr_fun this c
  ext w : 2
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, LinearMap.toAddMonoidHom_coe,
    AffChain.push_single, toChain_single, affSing_comp]

lemma toChain_map {X Y : TopCat.{u}} (f : X ⟶ Y) {m : ℕ} (σ : C(Δ m, X)) (k : ℕ)
    (c : AffChain k m) :
    toChain R σ k c ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f k =
      toChain R (f.hom.comp σ) k c := by
  suffices (Preadditive.rightComp R ((SSet.chainComplexMap (TopCat.toSSet.map f) R).f k)).comp
      (toChain R σ k) = toChain R (f.hom.comp σ) k from DFunLike.congr_fun this c
  ext w : 2
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, toChain_single,
    rightComp_apply_eq, SSet.ι_chainComplexMap_f, toSSet_map_app_sing, one_smul]
  rfl

abbrev idVerts (m : ℕ) : Fin (m + 1) → Δ m := fun i => StdSimplex.single i

lemma affSing_idVerts {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) :
    affSing σ (idVerts m) = sing σ := by
  simp [affSing, affineSimplex_single]

lemma toChain_single_idVerts {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) :
    toChain R σ m (Finsupp.single (idVerts m) 1) =
      (TopCat.toSSet.obj X).ιChainComplex (sing σ) := by
  simp [affSing_idVerts]

open Classical in
def toChainSub {X : TopCat.{u}} (A : (TopCat.toSSet.obj X).Subcomplex) {m : ℕ} (σ : C(Δ m, X))
    (k : ℕ) : AffChain k m →+ (R ⟶ (A.toSSet.chainComplex R).X k) :=
  Finsupp.liftAddHom fun w => zmultiplesHom _
    (if h : affSing σ w ∈ A.obj _ then A.toSSet.ιChainComplex (⟨affSing σ w, h⟩ : A.obj _)
      else 0)

lemma toChainSub_ι {X : TopCat.{u}} (A : (TopCat.toSSet.obj X).Subcomplex) {m : ℕ}
    (σ : C(Δ m, X)) (k : ℕ) (c : AffChain k m)
    (hc : ∀ w ∈ c.support, affSing σ w ∈ A.obj _) :
    toChainSub R A σ k c ≫ (SSet.chainComplexMap A.ι R).f k = toChain R σ k c := by
  rw [toChain_apply, toChainSub, Finsupp.liftAddHom_apply]
  simp only [zmultiplesHom_apply, Finsupp.sum]
  rw [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Preadditive.zsmul_comp, dite_eq_left (hc w hw), SSet.ι_chainComplexMap_f]
  rfl

lemma wt_affineSimplex {m n : ℕ} (v : Fin (m + 1) → Δ n) (t : Δ m) :
    wt (affineSimplex v t) = ∑ i, t.weights i • wt (v i) := by
  funext j
  simp [weights_affineMapMk_apply, Finset.sum_apply]

lemma wt_affineSimplex_mem_convexHull {m n : ℕ} (v : Fin (m + 1) → Δ n) (t : Δ m) :
    wt (affineSimplex v t) ∈ _root_.convexHull ℝ (Set.range (wt ∘ v)) := by
  rw [wt_affineSimplex]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => t.weights_nonneg i) (by simp)
    (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)

lemma range_wt_comp_affineSimplex_subset {m n : ℕ} (v : Fin (m + 1) → Δ n) :
    Set.range (wt ∘ affineSimplex v) ⊆ _root_.convexHull ℝ (Set.range (wt ∘ v)) := by
  rintro _ ⟨t, rfl⟩
  exact wt_affineSimplex_mem_convexHull v t

lemma isBounded_range_wt (n : ℕ) : Bornology.IsBounded (Set.range (wt (n := n))) :=
  StdSimplex.isBounded_range_toFun_comp_weights _

lemma isBounded_of_subset_range_wt {n : ℕ} {s : Set (Fin (n + 1) → ℝ)}
    (hs : s ⊆ Set.range wt) : Bornology.IsBounded s :=
  (isBounded_range_wt n).subset hs

lemma isBounded_range_wt_comp {n : ℕ} {α : Type*} (v : α → Δ n) :
    Bornology.IsBounded (Set.range (wt ∘ v)) :=
  isBounded_of_subset_range_wt (by rintro _ ⟨i, rfl⟩; exact ⟨v i, rfl⟩)

lemma diam_range_wt_le (n : ℕ) : Metric.diam (Set.range (wt (n := n))) ≤ 1 :=
  StdSimplex.diam_range_toFun_comp_weights_subset_closedBall _

lemma wt_bary {m n : ℕ} (v : Fin (m + 1) → Δ n) :
    wt (bary v) = ∑ i, ((m : ℝ) + 1)⁻¹ • wt (v i) := by
  funext j; simp [weights_bary, Finset.sum_apply]

lemma dist_wt_bary_le {m n : ℕ} (v : Fin (m + 1) → Δ n) (j : Fin (m + 1)) :
    dist (wt (bary v)) (wt (v j)) ≤ (m / (m + 1 : ℝ)) * Metric.diam (Set.range (wt ∘ v)) := by
  classical
  have hb := isBounded_range_wt_comp v
  rw [dist_eq_norm, wt_bary]
  have : ∑ i, ((m : ℝ) + 1)⁻¹ • wt (v i) - wt (v j) =
      ∑ i, ((m : ℝ) + 1)⁻¹ • (wt (v i) - wt (v j)) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [mul_inv_cancel₀ (by positivity), one_smul]
  rw [this]
  calc ‖∑ i, ((m : ℝ) + 1)⁻¹ • (wt (v i) - wt (v j))‖
      ≤ ∑ i, ‖((m : ℝ) + 1)⁻¹ • (wt (v i) - wt (v j))‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.univ.erase j, ((m : ℝ) + 1)⁻¹ * ‖wt (v i) - wt (v j)‖ := by
        rw [← Finset.sum_erase (s := Finset.univ) (a := j)
          (f := fun i => ‖((m : ℝ) + 1)⁻¹ • (wt (v i) - wt (v j))‖) (by simp)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (show (0 : ℝ) ≤ ((m : ℝ) + 1)⁻¹ by positivity)]
    _ ≤ ∑ i ∈ Finset.univ.erase j,
          ((m : ℝ) + 1)⁻¹ * Metric.diam (Set.range (wt ∘ v)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        rw [← dist_eq_norm]
        exact Metric.dist_le_diam_of_mem hb ⟨i, rfl⟩ ⟨j, rfl⟩
    _ = (m / (m + 1 : ℝ)) * Metric.diam (Set.range (wt ∘ v)) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

lemma dist_wt_map_le {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (hf : Function.Injective f)
    (s t : Δ m) :
    dist (wt (StdSimplex.map f s)) (wt (StdSimplex.map f t)) ≤ dist (wt s) (wt t) := by
  rw [dist_pi_le_iff dist_nonneg]
  intro b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    simp only [wt, StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective hf]
    exact dist_le_pi_dist _ _ a
  · simp only [wt, StdSimplex.weights_map, Finsupp.mapDomain_of_notMem_range _ _ hb]
    simp

end DifferentialGeometry.Topology.SingularPair
