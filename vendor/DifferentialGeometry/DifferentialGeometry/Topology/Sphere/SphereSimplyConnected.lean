module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace DifferentialGeometry.Topology

open Metric Module Set unitInterval

noncomputable section

def clamp01 (r : ℝ) : ℝ := max 0 (min r 1)

@[fun_prop]
theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clamp01_of_nonpos {r : ℝ} (h : r ≤ 0) : clamp01 r = 0 := by
  unfold clamp01
  rw [max_eq_left]
  exact (min_le_left _ _).trans h

theorem clamp01_of_one_le {r : ℝ} (h : 1 ≤ r) : clamp01 r = 1 := by
  unfold clamp01
  rw [min_eq_right h, max_eq_right zero_le_one]

theorem clamp01_of_mem {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : clamp01 r = r := by
  unfold clamp01
  rw [min_eq_left h1, max_eq_right h0]

theorem convex_pos {a b θ : ℝ} (ha : 0 < a) (hb : 0 < b) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    0 < (1 - θ) * a + θ * b := by
  rcases eq_or_lt_of_le h1 with rfl | hlt
  · simpa
  · have h2 : 0 < (1 - θ) * a := mul_pos (by linarith) ha
    have h3 : 0 ≤ θ * b := mul_nonneg h0 hb.le
    linarith

theorem exists_piece {n : ℕ} (hn : 0 < n) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ∃ i < n, (i : ℝ) / n ≤ s ∧ s ≤ (i + 1) / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rcases eq_or_lt_of_le h1 with rfl | hlt
  · refine ⟨n - 1, Nat.sub_lt hn one_pos, ?_, ?_⟩
    · rw [div_le_one hn']
      exact_mod_cast Nat.sub_le n 1
    · rw [le_div_iff₀ hn', one_mul]
      have : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        rw [← Nat.cast_succ]
        congr 1
        omega
      linarith
  · refine ⟨⌊n * s⌋₊, ?_, ?_, ?_⟩
    · rw [Nat.floor_lt (by positivity)]
      nlinarith
    · rw [div_le_iff₀ hn', mul_comm]
      exact Nat.floor_le (by positivity)
    · rw [le_div_iff₀ hn', mul_comm]
      exact (Nat.lt_floor_add_one _).le

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_pos_of_norm_sub_lt_one {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : ‖u - v‖ < 1) : 0 < inner ℝ u v := by
  have h1 := norm_sub_sq_real u v
  rw [hu, hv] at h1
  have h2 : ‖u - v‖ ^ 2 < 1 := by nlinarith [norm_nonneg (u - v)]
  linarith

def radialProj (v : E) : E := ‖v‖⁻¹ • v

theorem norm_radialProj {v : E} (hv : v ≠ 0) : ‖radialProj v‖ = 1 := by
  simpa [radialProj] using norm_smul_inv_norm (𝕜 := ℝ) hv

theorem radialProj_mem_sphere {v : E} (hv : v ≠ 0) : radialProj v ∈ sphere (0 : E) 1 :=
  mem_sphere_zero_iff_norm.2 (norm_radialProj hv)

theorem radialProj_of_norm_eq_one {v : E} (hv : ‖v‖ = 1) : radialProj v = v := by
  simp [radialProj, hv]

theorem continuous_radialProj_comp {X : Type*} [TopologicalSpace X] {f : X → E}
    (hf : Continuous f) (h : ∀ x, f x ≠ 0) : Continuous fun x => radialProj (f x) :=
  ((continuous_norm.comp hf).inv₀ fun x => norm_ne_zero_iff.mpr (h x)).smul hf

theorem radialProj_mem_span {W : Submodule ℝ E} {v : E} (h : v ∈ W) : radialProj v ∈ W :=
  W.smul_mem _ h

theorem mem_span_of_radialProj_mem {W : Submodule ℝ E} {v : E} (hv : v ≠ 0)
    (h : radialProj v ∈ W) : v ∈ W := by
  have := W.smul_mem ‖v‖ h
  rwa [radialProj, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul] at this

def polygon (p : ℕ → E) (n : ℕ) (s : ℝ) : E :=
  p 0 + ∑ j ∈ Finset.range n, clamp01 (n * s - j) • (p (j + 1) - p j)

@[fun_prop]
theorem continuous_polygon (p : ℕ → E) (n : ℕ) : Continuous (polygon p n) := by
  unfold polygon
  refine continuous_const.add (continuous_finsetSum _ fun j _ => ?_)
  exact (continuous_clamp01.comp (by fun_prop)).smul continuous_const

theorem polygon_zero (p : ℕ → E) (n : ℕ) : polygon p n 0 = p 0 := by
  unfold polygon
  rw [Finset.sum_eq_zero, add_zero]
  intro j _
  rw [clamp01_of_nonpos (by simp), zero_smul]

theorem polygon_one (p : ℕ → E) (n : ℕ) : polygon p n 1 = p n := by
  unfold polygon
  have h : ∀ j ∈ Finset.range n, clamp01 (n * 1 - j) • (p (j + 1) - p j) = p (j + 1) - p j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    rw [clamp01_of_one_le (by linarith), one_smul]
  rw [Finset.sum_congr rfl h, Finset.sum_range_sub]
  abel

theorem polygon_eq_of_mem (p : ℕ → E) {n i : ℕ} (hi : i < n) {s : ℝ} (hs : (i : ℝ) / n ≤ s)
    (hs' : s ≤ (i + 1) / n) :
    polygon p n s = p i + (n * s - i) • (p (i + 1) - p i) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le i) hi)
  have hs1 : (i : ℝ) ≤ n * s := by rwa [div_le_iff₀ hn', mul_comm] at hs
  have hs2 : n * s ≤ (i : ℝ) + 1 := by rwa [le_div_iff₀ hn', mul_comm] at hs'
  unfold polygon
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hi), Finset.sum_range_succ]
  have h1 : ∀ j ∈ Finset.range i, clamp01 (n * s - j) • (p (j + 1) - p j) = p (j + 1) - p j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj' : (j : ℝ) + 1 ≤ i := by exact_mod_cast hj
    rw [clamp01_of_one_le (by linarith), one_smul]
  have h2 : ∀ j ∈ Finset.Ico (i + 1) n, clamp01 (n * s - j) • (p (j + 1) - p j) = 0 := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hj' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hj.1
    rw [clamp01_of_nonpos (by linarith), zero_smul]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_range_sub,
    Finset.sum_const_zero, add_zero, clamp01_of_mem (by linarith) (by linarith)]
  abel

theorem polygon_mem_span (p : ℕ → E) {n i : ℕ} (hi : i < n) {s : ℝ} (hs : (i : ℝ) / n ≤ s)
    (hs' : s ≤ (i + 1) / n) :
    polygon p n s ∈ Submodule.span ℝ {p i, p (i + 1)} := by
  rw [polygon_eq_of_mem p hi hs hs', Submodule.mem_span_pair]
  refine ⟨1 - (n * s - i), n * s - i, ?_⟩
  rw [sub_smul, one_smul, smul_sub]
  abel

theorem inner_polygon_pos (p : ℕ → E) {n i : ℕ} (hi : i < n) {s : ℝ} (hs : (i : ℝ) / n ≤ s)
    (hs' : s ≤ (i + 1) / n) {v : E} (h1 : 0 < inner ℝ (p i) v) (h2 : 0 < inner ℝ (p (i + 1)) v) :
    0 < inner ℝ (polygon p n s) v := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le i) hi)
  have hs1 : (i : ℝ) ≤ n * s := by rwa [div_le_iff₀ hn', mul_comm] at hs
  have hs2 : n * s ≤ (i : ℝ) + 1 := by rwa [le_div_iff₀ hn', mul_comm] at hs'
  rw [polygon_eq_of_mem p hi hs hs', inner_add_left, real_inner_smul_left, inner_sub_left]
  have key := convex_pos h1 h2 (by linarith : 0 ≤ n * s - i) (by linarith : n * s - i ≤ 1)
  have : inner ℝ (p i) v + (n * s - i) * (inner ℝ (p (i + 1)) v - inner ℝ (p i) v)
      = (1 - (n * s - i)) * inner ℝ (p i) v + (n * s - i) * inner ℝ (p (i + 1)) v := by ring
  rw [this]
  exact key

theorem exists_subdivision {x : sphere (0 : E) 1} (γ : Path x x) :
    ∃ n : ℕ, 0 < n ∧ ∀ i < n, ∀ s : I, (i : ℝ) / n ≤ s → (s : ℝ) ≤ (i + 1) / n →
      0 < inner ℝ (γ s : E) (γ.extend ((i : ℝ) / n) : E) := by
  have hc : Continuous fun s : I => (γ s : E) := continuous_subtype_val.comp γ.continuous
  have hu := CompactSpace.uniformContinuous_of_continuous hc
  rw [Metric.uniformContinuous_iff] at hu
  obtain ⟨ε, hε, hεu⟩ := hu 1 one_pos
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  refine ⟨m + 1, Nat.succ_pos m, fun i hi s hs hs' => ?_⟩
  have hn' : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos m)
  have hin : (i : ℝ) / ((m + 1 : ℕ) : ℝ) ∈ I := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
    rw [div_le_one hn']
    exact_mod_cast hi.le
  rw [Path.extend_extends' γ ⟨_, hin⟩]
  apply inner_pos_of_norm_sub_lt_one (norm_eq_of_mem_sphere _) (norm_eq_of_mem_sphere _)
  have key := @hεu s ⟨_, hin⟩ ?_
  · rwa [dist_eq_norm] at key
  · rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
    have h1 : (s : ℝ) - (i : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 / ((m : ℝ) + 1) := by
      have : ((i : ℝ) + 1) / ((m + 1 : ℕ) : ℝ) - (i : ℝ) / ((m + 1 : ℕ) : ℝ)
          = 1 / ((m : ℝ) + 1) := by
        rw [← sub_div, add_sub_cancel_left, Nat.cast_succ]
      linarith
    constructor <;> linarith

theorem exists_homotopic_piecewise_geodesic {x : sphere (0 : E) 1} (γ : Path x x) :
    ∃ (n : ℕ) (p : ℕ → E) (δ : Path x x), γ.Homotopic δ ∧
      ∀ s : I, ∃ i < n, (δ s : E) ∈ Submodule.span ℝ {p i, p (i + 1)} := by
  obtain ⟨n, hn, hsub⟩ := exists_subdivision γ
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set p : ℕ → E := fun j => (γ.extend ((j : ℝ) / n) : E) with hp
  have hp_norm : ∀ j, ‖p j‖ = 1 := fun j => norm_eq_of_mem_sphere _
  have hp0 : p 0 = x := by simp [hp]
  have hpn : p n = x := by simp [hp, div_self hn'.ne']
  have hpos : ∀ (t : I) (s : I),
      ∃ i < n, 0 < inner ℝ ((1 - (t : ℝ)) • (γ s : E) + (t : ℝ) • polygon p n s) (p i) := by
    intro t s
    obtain ⟨i, hi, hs, hs'⟩ := exists_piece hn s.2.1 s.2.2
    refine ⟨i, hi, ?_⟩
    have h1 : 0 < inner ℝ (γ s : E) (p i) := hsub i hi s hs hs'
    have h2 : 0 < inner ℝ (polygon p n s) (p i) := by
      apply inner_polygon_pos p hi hs hs'
      · rw [real_inner_self_eq_norm_sq, hp_norm]
        norm_num
      · have hmem : ((i : ℝ) + 1) / n ∈ I := by
          refine ⟨by positivity, ?_⟩
          rw [div_le_one hn']
          exact_mod_cast hi
        have h3 := hsub i hi ⟨_, hmem⟩
          (div_le_div_of_nonneg_right (by linarith) hn'.le) le_rfl
        convert h3 using 2
        simp only [hp, Nat.cast_add, Nat.cast_one]
        exact congrArg Subtype.val (Path.extend_extends' γ ⟨_, hmem⟩)
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    exact convex_pos h1 h2 t.2.1 t.2.2
  set w : I × I → E := fun ts => (1 - (ts.1 : ℝ)) • (γ ts.2 : E) + (ts.1 : ℝ) • polygon p n ts.2
    with hw_def
  have hw : ∀ ts, w ts ≠ 0 := fun ts h => by
    obtain ⟨i, -, hi⟩ := hpos ts.1 ts.2
    rw [show (1 - (ts.1 : ℝ)) • (γ ts.2 : E) + (ts.1 : ℝ) • polygon p n ts.2 = w ts from rfl, h,
      inner_zero_left] at hi
    exact lt_irrefl _ hi
  have hwc : Continuous w := by
    apply Continuous.add
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp (γ.continuous.comp continuous_snd))
    · exact (continuous_subtype_val.comp continuous_fst).smul
        ((continuous_polygon p n).comp (continuous_subtype_val.comp continuous_snd))
  have hw0 : ∀ s : I, w (0, s) = (γ s : E) := fun s => by simp [hw_def]
  have hw1 : ∀ s : I, w (1, s) = polygon p n s := fun s => by simp [hw_def]
  have hwt0 : ∀ t : I, w (t, 0) = (x : E) := fun t => by
    simp only [hw_def, Set.Icc.coe_zero, polygon_zero, hp0, Path.source]
    rw [← add_smul, sub_add_cancel, one_smul]
  have hwt1 : ∀ t : I, w (t, 1) = (x : E) := fun t => by
    simp only [hw_def, Set.Icc.coe_one, polygon_one, hpn, Path.target]
    rw [← add_smul, sub_add_cancel, one_smul]
  set H : I × I → E := fun ts => radialProj (w ts) with hH_def
  have hH1 : ∀ ts, ‖H ts‖ = 1 := fun ts => norm_radialProj (hw ts)
  have hHc : Continuous H := continuous_radialProj_comp hwc hw
  have hHx : ‖(x : E)‖ = 1 := norm_eq_of_mem_sphere x
  have hHt0 : ∀ t : I, H (t, 0) = (x : E) := fun t => by
    change radialProj (w (t, 0)) = (x : E)
    rw [hwt0, radialProj_of_norm_eq_one hHx]
  have hHt1 : ∀ t : I, H (t, 1) = (x : E) := fun t => by
    change radialProj (w (t, 1)) = (x : E)
    rw [hwt1, radialProj_of_norm_eq_one hHx]
  have hH0 : ∀ s : I, H (0, s) = (γ s : E) := fun s => by
    change radialProj (w (0, s)) = (γ s : E)
    rw [hw0, radialProj_of_norm_eq_one (norm_eq_of_mem_sphere (γ s))]
  let δ : Path x x :=
    { toFun := fun s => ⟨H (1, s), mem_sphere_zero_iff_norm.2 (hH1 _)⟩
      continuous_toFun := (hHc.comp (continuous_const.prodMk continuous_id)).subtype_mk _
      source' := Subtype.ext (hHt0 1)
      target' := Subtype.ext (hHt1 1) }
  refine ⟨n, p, δ, ⟨?_⟩, ?_⟩
  · exact
      { toFun := fun ts => ⟨H ts, mem_sphere_zero_iff_norm.2 (hH1 ts)⟩
        continuous_toFun := hHc.subtype_mk _
        map_zero_left := fun s => Subtype.ext (hH0 s)
        map_one_left := fun s => rfl
        prop' := fun t s hs => by
          rcases hs with rfl | rfl
          · exact Subtype.ext ((hHt0 t).trans (congrArg Subtype.val γ.source.symm))
          · exact Subtype.ext ((hHt1 t).trans (congrArg Subtype.val γ.target.symm)) }
  · intro s
    obtain ⟨i, hi, hs, hs'⟩ := exists_piece hn s.2.1 s.2.2
    refine ⟨i, hi, ?_⟩
    change radialProj (w (1, s)) ∈ _
    rw [hw1]
    exact radialProj_mem_span (polygon_mem_span p hi hs hs')

end InnerProduct

section Avoid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem span_pair_ne_top (h3 : 3 ≤ finrank ℝ E) (a b : E) : Submodule.span ℝ {a, b} ≠ ⊤ := by
  intro htop
  have h1 : finrank ℝ (Submodule.span ℝ ({a, b} : Set E)) ≤ 2 := by
    classical
    refine (finrank_span_le_card ({a, b} : Set E)).trans ?_
    simp only [Set.toFinset_insert, Set.toFinset_singleton]
    exact Finset.card_le_two
  rw [htop, finrank_top] at h1
  omega

variable [FiniteDimensional ℝ E]

theorem interior_biUnion_span_pair_eq_empty (h3 : 3 ≤ finrank ℝ E) (p : ℕ → E) (n : ℕ) :
    interior (⋃ i ∈ Finset.range n, (Submodule.span ℝ {p i, p (i + 1)} : Set E)) = ∅ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert,
      interior_union_isClosed_of_interior_empty (Submodule.closed_of_finiteDimensional _) ih]
    by_contra h
    exact span_pair_ne_top h3 (p n) (p (n + 1))
      ((Submodule.span ℝ _).eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.2 h))

theorem exists_notMem_span_pair (h3 : 3 ≤ finrank ℝ E) (p : ℕ → E) (n : ℕ) :
    ∃ q : E, ∀ i < n, q ∉ Submodule.span ℝ {p i, p (i + 1)} := by
  by_contra hcon
  push Not at hcon
  have huniv : (⋃ i ∈ Finset.range n, (Submodule.span ℝ {p i, p (i + 1)} : Set E)) = univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨i, hi, hq⟩ := hcon q
    exact Set.mem_biUnion (Finset.mem_range.2 hi) hq
  have h := interior_biUnion_span_pair_eq_empty h3 p n
  rw [huniv, interior_univ] at h
  exact (Set.nonempty_iff_ne_empty.1 ⟨0, Set.mem_univ 0⟩) h

theorem exists_sphere_notMem_span_pair (h3 : 3 ≤ finrank ℝ E) (p : ℕ → E) (n : ℕ) :
    ∃ q : sphere (0 : E) 1, ∀ i < n, (q : E) ∉ Submodule.span ℝ {p i, p (i + 1)} := by
  obtain ⟨q₀, hq₀⟩ := exists_notMem_span_pair h3 p (n + 1)
  have hne : q₀ ≠ 0 := fun h => hq₀ 0 (Nat.succ_pos n) (h ▸ Submodule.zero_mem _)
  refine ⟨⟨radialProj q₀, radialProj_mem_sphere hne⟩, fun i hi h => ?_⟩
  exact hq₀ i (Nat.lt_succ_of_lt hi) (mem_span_of_radialProj_mem hne h)

end Avoid

def sphereComplSingletonHomeomorph {k : ℕ}
    (q : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)) ≃ₜ EuclideanSpace ℝ (Fin k) :=
  haveI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = k + 1) := ⟨finrank_euclideanSpace_fin⟩
  ((Homeomorph.setCongr (stereographic'_source q).symm).trans
    (stereographic' k q).toHomeomorphSourceTarget).trans
    ((Homeomorph.setCongr (stereographic'_target q)).trans (Homeomorph.Set.univ _))

theorem contractibleSpace_sphere_compl_singleton {k : ℕ}
    (q : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    ContractibleSpace ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)) :=
  (sphereComplSingletonHomeomorph q).contractibleSpace

theorem isSimplyConnected_sphere_compl_singleton {k : ℕ}
    (q : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    IsSimplyConnected ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)) := by
  have := contractibleSpace_sphere_compl_singleton q
  exact SimplyConnectedSpace.ofContractible _

theorem simplyConnectedSpace_sphere_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨?_, fun x γ => ?_⟩
  · rw [← isPathConnected_iff_pathConnectedSpace]
    refine isPathConnected_sphere ?_ 0 zero_le_one
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < k + 1)
  · obtain ⟨n, p, δ, hγδ, hδ⟩ := exists_homotopic_piecewise_geodesic γ
    have h3 : 3 ≤ finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) := by
      rw [finrank_euclideanSpace_fin]
      omega
    obtain ⟨q, hq⟩ := exists_sphere_notMem_span_pair h3 p n
    have hδq : ∀ s, δ s ∈ ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)) := by
      intro s hs
      obtain ⟨i, hi, hmem⟩ := hδ s
      rw [Set.mem_singleton_iff] at hs
      rw [hs] at hmem
      exact hq i hi hmem
    obtain ⟨F, -⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp
      (isSimplyConnected_sphere_compl_singleton q)).2 x δ hδq
    exact hγδ.trans ⟨F⟩

end

end DifferentialGeometry.Topology
