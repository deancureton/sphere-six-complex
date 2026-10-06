module

public import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.Variational.LinearMapSmoothness
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section


noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

section ShortIntervalExistence

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem exists_linearODE_solution_of_short
    {A : ℝ → (G →L[ℝ] G)} {h₀ : ℝ} {T M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn A (Icc (h₀ - T) (h₀ + T)))
    (hA_bd : ∀ t ∈ Icc (h₀ - T) (h₀ + T), ‖A t‖ ≤ M)
    (Z₀ : G) :
    ∃ Z : ℝ → G, Z h₀ = Z₀ ∧
      ∀ t ∈ Icc (h₀ - T) (h₀ + T), HasDerivWithinAt Z (A t (Z t))
        (Icc (h₀ - T) (h₀ + T)) t := by
  set v : ℝ → G → G := fun t y => A t y with hv_def
  set r₀ : ℝ := ‖Z₀‖ with hr₀_def
  have hr₀_nn : 0 ≤ r₀ := norm_nonneg _
  have h1mMT_pos : 0 < 1 - M * T := by linarith
  set a₀ : ℝ := (r₀ + 1) / (1 - M * T) with ha₀_def
  have ha₀_pos : 0 < a₀ := div_pos (by linarith [hr₀_nn]) h1mMT_pos
  have ha₀_nn : 0 ≤ a₀ := le_of_lt ha₀_pos
  have hMaT_le : M * a₀ * T ≤ a₀ - r₀ := by
    have hkey : a₀ * (1 - M * T) = r₀ + 1 := by
      rw [ha₀_def]; field_simp
    have h1 : a₀ - M * a₀ * T = r₀ + 1 := by
      have : a₀ - M * a₀ * T = a₀ * (1 - M * T) := by ring
      rw [this, hkey]
    linarith
  let tmin : ℝ := h₀ - T
  let tmax : ℝ := h₀ + T
  have htmin_le_t₀ : tmin ≤ h₀ := by change h₀ - T ≤ h₀; linarith
  have ht₀_le_tmax : h₀ ≤ tmax := by change h₀ ≤ h₀ + T; linarith
  let t₀Icc : Icc tmin tmax := ⟨h₀, ⟨htmin_le_t₀, ht₀_le_tmax⟩⟩
  let aN : ℝ≥0 := NNReal.mk a₀ ha₀_nn
  let rN : ℝ≥0 := NNReal.mk r₀ hr₀_nn
  let LN : ℝ≥0 := NNReal.mk (M * a₀) (mul_nonneg hM ha₀_nn)
  let KN : ℝ≥0 := NNReal.mk M hM
  have hpl : IsPicardLindelof v t₀Icc (0 : G) aN rN LN KN := by
    refine
    { lipschitzOnWith := ?_,
      continuousOn := ?_,
      norm_le := ?_,
      mul_max_le := ?_ }
    · intro t ht
      have hAτ_bd : ‖A t‖ ≤ M := hA_bd t ht
      have hlip : LipschitzWith KN (A t) := (A t).lipschitzWith_of_opNorm_le hAτ_bd
      exact hlip.lipschitzOnWith (s := closedBall (0 : G) aN)
    · intro y _
      have happly : Continuous (fun B : G →L[ℝ] G => B y) :=
        (ContinuousLinearMap.apply ℝ G y).continuous
      exact happly.comp_continuousOn hA_cont
    · intro t ht y hy
      have hAt_bd : ‖A t‖ ≤ M := hA_bd t ht
      have hy_norm : ‖y‖ ≤ a₀ := by
        have hy' : ‖y‖ ≤ (aN : ℝ) := by
          simpa only [mem_closedBall_zero_iff] using hy
        simpa only [aN, NNReal.coe_mk] using hy'
      change ‖v t y‖ ≤ (LN : ℝ)
      calc ‖v t y‖ = ‖A t y‖ := rfl
        _ ≤ ‖A t‖ * ‖y‖ := (A t).le_opNorm y
        _ ≤ M * a₀ := mul_le_mul hAt_bd hy_norm (norm_nonneg _) hM
    · change (LN : ℝ) * max (tmax - h₀) (h₀ - tmin) ≤ (aN : ℝ) - (rN : ℝ)
      have hmax_eq : max (tmax - h₀) (h₀ - tmin) = T := by
        have h1 : tmax - h₀ = T := by change (h₀ + T) - h₀ = T; ring
        have h2 : h₀ - tmin = T := by change h₀ - (h₀ - T) = T; ring
        rw [h1, h2]; exact max_self _
      rw [hmax_eq]
      change M * a₀ * T ≤ a₀ - r₀
      exact hMaT_le
  have hZ₀_mem : Z₀ ∈ closedBall (0 : G) rN := by
    rw [mem_closedBall_zero_iff]; change ‖Z₀‖ ≤ r₀; rfl
  obtain ⟨Z, hZ_initial, hZ_deriv⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt hZ₀_mem
  exact ⟨Z, hZ_initial, hZ_deriv⟩

end ShortIntervalExistence

section Uniqueness

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem linearODE_unique_on_Ioo
    {A : ℝ → (G →L[ℝ] G)} {a b h₀ : ℝ}
    (ht₀ : h₀ ∈ Ioo a b)
    (hA_cont : ContinuousOn A (Ioo a b))
    {Z₁ Z₂ : ℝ → G}
    (hZ₁ : ∀ t ∈ Ioo a b, HasDerivAt Z₁ (A t (Z₁ t)) t)
    (hZ₂ : ∀ t ∈ Ioo a b, HasDerivAt Z₂ (A t (Z₂ t)) t)
    (heq : Z₁ h₀ = Z₂ h₀) :
    EqOn Z₁ Z₂ (Ioo a b) := by
  intro t ht
  let v : ℝ → G → G := fun t y => A t y
  set a' := (a + min t h₀) / 2 with ha'
  set b' := (b + max t h₀) / 2 with hb'
  have hmin_lt : a < min t h₀ := lt_min ht.1 ht₀.1
  have hmax_lt : max t h₀ < b := max_lt ht.2 ht₀.2
  have hmin_le_t : min t h₀ ≤ t := min_le_left _ _
  have hmin_le_t₀ : min t h₀ ≤ h₀ := min_le_right _ _
  have ht_le_max : t ≤ max t h₀ := le_max_left _ _
  have ht₀_le_max : h₀ ≤ max t h₀ := le_max_right _ _
  have ha'_lt_min : a' < min t h₀ := by rw [ha']; linarith
  have ha_lt_a' : a < a' := by rw [ha']; linarith
  have hmax_lt_b' : max t h₀ < b' := by rw [hb']; linarith
  have hb'_lt_b : b' < b := by rw [hb']; linarith
  have hsub : Ioo a' b' ⊆ Ioo a b := fun s hs =>
    ⟨lt_trans ha_lt_a' hs.1, lt_trans hs.2 hb'_lt_b⟩
  have ht_mem' : t ∈ Ioo a' b' :=
    ⟨lt_of_lt_of_le ha'_lt_min hmin_le_t, lt_of_le_of_lt ht_le_max hmax_lt_b'⟩
  have ht₀_mem' : h₀ ∈ Ioo a' b' :=
    ⟨lt_of_lt_of_le ha'_lt_min hmin_le_t₀, lt_of_le_of_lt ht₀_le_max hmax_lt_b'⟩
  have hab_le : a' ≤ b' := le_of_lt (lt_trans ha'_lt_min (lt_of_le_of_lt hmin_le_t
    (lt_of_lt_of_le ht_mem'.2 (le_refl _))))
  have hIcc_sub : Icc a' b' ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le ha_lt_a' hs.1, lt_of_le_of_lt hs.2 hb'_lt_b⟩
  have hbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Icc a' b', ‖A τ‖ ≤ M := by
    have hcont' : ContinuousOn A (Icc a' b') := hA_cont.mono hIcc_sub
    have hcont_norm : ContinuousOn (fun τ => ‖A τ‖) (Icc a' b') :=
      continuous_norm.comp_continuousOn hcont'
    have hcpt : IsCompact (Icc a' b') := isCompact_Icc
    have hne : (Icc a' b').Nonempty := ⟨a', left_mem_Icc.mpr hab_le⟩
    rcases hcpt.exists_isMaxOn hne hcont_norm with ⟨τ₁, _, hτ₁_max⟩
    exact ⟨‖A τ₁‖, norm_nonneg _, fun τ hτ => hτ₁_max hτ⟩
  obtain ⟨M, hM_nn, hMbd⟩ := hbd
  let K : ℝ≥0 := ⟨M, hM_nn⟩
  have hv_lip : ∀ τ ∈ Ioo a' b', LipschitzOnWith K (v τ) univ := by
    intro τ hτ
    have hlip : LipschitzWith K (A τ) :=
      (A τ).lipschitzWith_of_opNorm_le (hMbd τ (Ioo_subset_Icc_self hτ))
    exact (LipschitzWith.lipschitzOnWith (s := (univ : Set G)) hlip)
  exact (ODE_solution_unique_of_mem_Ioo (v := v) (s := fun _ => univ) (K := K)
    hv_lip ht₀_mem'
    (fun τ hτ => ⟨hZ₁ τ (hsub hτ), mem_univ _⟩)
    (fun τ hτ => ⟨hZ₂ τ (hsub hτ), mem_univ _⟩)
    heq) ht_mem'

end Uniqueness

section InvariantRange

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem _root_.ContinuousLinearMap.range_eq_on_Ioo_of_hasDerivAt_eq_comp
    {W : ℝ → F →L[ℝ] G} {C : ℝ → F →L[ℝ] F} {a b : ℝ}
    (hC : ContinuousOn C (Ioo a b))
    (hW : ∀ t ∈ Ioo a b, HasDerivAt W ((W t).comp (C t)) t)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    (W s).range = (W t).range := by
  have hle : ∀ {u v : ℝ}, u ∈ Ioo a b → v ∈ Ioo a b →
      (W v).range ≤ (W u).range := by
    intro u v hu hv y hy
    let S : Submodule ℝ G := (W u).range
    let _ : FiniteDimensional ℝ S := by
      dsimp [S]
      infer_instance
    let _ : IsClosed (S : Set G) := Submodule.closed_of_finiteDimensional S
    let Q : G →L[ℝ] G ⧸ S := S.mkQL
    let Z : ℝ → F →L[ℝ] G ⧸ S := fun τ => Q.comp (W τ)
    let R : ℝ → (F →L[ℝ] G ⧸ S) →L[ℝ] F →L[ℝ] G ⧸ S :=
      fun τ => (ContinuousLinearMap.compL ℝ F F (G ⧸ S)).flip (C τ)
    have hR : ContinuousOn R (Ioo a b) :=
      (ContinuousLinearMap.compL ℝ F F (G ⧸ S)).flip.continuous.comp_continuousOn hC
    have hZ : ∀ τ ∈ Ioo a b, HasDerivAt Z (R τ (Z τ)) τ := by
      intro τ hτ
      have h := (hasDerivAt_const (τ) Q).clm_comp (hW τ hτ)
      simpa [Z, R, ContinuousLinearMap.comp_assoc] using h
    have hzero : ∀ τ ∈ Ioo a b,
        HasDerivAt (fun _ : ℝ => (0 : F →L[ℝ] G ⧸ S))
          (R τ ((fun _ : ℝ => (0 : F →L[ℝ] G ⧸ S)) τ)) τ := by
      intro τ hτ
      simpa using (hasDerivAt_const (τ) (0 : F →L[ℝ] G ⧸ S))
    have hinit : Z u = 0 := by
      ext x
      exact (Submodule.Quotient.mk_eq_zero S).mpr ⟨x, rfl⟩
    have huniq := linearODE_unique_on_Ioo hu hR hZ hzero hinit
    rcases hy with ⟨x, rfl⟩
    have hz := congrArg (fun L : F →L[ℝ] G ⧸ S => L x) (huniq hv)
    exact (Submodule.Quotient.mk_eq_zero S).mp (by simpa [Z, Q] using hz)
  exact le_antisymm (hle ht hs) (hle hs ht)

theorem _root_.ContinuousLinearMap.range_eq_on_Ioo_of_hasDerivAt_of_injective_of_deriv_range_le
    [FiniteDimensional ℝ G]
    {W D : ℝ → F →L[ℝ] G} {a b : ℝ}
    (hD : ContinuousOn D (Ioo a b))
    (hW : ∀ t ∈ Ioo a b, HasDerivAt W (D t) t)
    (hinj : ∀ t ∈ Ioo a b, Injective (W t))
    (hrange : ∀ t ∈ Ioo a b, (D t).range ≤ (W t).range)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    (W s).range = (W t).range := by
  have hlocal : IsLocallyConstant (fun u : Ioo a b => (W u).range) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro u
    let hleft :=
      ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional (hinj u u.property)
    let L : G →L[ℝ] F := hleft.leftInverse
    let B : ℝ → F →L[ℝ] F := fun τ => L.comp (W τ)
    have hBu : B u = 1 := by
      ext x
      exact hleft.leftInverse_leftInverse x
    have hB_cont : ContinuousAt B u := by
      have hcomp : ContinuousAt (fun T : F →L[ℝ] G => L.comp T) (W u) :=
        ((ContinuousLinearMap.compL ℝ F G F) L).continuous.continuousAt
      change ContinuousAt ((fun T : F →L[ℝ] G => L.comp T) ∘ W) (u : ℝ)
      exact hcomp.comp (hW u u.property).continuousAt
    have hunit_nhds : {τ : ℝ | IsUnit (B τ)} ∈ 𝓝 (u : ℝ) := by
      change B ⁻¹' {T : F →L[ℝ] F | IsUnit T} ∈ 𝓝 (u : ℝ)
      apply hB_cont.preimage_mem_nhds
      rw [hBu]
      exact Units.isOpen.mem_nhds isUnit_one
    have hgood : {τ : ℝ | IsUnit (B τ)} ∩ Ioo a b ∈ 𝓝 (u : ℝ) :=
      inter_mem hunit_nhds (isOpen_Ioo.mem_nhds u.property)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
    have hinterval : Ioo ((u : ℝ) - ε) ((u : ℝ) + ε) ⊆
        {τ : ℝ | IsUnit (B τ)} ∩ Ioo a b := by
      simpa only [← Real.ball_eq_Ioo] using hball
    let C : ℝ → F →L[ℝ] F := fun τ =>
      Ring.inverse (B τ) * L.comp (D τ)
    have hC : ContinuousOn C (Ioo ((u : ℝ) - ε) ((u : ℝ) + ε)) := by
      intro τ hτ
      have hτgood := hinterval hτ
      have hBτ_cont : ContinuousAt B τ := by
        have hcomp : ContinuousAt (fun T : F →L[ℝ] G => L.comp T) (W τ) :=
          ((ContinuousLinearMap.compL ℝ F G F) L).continuous.continuousAt
        change ContinuousAt ((fun T : F →L[ℝ] G => L.comp T) ∘ W) τ
        exact hcomp.comp (hW τ hτgood.2).continuousAt
      have hinv_cont : ContinuousAt Ring.inverse (B τ) := by
        simpa only [hτgood.1.unit_spec] using
          (NormedRing.inverse_continuousAt hτgood.1.unit)
      have hLD_cont : ContinuousAt (fun q => L.comp (D q)) τ := by
        have hcomp : ContinuousAt (fun T : F →L[ℝ] G => L.comp T) (D τ) :=
          ((ContinuousLinearMap.compL ℝ F G F) L).continuous.continuousAt
        exact hcomp.comp (hD.continuousAt (isOpen_Ioo.mem_nhds hτgood.2))
      exact ((hinv_cont.comp hBτ_cont).mul hLD_cont).continuousWithinAt
    have hfactor : ∀ τ ∈ Ioo ((u : ℝ) - ε) ((u : ℝ) + ε),
        (W τ).comp (C τ) = D τ := by
      intro τ hτ
      have hτgood := hinterval hτ
      ext y
      obtain ⟨x, hx⟩ := hrange τ hτgood.2 ⟨y, rfl⟩
      have hcancel : Ring.inverse (B τ) (B τ x) = x := by
        have h := congrArg (fun T : F →L[ℝ] F => T x)
          (Ring.inverse_mul_cancel (B τ) hτgood.1)
        simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
      have hLD : L (D τ y) = B τ x := by
        calc
          L (D τ y) = L (W τ x) := congrArg L hx.symm
          _ = B τ x := rfl
      calc
        (W τ).comp (C τ) y = W τ (Ring.inverse (B τ) (L (D τ y))) := by
          rfl
        _ = W τ (Ring.inverse (B τ) (B τ x)) := by rw [hLD]
        _ = W τ x := by rw [hcancel]
        _ = D τ y := hx
    have hW_local : ∀ τ ∈ Ioo ((u : ℝ) - ε) ((u : ℝ) + ε),
        HasDerivAt W ((W τ).comp (C τ)) τ := by
      intro τ hτ
      rw [hfactor τ hτ]
      exact hW τ (hinterval hτ).2
    have hu_local : (u : ℝ) ∈ Ioo ((u : ℝ) - ε) ((u : ℝ) + ε) := by
      constructor <;> linarith
    have hlocal_nhds : Subtype.val ⁻¹'
        Ioo ((u : ℝ) - ε) ((u : ℝ) + ε) ∈ 𝓝 u :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds hu_local)
    filter_upwards [hlocal_nhds] with v hv
    exact ContinuousLinearMap.range_eq_on_Ioo_of_hasDerivAt_eq_comp hC hW_local hv hu_local
  let hpre : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  exact hlocal.apply_eq_of_isPreconnected (@isPreconnected_univ _ _ hpre)
    (x := ⟨s, hs⟩) (y := ⟨t, ht⟩) trivial trivial

theorem _root_.Submodule.span_range_eq_on_Ioo_of_hasDerivAt_of_linearIndependent_of_deriv_mem
    {ι : Type*} [Finite ι] [FiniteDimensional ℝ G]
    {w w' : ι → ℝ → G} {a b : ℝ}
    (hw' : ∀ i, ContinuousOn (w' i) (Ioo a b))
    (hw : ∀ i t, t ∈ Ioo a b → HasDerivAt (w i) (w' i t) t)
    (hli : ∀ t ∈ Ioo a b, LinearIndependent ℝ (fun i => w i t))
    (hmem : ∀ i t, t ∈ Ioo a b →
      w' i t ∈ Submodule.span ℝ (Set.range fun j => w j t))
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    Submodule.span ℝ (Set.range fun i => w i s) =
      Submodule.span ℝ (Set.range fun i => w i t) := by
  let _ := Fintype.ofFinite ι
  let term : ι → G →L[ℝ] ((ι → ℝ) →L[ℝ] G) := fun i =>
    (ContinuousLinearMap.smulRightL ℝ (ι → ℝ) G) (ContinuousLinearMap.proj i)
  let W : ℝ → (ι → ℝ) →L[ℝ] G := fun τ => ∑ i, term i (w i τ)
  let D : ℝ → (ι → ℝ) →L[ℝ] G := fun τ => ∑ i, term i (w' i τ)
  have hD : ContinuousOn D (Ioo a b) := by
    apply continuousOn_finsetSum
    intro i hi
    exact (term i).continuous.comp_continuousOn (hw' i)
  have hW : ∀ τ ∈ Ioo a b, HasDerivAt W (D τ) τ := by
    intro τ hτ
    have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ => by
      have hi := (term i).hasFDerivAt.comp_hasDerivAt τ (hw i τ hτ)
      simpa only [Function.comp_apply] using hi)
    change HasDerivAt (fun q => ∑ i, term i (w i q)) (∑ i, term i (w' i τ)) τ
    have hfun : (∑ i, (term i : G → ((ι → ℝ) →L[ℝ] G)) ∘ w i) =
        fun q => ∑ i, term i (w i q) := by
      funext q
      simp only [Finset.sum_apply, Function.comp_apply]
    rw [← hfun]
    exact hsum
  have hW_apply (τ : ℝ) (c : ι → ℝ) :
      W τ c = ∑ i, c i • w i τ := by
    simp [W, term]
  have hD_apply (τ : ℝ) (c : ι → ℝ) :
      D τ c = ∑ i, c i • w' i τ := by
    simp [D, term]
  have hinj : ∀ τ ∈ Ioo a b, Injective (W τ) := by
    intro τ hτ c d hcd
    apply sub_eq_zero.mp
    apply funext
    intro i
    have hsum : ∑ j, (c - d) j • w j τ = 0 := by
      calc
        ∑ j, (c - d) j • w j τ = W τ (c - d) := (hW_apply τ (c - d)).symm
        _ = W τ c - W τ d := map_sub (W τ) c d
        _ = 0 := sub_eq_zero.mpr hcd
    exact (Fintype.linearIndependent_iff.mp (hli τ hτ)) (c - d) hsum i
  have hW_range (τ : ℝ) :
      (W τ).range = Submodule.span ℝ (Set.range fun i => w i τ) := by
    rw [← Fintype.range_linearCombination]
    congr 1
    ext c
    exact hW_apply τ c
  have hD_range (τ : ℝ) :
      (D τ).range = Submodule.span ℝ (Set.range fun i => w' i τ) := by
    rw [← Fintype.range_linearCombination]
    congr 1
    ext c
    exact hD_apply τ c
  have hrange : ∀ τ ∈ Ioo a b, (D τ).range ≤ (W τ).range := by
    intro τ hτ
    rw [hD_range, hW_range, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i τ hτ
  rw [← hW_range s, ← hW_range t]
  exact ContinuousLinearMap.range_eq_on_Ioo_of_hasDerivAt_of_injective_of_deriv_range_le
    hD hW hinj hrange hs ht

theorem _root_.ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_frame_ode
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {A : ℝ → H →L[ℝ] H} {W : ℝ → F →L[ℝ] H}
    {C : ℝ → F →L[ℝ] F} {a b : ℝ}
    (hC : ContinuousOn C (Ioo a b))
    (hW : ∀ t ∈ Ioo a b, HasDerivAt W ((W t).comp (C t)) t)
    (hker : ∀ t ∈ Ioo a b, (W t).range = (A t).ker)
    (hsymm : ∀ t ∈ Ioo a b, (A t).toLinearMap.IsSymmetric)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    (A s).ker = (A t).ker ∧ (A s).range = (A t).range := by
  have hframe : (W s).range = (W t).range :=
    ContinuousLinearMap.range_eq_on_Ioo_of_hasDerivAt_eq_comp hC hW hs ht
  have hkernel : (A s).ker = (A t).ker := by
    rw [← hker s hs, ← hker t ht]
    exact hframe
  refine ⟨hkernel, ?_⟩
  have horth : (A s).rangeᗮ = (A t).rangeᗮ := by
    rw [(hsymm s hs).orthogonal_range, (hsymm t ht).orthogonal_range]
    exact hkernel
  have horthorth := congrArg (fun K : Submodule ℝ H => Kᗮ) horth
  simpa using horthorth

theorem _root_.ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_frame_deriv_range
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {A : ℝ → H →L[ℝ] H} {W D : ℝ → F →L[ℝ] H} {a b : ℝ}
    (hD : ContinuousOn D (Ioo a b))
    (hW : ∀ t ∈ Ioo a b, HasDerivAt W (D t) t)
    (hinj : ∀ t ∈ Ioo a b, Injective (W t))
    (hderiv : ∀ t ∈ Ioo a b, (D t).range ≤ (W t).range)
    (hker : ∀ t ∈ Ioo a b, (W t).range = (A t).ker)
    (hsymm : ∀ t ∈ Ioo a b, (A t).toLinearMap.IsSymmetric)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    (A s).ker = (A t).ker ∧ (A s).range = (A t).range := by
  have hframe : (W s).range = (W t).range :=
    ContinuousLinearMap.range_eq_on_Ioo_of_hasDerivAt_of_injective_of_deriv_range_le
      hD hW hinj hderiv hs ht
  have hkernel : (A s).ker = (A t).ker := by
    rw [← hker s hs, ← hker t ht]
    exact hframe
  refine ⟨hkernel, ?_⟩
  have horth : (A s).rangeᗮ = (A t).rangeᗮ := by
    rw [(hsymm s hs).orthogonal_range, (hsymm t ht).orthogonal_range]
    exact hkernel
  have horthorth := congrArg (fun K : Submodule ℝ H => Kᗮ) horth
  simpa using horthorth

theorem _root_.ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_kernel_frame_deriv_annihilation
    {ι H : Type*} [Finite ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    {A A' : ℝ → H →L[ℝ] H} {w w' : ι → ℝ → H} {a b : ℝ}
    (hw' : ∀ i, ContinuousOn (w' i) (Ioo a b))
    (hA : ∀ t ∈ Ioo a b, HasDerivAt A (A' t) t)
    (hw : ∀ i t, t ∈ Ioo a b → HasDerivAt (w i) (w' i t) t)
    (hli : ∀ t ∈ Ioo a b, LinearIndependent ℝ (fun i => w i t))
    (hker : ∀ t ∈ Ioo a b,
      Submodule.span ℝ (Set.range fun i => w i t) = (A t).ker)
    (hann : ∀ t ∈ Ioo a b, ∀ v, v ∈ (A t).ker → A' t v = 0)
    (hsymm : ∀ t ∈ Ioo a b, (A t).toLinearMap.IsSymmetric)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    (A s).ker = (A t).ker ∧ (A s).range = (A t).range := by
  have hderiv_mem : ∀ i τ, τ ∈ Ioo a b →
      w' i τ ∈ Submodule.span ℝ (Set.range fun j => w j τ) := by
    intro i τ hτ
    have hwi : w i τ ∈ (A τ).ker := by
      rw [← hker τ hτ]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hprod := (hA τ hτ).clm_apply (hw i τ hτ)
    have hevent : (fun q => A q (w i q)) =ᶠ[𝓝 τ]
        (fun _ => (0 : H)) := by
      filter_upwards [isOpen_Ioo.eventually_mem hτ] with q hq
      apply LinearMap.mem_ker.mp
      rw [← hker q hq]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hzero : HasDerivAt (fun q => A q (w i q)) 0 τ :=
      (hasDerivAt_const τ (0 : H)).congr_of_eventuallyEq hevent
    have hsum : A' τ (w i τ) + A τ (w' i τ) = 0 := hprod.unique hzero
    rw [hann τ hτ (w i τ) hwi, zero_add] at hsum
    rw [hker τ hτ]
    exact LinearMap.mem_ker.mpr hsum
  have hkernel : (A s).ker = (A t).ker := by
    rw [← hker s hs, ← hker t ht]
    exact Submodule.span_range_eq_on_Ioo_of_hasDerivAt_of_linearIndependent_of_deriv_mem
      hw' hw hli hderiv_mem hs ht
  refine ⟨hkernel, ?_⟩
  have horth : (A s).rangeᗮ = (A t).rangeᗮ := by
    rw [(hsymm s hs).orthogonal_range, (hsymm t ht).orthogonal_range]
    exact hkernel
  have horthorth := congrArg (fun K : Submodule ℝ H => Kᗮ) horth
  simpa using horthorth

theorem _root_.ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_contDiffOn_kernel_frame_deriv_annihilation
    {ι H : Type*} [Finite ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    {A : ℝ → H →L[ℝ] H} {w : ι → ℝ → H} {a b : ℝ}
    (hA : ContDiffOn ℝ 1 A (Ioo a b))
    (hw : ∀ i, ContDiffOn ℝ 1 (w i) (Ioo a b))
    (hli : ∀ t ∈ Ioo a b, LinearIndependent ℝ (fun i => w i t))
    (hker : ∀ t ∈ Ioo a b,
      Submodule.span ℝ (Set.range fun i => w i t) = (A t).ker)
    (hann : ∀ t ∈ Ioo a b, ∀ v, v ∈ (A t).ker → deriv A t v = 0)
    (hsymm : ∀ t ∈ Ioo a b, (A t).toLinearMap.IsSymmetric)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    (A s).ker = (A t).ker ∧ (A s).range = (A t).range := by
  apply ContinuousLinearMap.ker_and_range_eq_on_Ioo_of_kernel_frame_deriv_annihilation
    (A' := deriv A) (w' := fun i => deriv (w i))
  · intro i
    exact (hw i).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  · intro τ hτ
    exact ((hA τ hτ).contDiffAt (isOpen_Ioo.mem_nhds hτ)).differentiableAt
      (by norm_num) |>.hasDerivAt
  · intro i τ hτ
    exact (((hw i) τ hτ).contDiffAt (isOpen_Ioo.mem_nhds hτ)).differentiableAt
      (by norm_num) |>.hasDerivAt
  · exact hli
  · exact hker
  · exact hann
  · exact hsymm
  · exact hs
  · exact ht

end InvariantRange

section SolutionOperator

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

def HasLinearODESolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G) (x : F) : Prop :=
  ∃ Z : ℝ → G, Z h₀ = Z₀ x ∧ ∀ t ∈ Ioo a b, HasDerivAt Z (A x t (Z t)) t

noncomputable def linearODESolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G) :
    F → ℝ → G := by
  classical
  exact fun x =>
    if h : HasLinearODESolution A a b h₀ Z₀ x then
      Classical.choose h
    else
      fun _ => Z₀ x

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace G] in
@[simp]
theorem linearODESolution_initial
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G) (x : F) :
    linearODESolution A a b h₀ Z₀ x h₀ = Z₀ x := by
  unfold linearODESolution
  by_cases h : HasLinearODESolution A a b h₀ Z₀ x
  · simp only [dite_eq_left h]
    exact (Classical.choose_spec h).1
  · simp only [dite_eq_right h]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace G] in
theorem linearODESolution_hasDerivAt_of_hasSolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G)
    {x : F} (hx : HasLinearODESolution A a b h₀ Z₀ x) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (linearODESolution A a b h₀ Z₀ x ·)
      (A x t (linearODESolution A a b h₀ Z₀ x t)) t := by
  have hZ_eq : linearODESolution A a b h₀ Z₀ x = Classical.choose hx := by
    unfold linearODESolution
    simp only [dite_eq_left hx]
  rw [hZ_eq]
  exact (Classical.choose_spec hx).2 t ht

end SolutionOperator

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
