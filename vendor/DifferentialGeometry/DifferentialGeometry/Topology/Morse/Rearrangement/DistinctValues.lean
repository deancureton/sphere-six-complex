module

public import DifferentialGeometry.Topology.Morse.Strip.Foundations.CriticalFinite
public import DifferentialGeometry.Topology.Morse.Rearrangement.MonotoneShift
public import Mathlib.Geometry.Manifold.Algebra.Structures

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H} [I.Boundaryless] [IsManifold I ∞ M]
  {f : M → ℝ} {a b : ℝ}

namespace DistinctValues

open MorseExistence

theorem isCriticalPointAt_add_const_iff {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) (c : ℝ) (x : M) :
    DifferentialGeometry.Topology.Morse.IsCriticalPointAt I (fun y => g y + c) x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
  have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hg' : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => g y + c) := hg.add contMDiff_const
  rw [isCriticalPointAt_iff_chart hg' hx, isCriticalPointAt_iff_chart hg hx]
  have : chartRep I (fun y => g y + c) x = fun y => chartRep I g x y + c := rfl
  rw [this, fderiv_add_const]

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem hessianAt_add_const (g : M → ℝ) (c : ℝ) (x : M) :
    hessianAt I (fun y => g y + c) x = hessianAt I g x :=
  MonotoneShift.chartHessianAt_add_const (fun y => g ((extChartAt I x).symm y)) _ c

theorem isNondegenerateCriticalPointAt_add_const_iff {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (c : ℝ) (x : M) :
    DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I (fun y => g y + c) x ↔ DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g x := by
  change (Morse.IsCriticalPointAt I (fun y => g y + c) x ∧
    (QuadraticMap.associated (R := ℝ) (hessianAt I (fun y => g y + c) x)).SeparatingLeft) ↔
    (Morse.IsCriticalPointAt I g x ∧
      (QuadraticMap.associated (R := ℝ) (hessianAt I g x)).SeparatingLeft)
  rw [isCriticalPointAt_add_const_iff hg, hessianAt_add_const]

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem morseIndex_add_const (g : M → ℝ) (c : ℝ) (x : M) :
    morseIndex I (fun y => g y + c) x = morseIndex I g x := by
  unfold morseIndex
  rw [hessianAt_add_const]

variable (I) in
def localShape (g g' : M → ℝ) (ε : ℝ) (x : M) : Prop :=
  (g' =ᶠ[𝓝 x] g) ∨ (g' =ᶠ[𝓝 x] fun y => g y + ε) ∨
    (¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ∧ ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g' x)

theorem localShape.isCriticalPointAt_iff {g g' : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) {ε : ℝ}
    {x : M} (h : localShape I g g' ε x) : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g' x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
  rcases h with h | h | h
  · exact MonotoneShift.isCriticalPointAt_congr_nhds h
  · exact (MonotoneShift.isCriticalPointAt_congr_nhds h).trans (isCriticalPointAt_add_const_iff hg ε x)
  · exact iff_of_false h.2 h.1

theorem localShape.isNondegenerateCriticalPointAt_iff {g g' : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) {ε : ℝ} {x : M} (h : localShape I g g' ε x) :
    DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g' x ↔ DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g x := by
  rcases h with h | h | h
  · exact MonotoneShift.isNondegenerateCriticalPointAt_congr_nhds h
  · exact (MonotoneShift.isNondegenerateCriticalPointAt_congr_nhds h).trans
      (isNondegenerateCriticalPointAt_add_const_iff hg ε x)
  · exact iff_of_false (fun hn => h.2 hn.1) (fun hn => h.1 hn.1)

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem localShape.morseIndex_eq {g g' : M → ℝ} {ε : ℝ} {x : M} (h : localShape I g g' ε x)
    (hc : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x) : morseIndex I g' x = morseIndex I g x := by
  rcases h with h | h | h
  · exact MonotoneShift.morseIndex_congr_nhds h
  · exact (MonotoneShift.morseIndex_congr_nhds h).trans (morseIndex_add_const g ε x)
  · exact absurd hc h.1

theorem morseStrip_of_localShape {g g' : M → ℝ} (hg : MorseStrip I g a b)
    (hg' : ContMDiff I 𝓘(ℝ, ℝ) ∞ g') (hmod : ModifiedWithin g a b g') {ε : ℝ}
    (hloc : ∀ x, localShape I g g' ε x) : MorseStrip I g' a b where
  smooth := hg'
  lt := hg.lt
  compact := by
    rw [hmod.preimage_Icc]
    exact hg.compact
  regular := by
    intro x hx hc
    have hx' : g x = a ∨ g x = b := by
      rcases hx with hx | hx
      · left
        have : x ∈ g' ⁻¹' {a} := hx
        rw [hmod.preimage_singleton_left] at this
        exact this
      · right
        have : x ∈ g' ⁻¹' {b} := hx
        rw [hmod.preimage_singleton_right] at this
        exact this
    exact hg.regular x hx' (((hloc x).isCriticalPointAt_iff hg.smooth).1 hc)
  nondegenerate := by
    intro x hx hc
    have hx' : g x ∈ Ioo a b := by
      have : x ∈ g' ⁻¹' Ioo a b := hx
      rwa [hmod.preimage_Ioo] at this
    exact ((hloc x).isNondegenerateCriticalPointAt_iff hg.smooth).2
      (hg.nondegenerate x hx' (((hloc x).isCriticalPointAt_iff hg.smooth).1 hc))

variable [T2Space M]

theorem exists_bump_shift (hf : MorseStrip I f a b) {p : M} (hp : f p ∈ Ioo a b)
    (hc : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, localShape I f g ε x) ∧ g p = f p + ε ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x ≠ p → g x = f x) := by
  obtain ⟨ρ, hρ, hρT, hρIoo, hρcrit⟩ := hf.exists_chartBall_no_other_critical hp hc
  set e := extChartAt I p with he
  have hfc : Continuous f := hf.smooth.continuous
  have hpS : p ∈ e.source := mem_extChartAt_source p
  obtain ⟨β, hbIn, hbOut⟩ : ∃ β : SmoothBumpFunction I p, β.rIn = ρ / 2 ∧ β.rOut = ρ :=
    ⟨{ rIn := ρ / 2, rOut := ρ, rIn_pos := by positivity, rIn_lt_rOut := by linarith,
       closedBall_subset := fun y hy => hρT hy.1 }, rfl, rfl⟩
  set K := e.symm '' Metric.closedBall (e p) ρ with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hρT)
  have hKIoo : ∀ x ∈ K, f x ∈ Ioo a b := by
    rintro x ⟨y, hy, rfl⟩
    exact hρIoo y hy
  have hKcrit : ∀ x ∈ K, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x = p := by
    rintro x ⟨y, hy, rfl⟩ hx
    rw [hρcrit y hy hx]
    exact e.left_inv hpS
  have htsupp : tsupport β ⊆ K := by
    refine β.tsupport_subset_symm_image_closedBall.trans ?_
    rw [hbOut]
    exact image_mono inter_subset_left
  have hsuppS : tsupport β ⊆ e.source := β.tsupport_subset_extChartAt_source
  obtain ⟨m, hm, hmK⟩ : ∃ m > 0, ∀ x ∈ K, a + m ≤ f x ∧ f x ≤ b - m := by
    have hne : K.Nonempty := ⟨p, e p, Metric.mem_closedBall_self hρ.le, e.left_inv hpS⟩
    obtain ⟨x₀, hx₀, hmin⟩ := hKc.exists_isMinOn hne hfc.continuousOn
    obtain ⟨x₁, hx₁, hmax⟩ := hKc.exists_isMaxOn hne hfc.continuousOn
    refine ⟨min (f x₀ - a) (b - f x₁),
      lt_min (sub_pos.2 (hKIoo x₀ hx₀).1) (sub_pos.2 (hKIoo x₁ hx₁).2), fun x hx => ⟨?_, ?_⟩⟩
    · have h1 : f x₀ ≤ f x := isMinOn_iff.1 hmin x hx
      have h2 : min (f x₀ - a) (b - f x₁) ≤ f x₀ - a := min_le_left _ _
      linarith
    · have h1 : f x ≤ f x₁ := isMaxOn_iff.1 hmax x hx
      have h2 : min (f x₀ - a) (b - f x₁) ≤ b - f x₁ := min_le_right _ _
      linarith
  set A := Metric.closedBall (e p) ρ \ Metric.ball (e p) (ρ / 2) with hA
  have hAc : IsCompact A := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hAT : A ⊆ e.target := fun y hy => hρT hy.1
  set F := chartRep I f p with hF
  have hFcont : ContinuousOn (fderiv ℝ F) e.target :=
    (contDiffOn_chartRep hf.smooth p).continuousOn_fderiv_of_isOpen
      (isOpen_extChartAt_target p) (by simp)
  have hAne : ∀ y ∈ A, fderiv ℝ F y ≠ 0 := by
    intro y hy h0
    have hyT := hAT hy
    have hxs : e.symm y ∈ e.source := e.map_target hyT
    have hcrit : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f (e.symm y) := by
      rw [isCriticalPointAt_iff_chart hf.smooth hxs, e.right_inv hyT]
      exact h0
    have := hρcrit y hy.1 hcrit
    apply hy.2
    rw [this, Metric.mem_ball, dist_self]
    positivity
  set B : (Fin n → ℝ) → ℝ := ⇑β.toContDiffBump with hB
  have hBcont : Continuous (fderiv ℝ B) :=
    (β.toContDiffBump.contDiff (n := 1)).continuous_fderiv (by simp)
  have hBd : Differentiable ℝ B := (β.toContDiffBump.contDiff (n := 1)).differentiable (by simp)
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ y ∈ A, fderiv ℝ F y + ε • fderiv ℝ B y ≠ 0 := by
    refine hAc.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ)) fun y hy => ?_
    have h1 : ContinuousAt (fun z : ℝ × (Fin n → ℝ) => fderiv ℝ F z.2 + z.1 • fderiv ℝ B z.2)
        (0, y) := by
      have hF' : ContinuousAt (fderiv ℝ F) y :=
        hFcont.continuousAt ((isOpen_extChartAt_target p).mem_nhds (hAT hy))
      exact (hF'.comp continuousAt_snd).add
        (continuousAt_fst.smul (hBcont.continuousAt.comp continuousAt_snd))
    have h2 : fderiv ℝ F y + (0 : ℝ) • fderiv ℝ B y ≠ 0 := by simpa using hAne y hy
    exact h1.eventually_ne h2
  filter_upwards [hev, eventually_abs_sub_lt (0 : ℝ) hm] with ε hε hεm
  rw [sub_zero] at hεm
  set g : M → ℝ := fun x => f x + ε * β x with hg
  have hgs : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hf.smooth.add (contMDiff_const.mul β.contMDiff)
  have hb0 : ∀ x, x ∉ tsupport β → g x = f x := fun x hx => by
    change f x + ε * β x = f x
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, add_zero]
  have hloc : ∀ x, localShape I f g ε x := by
    intro x
    by_cases hx : x ∈ tsupport β
    · have hxS : x ∈ e.source := hsuppS hx
      have hxS' : x ∈ (chartAt H p).source := β.tsupport_subset_chartAt_source hx
      by_cases hd : dist (e x) (e p) < ρ / 2
      · right; left
        have h1 : β =ᶠ[𝓝 x] 1 := β.eventuallyEq_one_of_dist_lt hxS' (by rwa [hbIn])
        filter_upwards [h1] with y hy
        simp only [Pi.one_apply] at hy
        change f y + ε * β y = f y + ε
        rw [hy, mul_one]
      · right; right
        have hyA : e x ∈ A := by
          refine ⟨?_, hd⟩
          obtain ⟨y, hy, hyx⟩ := β.tsupport_subset_symm_image_closedBall hx
          rw [← hyx, e.right_inv (β.closedBall_subset hy)]
          rw [hbOut] at hy
          exact hy.1
        refine ⟨fun hcrit => ?_, fun hcrit => ?_⟩
        · have := hρcrit (e x) hyA.1 (by rwa [e.left_inv hxS])
          apply hd
          rw [this, dist_self]
          positivity
        · rw [isCriticalPointAt_iff_chart hgs hxS] at hcrit
          have hloc' : chartRep I g p =ᶠ[𝓝 (e x)] fun y => F y + ε * B y := by
            filter_upwards [(isOpen_extChartAt_target p).mem_nhds (e.map_source hxS)] with y hy
            have hmem : e.symm y ∈ (chartAt H p).source := by
              rw [← extChartAt_source I]
              exact e.map_target hy
            change f (e.symm y) + ε * β (e.symm y) = f (e.symm y) + ε * B y
            rw [β.eqOn_source hmem, Function.comp_apply, e.right_inv hy]
          rw [hloc'.fderiv_eq] at hcrit
          have hFd : DifferentiableAt ℝ F (e x) :=
            (contDiffAt_chartRep hf.smooth (e.map_source hxS)).differentiableAt (by simp)
          have hsum : HasFDerivAt (fun y => F y + ε * B y)
              (fderiv ℝ F (e x) + ε • fderiv ℝ B (e x)) (e x) :=
            hFd.hasFDerivAt.add ((hBd (e x)).hasFDerivAt.const_mul ε)
          rw [hsum.fderiv] at hcrit
          exact hε _ hyA hcrit
    · left
      filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hx] with y hy
      exact hb0 y hy
  have hmod : ModifiedWithin f a b g := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · apply hb0
      intro hxs
      exact hx (hKIoo x (htsupp hxs))
    · by_cases hxs : x ∈ tsupport β
      · obtain ⟨h1, h2⟩ := hmK x (htsupp hxs)
        have hb1 : |ε * β x| < m := by
          rw [abs_mul]
          have hbx : |β x| ≤ 1 := by
            rw [abs_le]
            exact ⟨by linarith [β.nonneg (x := x)], β.le_one⟩
          calc |ε| * |β x| ≤ |ε| * 1 := mul_le_mul_of_nonneg_left hbx (abs_nonneg _)
            _ < m := by rw [mul_one]; exact hεm
        obtain ⟨h3, h4⟩ := abs_lt.1 hb1
        change f x + ε * β x ∈ Ioo a b
        exact ⟨by linarith, by linarith⟩
      · rw [hb0 x hxs]
        exact hx
  refine ⟨g, hmod, morseStrip_of_localShape hf hgs hmod hloc, hloc, ?_, ?_⟩
  · change f p + ε * β p = f p + ε
    rw [β.eq_one, mul_one]
  · intro x hx hxp
    apply hb0
    intro hxs
    exact hxp (hKcrit x (htsupp hxs) hx)

theorem eventually_notMem_finite {F : Set ℝ} (hF : F.Finite) : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ε ∉ F := by
  rw [eventually_nhdsWithin_iff]
  have hopen : IsOpen (F \ {0})ᶜ := hF.sdiff.isClosed.isOpen_compl
  have h0 : (0 : ℝ) ∈ (F \ {0})ᶜ := fun h => h.2 rfl
  filter_upwards [hopen.mem_nhds h0] with ε hε hne hεF
  exact hε ⟨hεF, hne⟩

end DistinctValues

open DistinctValues in
variable (I) in
theorem exists_distinct_critical_values [T2Space M] (hf : MorseStrip I f a b) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, f x ∈ Ioo a b → (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)) ∧
      (∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x) ∧
      Set.InjOn g {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} := by
  classical
  set C := {x | f x ∈ Icc a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} with hC
  have hCf : C.Finite := hf.finite_critical
  have key : ∀ T : Finset M, (↑T : Set M) ⊆ C → ∃ g : M → ℝ, ModifiedWithin f a b g ∧
      MorseStrip I g a b ∧ (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x) ∧ Set.InjOn g ↑T := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨f, ModifiedWithin.refl f a b, hf, fun _ => Iff.rfl, fun _ _ => rfl, by simp⟩
    | insert p T hpT ih =>
      intro hsub
      obtain ⟨g, hmod, hg, hcrit, hidx, hinj⟩ := ih fun x hx =>
        hsub (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
      have hpC : p ∈ C := hsub (Finset.mem_coe.2 (Finset.mem_insert_self p T))
      have hfp : f p ∈ Ioo a b := by
        rcases hpC with ⟨⟨h1, h2⟩, hc⟩
        exact ⟨lt_of_le_of_ne h1 fun h => hf.regular p (Or.inl h.symm) hc,
          lt_of_le_of_ne h2 fun h => hf.regular p (Or.inr h) hc⟩
      have hgp : g p ∈ Ioo a b := hmod.mapsTo hfp
      have hgc : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p := (hcrit p).2 hpC.2
      have hev := exists_bump_shift hg hgp hgc
      have hfin : ((fun q => g q - g p) '' (↑T : Set M)).Finite := T.finite_toSet.image _
      obtain ⟨ε, ⟨g', hmod', hg', hloc, hg'p, hg'eq⟩, hεF⟩ :=
        ((hev.filter_mono nhdsWithin_le_nhds).and (eventually_notMem_finite hfin)).exists
      have hT : ∀ x ∈ (↑T : Set M), g' x = g x := fun x hx =>
        hg'eq x ((hcrit x).2 (hsub (Finset.mem_coe.2
          (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))).2)
          fun h => hpT (h ▸ Finset.mem_coe.1 hx)
      refine ⟨g', hmod.trans hmod', hg',
        fun x => ((hloc x).isCriticalPointAt_iff hg.smooth).trans (hcrit x), fun x hx => ?_, ?_⟩
      · rw [(hloc x).morseIndex_eq ((hcrit x).2 hx), hidx x hx]
      · rw [Finset.coe_insert, Set.injOn_insert (by simpa using hpT)]
        refine ⟨fun x hx y hy hxy => hinj hx hy (by rwa [hT x hx, hT y hy] at hxy), ?_⟩
        rintro ⟨q, hq, hqp⟩
        rw [hT q hq, hg'p] at hqp
        exact hεF ⟨q, hq, by linarith⟩
  obtain ⟨g, hmod, hg, hcrit, hidx, hinj⟩ := key hCf.toFinset (by simp)
  refine ⟨g, hmod, hg, fun x _ => hcrit x, fun x _ hx => hidx x hx, hinj.mono ?_⟩
  rw [hCf.coe_toFinset]
  exact fun x hx => ⟨Ioo_subset_Icc_self hx.1, hx.2⟩

end

end DifferentialGeometry.Topology
