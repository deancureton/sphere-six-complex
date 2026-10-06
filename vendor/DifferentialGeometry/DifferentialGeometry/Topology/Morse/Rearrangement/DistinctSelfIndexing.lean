module

public import DifferentialGeometry.Topology.Morse.Rearrangement.DistinctValues

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H} [I.Boundaryless] [IsManifold I ∞ M]
  {f : M → ℝ} {a b : ℝ}

namespace DistinctSelfIndexing

theorem exists_pos_le_of_finite {D : Set ℝ} (hD : D.Finite) (hpos : ∀ d ∈ D, 0 < d) :
    ∃ δ > 0, ∀ d ∈ D, δ ≤ d := by
  induction D, hD using Set.Finite.induction_on with
  | empty => exact ⟨1, one_pos, fun d hd => absurd hd (notMem_empty d)⟩
  | @insert d D _ _ ih =>
    obtain ⟨δ, hδ, hle⟩ := ih fun e he => hpos e (mem_insert_of_mem d he)
    refine ⟨min δ d, lt_min hδ (hpos d (mem_insert d D)), fun e he => ?_⟩
    rcases mem_insert_iff.1 he with rfl | he
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hle e he)

theorem exists_index_gap (hf : MorseStrip I f a b) (hsi : isSelfIndexing I f a b) :
    ∃ δ > 0, ∀ p q, f p ∈ Ioo a b → f q ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f q →
      morseIndex I f p < morseIndex I f q → δ ≤ f q - f p := by
  set C := {x | f x ∈ Icc a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} with hC
  have hCf : C.Finite := hf.finite_critical
  set D := (fun pq : M × M => f pq.2 - f pq.1) ''
    {pq | pq.1 ∈ C ∧ pq.2 ∈ C ∧ f pq.1 ∈ Ioo a b ∧ f pq.2 ∈ Ioo a b ∧
      morseIndex I f pq.1 < morseIndex I f pq.2} with hD
  have hDf : D.Finite := by
    refine Set.Finite.image _ ((hCf.prod hCf).subset ?_)
    rintro ⟨p, q⟩ ⟨hp, hq, -⟩
    exact ⟨hp, hq⟩
  have hpos : ∀ d ∈ D, 0 < d := by
    rintro d ⟨⟨p, q⟩, ⟨hp, hq, hfp, hfq, hidx⟩, rfl⟩
    exact sub_pos.2 (hsi p q hfp hfq hp.2 hq.2 hidx)
  obtain ⟨δ, hδ, hle⟩ := exists_pos_le_of_finite hDf hpos
  refine ⟨δ, hδ, fun p q hfp hfq hcp hcq hidx => hle _ ?_⟩
  exact ⟨(p, q), ⟨⟨Ioo_subset_Icc_self hfp, hcp⟩, ⟨Ioo_subset_Icc_self hfq, hcq⟩, hfp, hfq, hidx⟩,
    rfl⟩

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem isSelfIndexing_of_close {g : M → ℝ} {δ : ℝ}
    (hgap : ∀ p q, f p ∈ Ioo a b → f q ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f q →
      morseIndex I f p < morseIndex I f q → δ ≤ f q - f p)
    (hmod : ModifiedWithin f a b g) (hcrit : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hidx : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x)
    (hclose : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → |g x - f x| < δ / 2) :
    isSelfIndexing I g a b := by
  intro p q hgp hgq hcp hcq hlt
  have hpre : ∀ x, g x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod.preimage_Ioo x
  have hfp : f p ∈ Ioo a b := (hpre p).1 hgp
  have hfq : f q ∈ Ioo a b := (hpre q).1 hgq
  have hcp' : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p := (hcrit p).1 hcp
  have hcq' : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f q := (hcrit q).1 hcq
  rw [hidx p hcp', hidx q hcq'] at hlt
  have h1 := hgap p q hfp hfq hcp' hcq' hlt
  have h2 := abs_sub_lt_iff.1 (hclose p hfp hcp')
  have h3 := abs_sub_lt_iff.1 (hclose q hfq hcq')
  linarith [h2.1, h3.2]

end DistinctSelfIndexing

open DistinctValues DistinctSelfIndexing in
variable (I) in
theorem exists_distinct_selfIndexing [T2Space M] (hf : MorseStrip I f a b)
    (hsi : isSelfIndexing I f a b) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ isSelfIndexing I g a b ∧
      (∀ x, f x ∈ Ioo a b → (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)) ∧
      (∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x) ∧
      Set.InjOn g {x | g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x} := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := exists_index_gap hf hsi
  have hδ2 : (0 : ℝ) < δ / 2 := by positivity
  set C := {x | f x ∈ Icc a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} with hC
  have hCf : C.Finite := hf.finite_critical
  have hCo : ∀ x ∈ C, f x ∈ Ioo a b := by
    rintro x ⟨⟨h1, h2⟩, hc⟩
    exact ⟨lt_of_le_of_ne h1 fun h => hf.regular x (Or.inl h.symm) hc,
      lt_of_le_of_ne h2 fun h => hf.regular x (Or.inr h) hc⟩
  have key : ∀ T : Finset M, (↑T : Set M) ⊆ C → ∃ g : M → ℝ, ModifiedWithin f a b g ∧
      MorseStrip I g a b ∧ (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x) ∧ Set.InjOn g ↑T ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x ∉ T → g x = f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → |g x - f x| < δ / 2) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨f, ModifiedWithin.refl f a b, hf, fun _ => Iff.rfl, fun _ _ => rfl, by simp,
        fun _ _ _ => rfl, fun x _ => ?_⟩
      simpa using hδ2
    | insert p T hpT ih =>
      intro hsub
      obtain ⟨g, hmod, hg, hcrit, hidx, hinj, hunmoved, hclose⟩ := ih fun x hx =>
        hsub (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
      have hpC : p ∈ C := hsub (Finset.mem_coe.2 (Finset.mem_insert_self p T))
      have hfp : f p ∈ Ioo a b := hCo p hpC
      have hgp : g p ∈ Ioo a b := hmod.mapsTo hfp
      have hgc : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p := (hcrit p).2 hpC.2
      have hev := exists_bump_shift hg hgp hgc
      have hfin : ((fun q => g q - g p) '' (↑T : Set M)).Finite := T.finite_toSet.image _
      have hsmall : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < δ / 2 := by
        simpa using eventually_abs_sub_lt (0 : ℝ) hδ2
      obtain ⟨ε, ⟨⟨g', hmod', hg', hloc, hg'p, hg'eq⟩, hεδ⟩, hεF⟩ :=
        (((hev.and hsmall).filter_mono nhdsWithin_le_nhds).and
          (eventually_notMem_finite hfin)).exists
      have hT : ∀ x ∈ (↑T : Set M), g' x = g x := fun x hx =>
        hg'eq x ((hcrit x).2 (hsub (Finset.mem_coe.2
          (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))).2)
          fun h => hpT (h ▸ Finset.mem_coe.1 hx)
      have hcrit' : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g' x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := fun x =>
        ((hloc x).isCriticalPointAt_iff hg.smooth).trans (hcrit x)
      refine ⟨g', hmod.trans hmod', hg', hcrit', fun x hx => ?_, ?_, fun x hx hxT => ?_,
        fun x hx => ?_⟩
      · rw [(hloc x).morseIndex_eq ((hcrit x).2 hx), hidx x hx]
      · rw [Finset.coe_insert, Set.injOn_insert (by simpa using hpT)]
        refine ⟨fun x hx y hy hxy => hinj hx hy (by rwa [hT x hx, hT y hy] at hxy), ?_⟩
        rintro ⟨q, hq, hqp⟩
        rw [hT q hq, hg'p] at hqp
        exact hεF ⟨q, hq, by linarith⟩
      · have hxp : x ≠ p := fun h => hxT (h ▸ Finset.mem_insert_self p T)
        have hxT' : x ∉ T := fun h => hxT (Finset.mem_insert_of_mem h)
        rw [hg'eq x ((hcrit x).2 hx) hxp, hunmoved x hx hxT']
      · by_cases hxp : x = p
        · subst hxp
          rw [hg'p, hunmoved x hx hpT]
          simpa using hεδ
        · rw [hg'eq x ((hcrit x).2 hx) hxp]
          exact hclose x hx
  obtain ⟨g, hmod, hg, hcrit, hidx, hinj, -, hclose⟩ := key hCf.toFinset (by simp)
  have hpre : ∀ x, g x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod.preimage_Ioo x
  refine ⟨g, hmod, hg, isSelfIndexing_of_close hgap hmod hcrit hidx fun x _ hx => hclose x hx,
    fun x _ => hcrit x, fun x _ hx => hidx x hx, hinj.mono ?_⟩
  rw [hCf.coe_toFinset]
  exact fun x hx => ⟨Ioo_subset_Icc_self ((hpre x).1 hx.1), (hcrit x).1 hx.2⟩

end

end DifferentialGeometry.Topology
