module

public import DifferentialGeometry.Topology.Morse.Rearrangement.MonotoneShift

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set

namespace NegDual

section Sets

variable {M : Type*} {f : M → ℝ} {a b c : ℝ}

theorem neg_mem_Icc_iff {x : ℝ} : -x ∈ Icc (-b) (-a) ↔ x ∈ Icc a b := by
  simp only [mem_Icc, neg_le_neg_iff]
  exact and_comm

theorem neg_mem_Ioo_iff {x : ℝ} : -x ∈ Ioo (-b) (-a) ↔ x ∈ Ioo a b := by
  simp only [mem_Ioo, neg_lt_neg_iff]
  exact and_comm

theorem neg_mem_Iic_iff {x : ℝ} : -x ∈ Iic (-c) ↔ x ∈ Ici c := by
  simp only [mem_Iic, mem_Ici, neg_le_neg_iff]

theorem preimage_neg_Icc : (fun x => -f x) ⁻¹' Icc (-b) (-a) = f ⁻¹' Icc a b := by
  ext x
  exact neg_mem_Icc_iff

theorem preimage_neg_Ioo : (fun x => -f x) ⁻¹' Ioo (-b) (-a) = f ⁻¹' Ioo a b := by
  ext x
  exact neg_mem_Ioo_iff

theorem preimage_neg_singleton : (fun x => -f x) ⁻¹' {-c} = f ⁻¹' {c} := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, neg_inj]

theorem preimage_neg_Iic : (fun x => -f x) ⁻¹' Iic (-c) = f ⁻¹' Ici c := by
  ext x
  exact neg_mem_Iic_iff

theorem neg_neg_fun : (fun x => -(-f x)) = f := by
  funext x
  exact neg_neg _

theorem connectedSpace_neg_strip_iff [TopologicalSpace M] :
    ConnectedSpace ((fun x => -f x) ⁻¹' Icc (-b) (-a)) ↔
      ConnectedSpace (f ⁻¹' Icc a b) := by
  rw [preimage_neg_Icc]

theorem simplyConnectedSpace_neg_strip_iff [TopologicalSpace M] :
    SimplyConnectedSpace ((fun x => -f x) ⁻¹' Icc (-b) (-a)) ↔
      SimplyConnectedSpace (f ⁻¹' Icc a b) := by
  rw [preimage_neg_Icc]

theorem nonempty_neg_level_iff :
    ((fun x => -f x) ⁻¹' {-c}).Nonempty ↔ (f ⁻¹' {c}).Nonempty := by
  rw [preimage_neg_singleton]

theorem simplyConnectedSpace_neg_level_iff [TopologicalSpace M] :
    SimplyConnectedSpace ((fun x => -f x) ⁻¹' {-c}) ↔ SimplyConnectedSpace (f ⁻¹' {c}) := by
  rw [preimage_neg_singleton]

end Sets

section Hessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem chartHessianAt_neg (g : E → ℝ) (x : E) :
    DifferentialGeometry.Topology.Morse.chartHessianAt (fun y => -g y) x = -DifferentialGeometry.Topology.Morse.chartHessianAt g x := by
  have h1 : fderiv ℝ (fun y => -g y) = fun y => -fderiv ℝ g y := funext fun _ => fderiv_fun_neg
  ext v
  rw [neg_apply, MonotoneShift.chartHessianAt_apply, MonotoneShift.chartHessianAt_apply, h1,
    fderiv_fun_neg]
  simp

theorem separatingLeft_associated_neg_iff (Q : QuadraticForm ℝ E) :
    (QuadraticMap.associated (R := ℝ) (-Q)).SeparatingLeft ↔
      (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft := by
  rw [map_neg]
  simp only [LinearMap.SeparatingLeft, LinearMap.neg_apply, neg_eq_zero]

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem hessianAt_neg (I : ModelWithCorners ℝ E H) (f : M → ℝ) (p : M) :
    hessianAt I (fun x => -f x) p = -hessianAt I f p :=
  chartHessianAt_neg (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)

theorem isCriticalPointAt_neg_iff (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) :
    DifferentialGeometry.Topology.Morse.IsCriticalPointAt I (fun x => -f x) x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
  unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt
  have h : mfderiv I 𝓘(ℝ, ℝ) (fun x => -f x) x = -mfderiv I 𝓘(ℝ, ℝ) f x := mfderiv_neg
  rw [h]
  exact neg_eq_zero

theorem isNondegenerateCriticalPointAt_neg_iff (I : ModelWithCorners ℝ E H) (f : M → ℝ) (p : M) :
    DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I (fun x => -f x) p ↔ DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f p := by
  change (Morse.IsCriticalPointAt I (fun x => -f x) p ∧
    (QuadraticMap.associated (R := ℝ) (hessianAt I (fun x => -f x) p)).SeparatingLeft) ↔
    (Morse.IsCriticalPointAt I f p ∧
      (QuadraticMap.associated (R := ℝ) (hessianAt I f p)).SeparatingLeft)
  rw [isCriticalPointAt_neg_iff, hessianAt_neg, separatingLeft_associated_neg_iff]

theorem crit_neg_iff (I : ModelWithCorners ℝ E H) (f : M → ℝ) {a b : ℝ} (x : M) :
    ((fun x => -f x) x ∈ Ioo (-b) (-a) ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I (fun x => -f x) x) ↔
      (f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) := by
  rw [isCriticalPointAt_neg_iff]
  exact and_congr_left fun _ => neg_mem_Ioo_iff

end Hessian

section Index

theorem sigPos_add_sigNeg_of_separatingLeft {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) : sigPos Q + sigNeg Q = n := by
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (𝕜 := ℝ) (Q := Q)
  have hrad : Q.radical = ⊥ := by
    rw [QuadraticMap.radical_eq_ker_associated, ← LinearMap.separatingLeft_iff_ker_eq_bot]
    exact hQ
  rw [hrad, finrank_bot, add_zero, Module.finrank_fin_fun] at h
  exact h

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {p : M}

theorem morseIndex_neg (I : ModelWithCorners ℝ (Fin n → ℝ) H) (f : M → ℝ) (p : M) :
    morseIndex I (fun x => -f x) p = sigPos (hessianAt I f p) := by
  unfold morseIndex
  rw [hessianAt_neg, sigNeg_neg]

theorem morseIndex_neg_add (hp : DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f p) :
    morseIndex I (fun x => -f x) p + morseIndex I f p = n := by
  rw [morseIndex_neg]
  exact sigPos_add_sigNeg_of_separatingLeft _ hp.2

theorem morseIndex_neg_add' (hp : DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I (fun x => -f x) p) :
    morseIndex I (fun x => -f x) p + morseIndex I f p = n :=
  morseIndex_neg_add ((isNondegenerateCriticalPointAt_neg_iff I f p).1 hp)

theorem morseIndex_le (hp : DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f p) : morseIndex I f p ≤ n := by
  have := morseIndex_neg_add hp
  omega

theorem morseIndex_neg_eq (hp : DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f p) :
    morseIndex I (fun x => -f x) p = n - morseIndex I f p := by
  have := morseIndex_neg_add hp
  omega

theorem morseIndex_eq_sub_neg (hp : DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f p) :
    morseIndex I f p = n - morseIndex I (fun x => -f x) p := by
  have := morseIndex_neg_add hp
  omega

theorem morseIndex_neg_eq_zero_iff (hp : DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f p) :
    morseIndex I (fun x => -f x) p = 0 ↔ morseIndex I f p = n := by
  have := morseIndex_neg_add hp
  omega

theorem morseIndex_neg_pos_iff (hp : DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f p) :
    0 < morseIndex I (fun x => -f x) p ↔ morseIndex I f p < n := by
  have := morseIndex_neg_add hp
  omega

theorem morseIndex_neg_lt_iff (hp : DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f p) :
    morseIndex I (fun x => -f x) p < n ↔ 0 < morseIndex I f p := by
  have := morseIndex_neg_add hp
  omega

end Index

end NegDual

section Structures

open NegDual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {f g : M → ℝ} {a b : ℝ}

theorem MorseStrip.neg (hf : MorseStrip I f a b) : MorseStrip I (fun x => -f x) (-b) (-a) where
  smooth := hf.smooth.neg
  lt := neg_lt_neg hf.lt
  compact := by
    rw [preimage_neg_Icc]
    exact hf.compact
  regular := fun x hx => by
    rw [isCriticalPointAt_neg_iff]
    apply hf.regular
    rcases hx with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  nondegenerate := fun x hx hc => by
    rw [isNondegenerateCriticalPointAt_neg_iff]
    exact hf.nondegenerate x (neg_mem_Ioo_iff.1 hx) ((isCriticalPointAt_neg_iff I f x).1 hc)

theorem MorseStrip.of_neg (hf : MorseStrip I (fun x => -f x) (-b) (-a)) : MorseStrip I f a b := by
  have h := hf.neg
  simpa only [neg_neg_fun, neg_neg] using h

theorem isSelfIndexing.neg {n : ℕ} {I : ModelWithCorners ℝ (Fin n → ℝ) H}
    (hf : MorseStrip I f a b) (h : isSelfIndexing I f a b) :
    isSelfIndexing I (fun x => -f x) (-b) (-a) := by
  intro p q hp hq hcp hcq hlt
  rw [neg_mem_Ioo_iff] at hp hq
  rw [isCriticalPointAt_neg_iff] at hcp hcq
  have hnp := hf.nondegenerate p hp hcp
  have hnq := hf.nondegenerate q hq hcq
  have h1 := morseIndex_neg_add hnp
  have h2 := morseIndex_neg_add hnq
  have hqp : morseIndex I f q < morseIndex I f p := by omega
  have := h q p hq hp hcq hcp hqp
  change -f p < -f q
  linarith

theorem isSelfIndexing.of_neg {n : ℕ} {I : ModelWithCorners ℝ (Fin n → ℝ) H}
    (hf : MorseStrip I f a b) (h : isSelfIndexing I (fun x => -f x) (-b) (-a)) :
    isSelfIndexing I f a b := by
  have h' := h.neg hf.neg
  simpa only [neg_neg_fun, neg_neg] using h'

omit [TopologicalSpace M] in
theorem ModifiedWithin.neg (h : ModifiedWithin f a b g) :
    ModifiedWithin (fun x => -f x) (-b) (-a) (fun x => -g x) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [preimage_neg_Ioo] at hx
    show -g x = -f x
    rw [h.eqOn hx]
  · rw [preimage_neg_Ioo] at hx
    exact neg_mem_Ioo_iff.2 (h.mapsTo hx)

omit [TopologicalSpace M] in
theorem ModifiedWithin.of_neg (h : ModifiedWithin (fun x => -f x) (-b) (-a) (fun x => -g x)) :
    ModifiedWithin f a b g := by
  have h' := h.neg
  simpa only [neg_neg_fun, neg_neg] using h'

omit [TopologicalSpace M] in
theorem modifiedWithin_neg_iff :
    ModifiedWithin (fun x => -f x) (-b) (-a) (fun x => -g x) ↔ ModifiedWithin f a b g :=
  ⟨ModifiedWithin.of_neg, ModifiedWithin.neg⟩

end Structures

end DifferentialGeometry.Topology
