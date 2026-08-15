/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Fidelity.TraceDistance
public import QITBench.Base.Fidelity.TraceNormSpectral
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

namespace QITBench.Fidelity

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

noncomputable section

private theorem quadraticForm_eq_dotProduct {n : ℕ}
    (A : CMatrix (Fin n)) (x : Fin n → ℂ) :
    quadraticForm A x = star x ⬝ᵥ (A *ᵥ x) := by
  simp [quadraticForm, dotProduct, Matrix.mulVec,
    Finset.mul_sum, mul_assoc]

private theorem quadraticForm_sub {n : ℕ}
    (A B : CMatrix (Fin n)) (x : Fin n → ℂ) :
    quadraticForm (A - B) x = quadraticForm A x - quadraticForm B x := by
  simp [quadraticForm, Matrix.sub_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib]

private theorem star_dotProduct_mulVec {d : Type*} [Fintype d]
    (M : CMatrix d) (x y : d → ℂ) :
    star x ⬝ᵥ (M *ᵥ y) = star (star M *ᵥ x) ⬝ᵥ y := by
  calc star x ⬝ᵥ (M *ᵥ y) = (star x ᵥ* M) ⬝ᵥ y := Matrix.dotProduct_mulVec _ _ _
    _ = star (star M *ᵥ x) ⬝ᵥ y := by
        rw [Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_conjTranspose]

private theorem rankOneMatrix_mulVec {d : Type*} [Fintype d]
    (M : CMatrix d) (x : d → ℂ) :
    rankOneMatrix (M *ᵥ x) = M * rankOneMatrix x * star M := by
  have h1 : rankOneMatrix (M *ᵥ x) = Matrix.vecMulVec (M *ᵥ x) (star (M *ᵥ x)) := rfl
  have h2 : rankOneMatrix x = Matrix.vecMulVec x (star x) := rfl
  rw [h1, h2, Matrix.star_mulVec, Matrix.star_eq_conjTranspose, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul]

private theorem trace_rankOne_star_unitary_mulVec {d : Type*} [Fintype d] [DecidableEq d]
    (U : unitary (CMatrix d)) (x : d → ℂ) :
    Matrix.trace (rankOneMatrix ((star (U : CMatrix d)) *ᵥ x)) =
      Matrix.trace (rankOneMatrix x) := by
  have hstar : star (star (U : CMatrix d)) = (U : CMatrix d) := star_star _
  have hun : (U : CMatrix d) * (star (U : CMatrix d)) = 1 :=
    Unitary.coe_mul_star_self U
  rw [rankOneMatrix_mulVec, hstar]
  calc Matrix.trace ((star (U : CMatrix d)) * rankOneMatrix x * (U : CMatrix d))
      = Matrix.trace ((U : CMatrix d) *
          ((star (U : CMatrix d)) * rankOneMatrix x)) :=
        Matrix.trace_mul_comm _ _
    _ = Matrix.trace (((U : CMatrix d) *
          (star (U : CMatrix d))) * rankOneMatrix x) := by
        rw [Matrix.mul_assoc]
    _ = Matrix.trace (rankOneMatrix x) := by rw [hun, Matrix.one_mul]

private theorem re_trace_abs_eq_sum_abs_eigenvalues {d : Type*} [Fintype d] [DecidableEq d]
    {X : CMatrix d} (hX : X.IsHermitian) :
    Complex.re (Matrix.trace (CFC.sqrt (X.conjTranspose * X))) =
      ∑ i, |hX.eigenvalues i| := by
  classical
  set U := hX.eigenvectorUnitary with hU
  set e := hX.eigenvalues with he
  set D : CMatrix d := Matrix.diagonal (RCLike.ofReal ∘ e) with hD
  set Dabs : CMatrix d := Matrix.diagonal (fun i => ((|e i| : ℝ) : ℂ)) with hDabs
  have hspec : X = Unitary.conjStarAlgAut ℂ _ U D := hX.spectral_theorem
  set B : CMatrix d := Unitary.conjStarAlgAut ℂ _ U Dabs with hB
  have hB_eq : B = (U : CMatrix d) * Dabs * (star (U : CMatrix d)) :=
    Unitary.conjStarAlgAut_apply _ _
  have hDabs_pos : Dabs.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact Complex.zero_le_real.mpr (abs_nonneg _)
  have hB_pos : B.PosSemidef := by
    rw [hB_eq]
    have hstarU : (star (U : CMatrix d)) = ((U : CMatrix d))ᴴ :=
      Matrix.star_eq_conjTranspose _
    rw [hstarU]
    exact hDabs_pos.mul_mul_conjTranspose_same (U : CMatrix d)
  have hDD : Dabs * Dabs = D * D := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst i
      simp only [Matrix.diagonal_apply, ↓reduceIte, Function.comp_apply]
      show ((|e j| : ℝ) : ℂ) * ((|e j| : ℝ) : ℂ) = ((e j : ℝ) : ℂ) * ((e j : ℝ) : ℂ)
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, abs_mul_abs_self]
    · simp [hij]
  have hBB : B * B = X.conjTranspose * X := by
    have hsquare : B * B = Unitary.conjStarAlgAut ℂ _ U (Dabs * Dabs) :=
      (map_mul (Unitary.conjStarAlgAut ℂ (CMatrix d) U) Dabs Dabs).symm
    have hXX : X * X = Unitary.conjStarAlgAut ℂ _ U (D * D) := by
      rw [hspec]
      exact (map_mul (Unitary.conjStarAlgAut ℂ (CMatrix d) U) D D).symm
    rw [hsquare, hDD, ← hXX, hX.eq]
  have hsqrt : CFC.sqrt (X.conjTranspose * X) = B := by
    have ha : 0 ≤ X.conjTranspose * X :=
      Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self X)
    have hb : 0 ≤ B := hB_pos.nonneg
    exact (CFC.sqrt_eq_iff _ _ ha hb).mpr hBB
  have htrace : B.trace = ∑ i, ((|e i| : ℝ) : ℂ) := by
    rw [hB_eq]
    calc Matrix.trace ((U : CMatrix d) * Dabs * (star (U : CMatrix d)))
        = Matrix.trace ((star (U : CMatrix d)) * ((U : CMatrix d) * Dabs)) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace (((star (U : CMatrix d)) * (U : CMatrix d)) * Dabs) := by
          rw [Matrix.mul_assoc]
      _ = Matrix.trace Dabs := by
          rw [Unitary.coe_star_mul_self, Matrix.one_mul]
      _ = ∑ i, ((|e i| : ℝ) : ℂ) := Matrix.trace_diagonal _
  rw [hsqrt, htrace, ← Complex.ofReal_sum, Complex.ofReal_re]

private theorem trace_hermitian_eq_sum_eigenvalues {d : Type*} [Fintype d] [DecidableEq d]
    {X : CMatrix d} (hX : X.IsHermitian) :
    X.trace = ∑ i, ((hX.eigenvalues i : ℝ) : ℂ) := by
  classical
  set U := hX.eigenvectorUnitary with hU
  set e := hX.eigenvalues with he
  set D : CMatrix d := Matrix.diagonal (RCLike.ofReal ∘ e) with hD
  have hspec : X = Unitary.conjStarAlgAut ℂ _ U D := hX.spectral_theorem
  calc X.trace = Matrix.trace ((U : CMatrix d) * D * (star (U : CMatrix d))) := by
        rw [hspec, Unitary.conjStarAlgAut_apply]
    _ = Matrix.trace ((star (U : CMatrix d)) * ((U : CMatrix d) * D)) :=
        Matrix.trace_mul_comm _ _
    _ = Matrix.trace (((star (U : CMatrix d)) * (U : CMatrix d)) * D) := by
        rw [Matrix.mul_assoc]
    _ = Matrix.trace D := by
        rw [Unitary.coe_star_mul_self, Matrix.one_mul]
    _ = ∑ i, ((e i : ℝ) : ℂ) := by
        rw [Matrix.trace_diagonal]
        exact Finset.sum_congr rfl fun i _ => rfl

private noncomputable def spectralVec {d : Type*} [Fintype d] [DecidableEq d]
    {X : CMatrix d} (hX : X.IsHermitian) (x : d → ℂ) : d → ℂ :=
  (star (hX.eigenvectorUnitary : CMatrix d)) *ᵥ x

private theorem re_dotProduct_hermitian {d : Type*} [Fintype d] [DecidableEq d]
    {X : CMatrix d} (hX : X.IsHermitian) (x : d → ℂ) :
    Complex.re (star x ⬝ᵥ (X *ᵥ x)) =
      ∑ i, hX.eigenvalues i * Complex.re (spectralVec hX x i * star (spectralVec hX x i)) := by
  classical
  set U := hX.eigenvectorUnitary with hU
  set e := hX.eigenvalues with he
  have hspec : X = Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (RCLike.ofReal ∘ e)) :=
    hX.spectral_theorem
  have hXv : X *ᵥ x = (U : CMatrix d) *ᵥ
      (Matrix.diagonal (RCLike.ofReal ∘ e) *ᵥ ((star (U : CMatrix d)) *ᵥ x)) := by
    rw [hspec, Unitary.conjStarAlgAut_apply, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
  have hqf : star x ⬝ᵥ (X *ᵥ x) = ∑ i, ((e i : ℝ) : ℂ) * (spectralVec hX x i * star (spectralVec hX x i)) := by
    rw [hXv, star_dotProduct_mulVec]
    have hstarU : star ((U : CMatrix d)) *ᵥ x = spectralVec hX x := rfl
    rw [hstarU]
    simp only [dotProduct, Matrix.mulVec, Matrix.diagonal_apply, Function.comp_apply,
      Pi.star_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp only [↓reduceIte]
      show star (spectralVec hX x i) * (((e i : ℝ) : ℂ) * spectralVec hX x i) =
        ((e i : ℝ) : ℂ) * (spectralVec hX x i * star (spectralVec hX x i))
      ring
    · intro j _ hji
      simp only [hji.symm, ↓reduceIte, zero_mul]
    · intro hi
      simp at hi
  rw [hqf, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Complex.re_ofReal_mul _ _

private theorem spectralVec_norm {d : Type*} [Fintype d] [DecidableEq d]
    {X : CMatrix d} (hX : X.IsHermitian) (x : d → ℂ)
    (hx : ∑ i, x i * star (x i) = 1) :
    ∑ i, spectralVec hX x i * star (spectralVec hX x i) = 1 := by
  have h := trace_rankOne_star_unitary_mulVec hX.eigenvectorUnitary x
  rw [rankOneMatrix_trace, rankOneMatrix_trace] at h
  have htr : x ⬝ᵥ (fun i => star (x i)) = 1 := by
    rw [← hx]; rfl
  rw [htr] at h
  exact h

private theorem two_mul_sum_le_sum_abs {d : Type*} [Fintype d]
    {e s : d → ℝ} (he : ∑ i, e i = 0) (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∑ i, s i = 1) :
    2 * ∑ i, e i * s i ≤ ∑ i, |e i| := by
  have hshift : ∑ i, e i * (s i - 1 / 2) = ∑ i, e i * s i := by
    have h1 : ∑ i, e i * (s i - 1 / 2) = ∑ i, e i * s i - (∑ i, e i) * (1 / 2) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [h1, he, zero_mul, sub_zero]
  have hbound : ∀ i, |s i - 1 / 2| ≤ 1 / 2 := by
    intro i
    have hi : s i ≤ 1 := by
      have h := Finset.single_le_sum (f := s) (fun j _ => hs0 j) (Finset.mem_univ i)
      rw [hs1] at h
      exact h
    rw [abs_le]
    constructor <;> linarith [hs0 i]
  calc 2 * ∑ i, e i * s i = 2 * ∑ i, e i * (s i - 1 / 2) := by rw [hshift]
    _ ≤ 2 * ∑ i, |e i| * (1 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc ∑ i, e i * (s i - 1 / 2)
            ≤ ∑ i, |e i * (s i - 1 / 2)| :=
              Finset.sum_le_sum fun i _ => le_abs_self _
          _ = ∑ i, |e i| * |s i - 1 / 2| :=
              Finset.sum_congr rfl fun i _ => abs_mul _ _
          _ ≤ ∑ i, |e i| * (1 / 2) :=
              Finset.sum_le_sum fun i _ =>
                mul_le_mul_of_nonneg_left (hbound i) (abs_nonneg _)
    _ = ∑ i, |e i| := by
        rw [← Finset.sum_mul]
        ring

theorem pureStateFidelity_traceDistance_lower
    {n : ℕ}
    (psi : PureVector (Fin n))
    (sigma : State (Fin n)) :
    1 - pureStateFidelity psi sigma ^ 2 ≤
      traceDistance psi.state.matrix sigma.matrix := by
  classical
  set X : CMatrix (Fin n) := psi.state.matrix - sigma.matrix with hXdef
  have hX : X.IsHermitian :=
    Matrix.IsHermitian.sub psi.state_matrix_isHermitian sigma.pos.isHermitian
  have htr : X.trace = 0 := by
    rw [hXdef, Matrix.trace_sub, psi.state.trace_eq_one, sigma.trace_eq_one, sub_self]

  have hx1 : ∑ i, psi.amp i * star (psi.amp i) = 1 := by
    have h := psi.trace_rankOne_eq_one
    rw [rankOneMatrix_trace] at h
    exact h

  have hq_nonneg : 0 ≤ quadraticForm sigma.matrix psi.amp := by
    rw [quadraticForm_eq_dotProduct]
    exact sigma.pos.dotProduct_mulVec_nonneg psi.amp
  have hF_sq : pureStateFidelity psi sigma ^ 2 =
      Complex.re (quadraticForm sigma.matrix psi.amp) :=
    Real.sq_sqrt (Complex.nonneg_iff.mp hq_nonneg).1

  have hψ1 : (∑ i, star (psi.amp i) * psi.amp i) = 1 := by
    rw [← hx1]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hqfP : quadraticForm psi.state.matrix psi.amp = 1 := by
    rw [quadraticForm_eq_dotProduct, PureVector.state_matrix]
    have hvec : (rankOneMatrix psi.amp *ᵥ psi.amp) =
        fun i => psi.amp i * (∑ j, star (psi.amp j) * psi.amp j) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, rankOneMatrix_apply, mul_assoc]
      rw [← Finset.mul_sum]
    calc star psi.amp ⬝ᵥ (rankOneMatrix psi.amp *ᵥ psi.amp)
        = ∑ i, star (psi.amp i) * (psi.amp i * (∑ j, star (psi.amp j) * psi.amp j)) := by
          rw [hvec]; rfl
      _ = (∑ i, star (psi.amp i) * psi.amp i) * (∑ j, star (psi.amp j) * psi.amp j) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := by rw [hψ1, mul_one]

  have hXtr0 : ∑ i, hX.eigenvalues i = 0 := by
    have h := trace_hermitian_eq_sum_eigenvalues hX
    rw [htr] at h
    have h2 := congrArg Complex.re h
    rw [Complex.re_sum] at h2
    simp only [Complex.ofReal_re, Complex.zero_re] at h2
    exact h2.symm

  set w : Fin n → ℂ := spectralVec hX psi.amp with hwdef
  have hw1 : ∑ i, w i * star (w i) = 1 :=
    spectralVec_norm hX psi.amp hx1
  have ht1 : ∑ i, Complex.re (w i * star (w i)) = 1 := by
    rw [← Complex.re_sum, hw1, Complex.one_re]
  have ht0 : ∀ i, 0 ≤ Complex.re (w i * star (w i)) := by
    intro i
    have h : w i * star (w i) = ((Complex.normSq (w i) : ℝ) : ℂ) := Complex.mul_conj _
    rw [h, Complex.ofReal_re]
    exact Complex.normSq_nonneg _

  have hmain_eq : 1 - pureStateFidelity psi sigma ^ 2 =
      ∑ i, hX.eigenvalues i * Complex.re (w i * star (w i)) := by
    have hqX : Complex.re (quadraticForm X psi.amp) =
        1 - Complex.re (quadraticForm sigma.matrix psi.amp) := by
      rw [hXdef, quadraticForm_sub, Complex.sub_re, hqfP]
      simp
    rw [hF_sq, ← hqX]
    rw [quadraticForm_eq_dotProduct]
    exact re_dotProduct_hermitian hX psi.amp
  have htd : traceDistance psi.state.matrix sigma.matrix =
      (1 / 2 : ℝ) * ∑ i, |hX.eigenvalues i| := by
    show (1 / 2 : ℝ) * traceNorm X = (1 / 2 : ℝ) * ∑ i, |hX.eigenvalues i|
    congr 1
    exact re_trace_abs_eq_sum_abs_eigenvalues hX
  rw [hmain_eq, htd]
  have hsum := two_mul_sum_le_sum_abs hXtr0 ht0 ht1
  linarith

def pureOverlapSq {a : Type*} [Fintype a] [DecidableEq a]
    (psi phi : PureVector a) : ℝ :=
  Complex.normSq (∑ i, star (psi.amp i) * phi.amp i)

private theorem rankOneMatrix_mul_trace_re_eq_pureOverlapSq
    {a : Type*} [Fintype a] [DecidableEq a]
    (psi phi : PureVector a) :
    (rankOneMatrix psi.amp * rankOneMatrix phi.amp).trace.re =
      pureOverlapSq psi phi := by
  let C : ℂ := ∑ i, star (psi.amp i) * phi.amp i
  have htrace : (rankOneMatrix psi.amp * rankOneMatrix phi.amp).trace =
      C * star C := by
    change (Matrix.vecMulVec psi.amp (fun i => star (psi.amp i)) *
        Matrix.vecMulVec phi.amp (fun i => star (phi.amp i))).trace = _
    rw [Matrix.vecMulVec_mul_vecMulVec]
    simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ x, psi.amp x * (C * star (phi.amp x))) = C * star C
    calc
      (∑ x, psi.amp x * (C * star (phi.amp x))) =
          ∑ x, C * (star (phi.amp x) * psi.amp x) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
      _ = C * (∑ x, star (phi.amp x) * psi.amp x) := by
            simp [Finset.mul_sum]
      _ = C * star C := by
            congr 1
            simp [C, mul_comm]
  rw [htrace]
  have hC : C * star C = ((Complex.normSq C : ℝ) : ℂ) := Complex.mul_conj C
  rw [hC, Complex.ofReal_re]
  rfl

private theorem pureOverlapSq_comm
    {a : Type*} [Fintype a] [DecidableEq a]
    (psi phi : PureVector a) :
    pureOverlapSq phi psi = pureOverlapSq psi phi := by
  have hover : (∑ i, star (phi.amp i) * psi.amp i) =
      star (∑ i, star (psi.amp i) * phi.amp i) := by
    simp [mul_comm]
  change Complex.normSq (∑ i, star (phi.amp i) * psi.amp i) =
    Complex.normSq (∑ i, star (psi.amp i) * phi.amp i)
  rw [hover]
  exact Complex.normSq_conj _

theorem pureState_sub_sq_trace_re_eq_two_mul_one_sub_overlapSq
    {a : Type*} [Fintype a] [DecidableEq a]
    (psi phi : PureVector a) :
    (((psi.state.matrix - phi.state.matrix) *
        (psi.state.matrix - phi.state.matrix)).trace).re =
      2 * (1 - pureOverlapSq psi phi) := by
  have hpsi : (psi.state.matrix * psi.state.matrix).trace.re = 1 := by
    rw [PureVector.state_matrix_mul_self, psi.state.trace_eq_one]
    norm_num
  have hphi : (phi.state.matrix * phi.state.matrix).trace.re = 1 := by
    rw [PureVector.state_matrix_mul_self, phi.state.trace_eq_one]
    norm_num
  have hpsiphi : (psi.state.matrix * phi.state.matrix).trace.re =
      pureOverlapSq psi phi := by
    simpa [PureVector.state_matrix] using
      rankOneMatrix_mul_trace_re_eq_pureOverlapSq psi phi
  have hphipsi : (phi.state.matrix * psi.state.matrix).trace.re =
      pureOverlapSq psi phi := by
    have h := rankOneMatrix_mul_trace_re_eq_pureOverlapSq phi psi
    simpa [PureVector.state_matrix, pureOverlapSq_comm psi phi] using h
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub]
  rw [Complex.sub_re, Complex.sub_re, Complex.sub_re]
  rw [hpsi, hphi, hpsiphi, hphipsi]
  ring

private theorem pureState_sub_toEuclideanLin_mem_span
    {a : Type*} [Fintype a] [DecidableEq a]
    (psi phi : PureVector a) (x : EuclideanSpace ℂ a) :
    (psi.state.matrix - phi.state.matrix).toEuclideanLin x ∈
      Submodule.span ℂ
        ({WithLp.toLp 2 psi.amp, WithLp.toLp 2 phi.amp} : Set (EuclideanSpace ℂ a)) := by
  let cpsi : ℂ := ∑ j, star (psi.amp j) * x j
  let cphi : ℂ := ∑ j, star (phi.amp j) * x j
  have hx : (psi.state.matrix - phi.state.matrix).toEuclideanLin x =
      cpsi • WithLp.toLp 2 psi.amp - cphi • WithLp.toLp 2 phi.amp := by
    ext i
    simp [Matrix.toEuclideanLin, Matrix.toLpLin, Matrix.mulVec, dotProduct,
      PureVector.state_matrix, rankOneMatrix_apply, cpsi, cphi, Finset.mul_sum,
      mul_comm, mul_left_comm]
  rw [hx]
  exact Submodule.sub_mem _
    (Submodule.smul_mem _ cpsi (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ cphi (Submodule.subset_span (by simp)))

private theorem pureState_sub_toEuclideanLin_finrank_range_le_two
    {a : Type*} [Fintype a] [DecidableEq a]
    (psi phi : PureVector a) :
    Module.finrank ℂ
      (LinearMap.range (psi.state.matrix - phi.state.matrix).toEuclideanLin) ≤ 2 := by
  let s : Finset (EuclideanSpace ℂ a) :=
    {WithLp.toLp 2 psi.amp, WithLp.toLp 2 phi.amp}
  let S : Submodule ℂ (EuclideanSpace ℂ a) := Submodule.span ℂ (s : Set _)
  have hle : LinearMap.range (psi.state.matrix - phi.state.matrix).toEuclideanLin ≤ S := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    simpa [S, s] using pureState_sub_toEuclideanLin_mem_span psi phi x
  have hfin : Module.finrank ℂ S ≤ s.card := by
    simpa [S] using finrank_span_finset_le_card (R := ℂ) s
  have hcard : s.card ≤ 2 := by
    simpa [s] using
      (Finset.card_le_two (a := WithLp.toLp 2 psi.amp)
        (b := WithLp.toLp 2 phi.amp))
  exact (Submodule.finrank_mono hle).trans (hfin.trans hcard)

theorem pureState_traceDistance_le_sqrt_one_sub_overlapSq
    {a : Type*} [Fintype a] [DecidableEq a]
    (psi phi : PureVector a) :
    traceDistance psi.state.matrix phi.state.matrix ≤
      Real.sqrt (1 - pureOverlapSq psi phi) := by
  let D : CMatrix a := psi.state.matrix - phi.state.matrix
  have hDherm : D.IsHermitian := psi.state.pos.isHermitian.sub phi.state.pos.isHermitian
  have hstar : star D = D := hDherm.eq
  have hhs : ((star D * D).trace).re = 2 * (1 - pureOverlapSq psi phi) := by
    rw [hstar]
    exact pureState_sub_sq_trace_re_eq_two_mul_one_sub_overlapSq psi phi
  have htrace_nonneg : 0 ≤ ((star D * D).trace).re :=
    (Matrix.PosSemidef.trace_nonneg
      (Matrix.posSemidef_conjTranspose_mul_self D)).1
  have hsq_traceNorm : traceNorm D ^ 2 ≤ 4 * (1 - pureOverlapSq psi phi) := by
    have hrank :
        (Module.finrank ℂ (LinearMap.range D.toEuclideanLin) : ℝ) ≤ 2 := by
      exact_mod_cast pureState_sub_toEuclideanLin_finrank_range_le_two psi phi
    have hmain := traceNorm_sq_le_finrank_range_mul_hilbertSchmidt D
    calc
      traceNorm D ^ 2 ≤
          (Module.finrank ℂ (LinearMap.range D.toEuclideanLin) : ℝ) *
            ((star D * D).trace).re := hmain
      _ ≤ 2 * ((star D * D).trace).re := by
          exact mul_le_mul_of_nonneg_right hrank htrace_nonneg
      _ = 4 * (1 - pureOverlapSq psi phi) := by
          rw [hhs]
          ring
  have hsq_distance : ((1 / 2 : ℝ) * traceNorm D) ^ 2 ≤
      1 - pureOverlapSq psi phi := by
    nlinarith
  change (1 / 2 : ℝ) * traceNorm D ≤ Real.sqrt (1 - pureOverlapSq psi phi)
  exact Real.le_sqrt_of_sq_le hsq_distance

end

end QITBench.Fidelity
