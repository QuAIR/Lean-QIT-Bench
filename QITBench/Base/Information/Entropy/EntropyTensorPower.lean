/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.State
public import QITBench.Base.Classical.CQState
public import QITBench.Base.Information.Entropy.Entropy
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix Polynomial

namespace QITBench

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

lemma eigenvalueMultiset_eq_of_eq {n : Type u} [Fintype n] [DecidableEq n]
    {M₁ M₂ : CMatrix n} (heq : M₁ = M₂)
    (hH : M₁.IsHermitian) (hH' : M₂.IsHermitian) :
    eigenvalueMultiset hH = eigenvalueMultiset hH' := by
  subst heq
  rfl

theorem eigenvalueMultiset_reindex {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : CMatrix α) (hM : M.IsHermitian) (e : α ≃ β) :
    eigenvalueMultiset (hM.submatrix e.symm) = eigenvalueMultiset hM := by
  have hchar :
      (M.submatrix e.symm e.symm).charpoly = M.charpoly := by
    simpa [Matrix.reindex] using Matrix.charpoly_reindex e M
  apply Multiset.map_injective (f := RCLike.ofReal (K := ℂ))
    (RCLike.ofReal_injective (K := ℂ))
  unfold eigenvalueMultiset
  rw [Multiset.map_map, Multiset.map_map]
  rw [← (hM.submatrix e.symm).roots_charpoly_eq_eigenvalues,
    ← hM.roots_charpoly_eq_eigenvalues, hchar]

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem kronecker_isHermitian (A : CMatrix a) (B : CMatrix b)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.kronecker A B).IsHermitian := by
  show (Matrix.kronecker A B)ᴴ = Matrix.kronecker A B
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker,
    show Aᴴ = A from hA.eq, show Bᴴ = B from hB.eq]

def tensorPowerMultiset (s : Multiset ℝ) : ℕ → Multiset ℝ
  | 0 => ({1} : Multiset ℝ)
  | n + 1 => s.bind fun x => (tensorPowerMultiset s n).map fun y => x * y

@[simp]
theorem tensorPowerMultiset_zero (s : Multiset ℝ) :
    tensorPowerMultiset s 0 = ({1} : Multiset ℝ) := rfl

@[simp]
theorem tensorPowerMultiset_succ (s : Multiset ℝ) (n : ℕ) :
    tensorPowerMultiset s (n + 1) =
      s.bind fun x => (tensorPowerMultiset s n).map fun y => x * y := rfl

lemma charpoly_conjStarAlgAut (M : CMatrix a) (u : Matrix.unitaryGroup a ℂ) :
    (Unitary.conjStarAlgAut ℂ _ u M).charpoly = M.charpoly := by
  rw [Unitary.conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc,
    Unitary.coe_star_mul_self, one_mul]

theorem eigenvalueMultiset_diagonal_ofReal (f : a → ℝ)
    (hD : (Matrix.diagonal fun i => (f i : ℂ)).IsHermitian) :
    eigenvalueMultiset hD = Multiset.map f Finset.univ.val := by

  have hCpoly_roots := hD.roots_charpoly_eq_eigenvalues
  have hCpoly_diag : (Matrix.diagonal fun i => (f i : ℂ)).charpoly =
      ∏ i : a, (X - C ((f i : ℂ))) := charpoly_diagonal _
  have hCpoly_roots_diag :
      (Matrix.diagonal fun i => (f i : ℂ)).charpoly.roots =
        Multiset.map (fun i => (f i : ℂ)) Finset.univ.val := by
    rw [hCpoly_diag, roots_prod]
    · simp only [roots_X_sub_C, Multiset.bind_singleton]
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero _
  have hRootsEq :
      (Multiset.map (RCLike.ofReal ∘ hD.eigenvalues) Finset.univ.val :
        Multiset ℂ) =
        Multiset.map (fun i => (f i : ℂ)) Finset.univ.val := by
    rw [← hCpoly_roots, hCpoly_roots_diag]
  have hRHSReal :
      Multiset.map (fun i => (f i : ℂ)) Finset.univ.val =
        Multiset.map (RCLike.ofReal ∘ f) Finset.univ.val := by rfl
  rw [hRHSReal] at hRootsEq
  rw [← Multiset.map_map, ← Multiset.map_map] at hRootsEq
  exact Multiset.map_injective RCLike.ofReal_injective hRootsEq

theorem eigenvalueMultiset_kronecker (A : CMatrix a) (B : CMatrix b)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    eigenvalueMultiset (kronecker_isHermitian A B hA hB) =
      (eigenvalueMultiset hA).bind fun α =>
        (eigenvalueMultiset hB).map fun β => α * β := by

  let UA : Matrix.unitaryGroup a ℂ := hA.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ := hB.eigenvectorUnitary
  let U : Matrix.unitaryGroup (Prod a b) ℂ :=
    ⟨Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b),
      Matrix.kronecker_mem_unitary UA.2 UB.2⟩
  let α : a → ℝ := hA.eigenvalues
  let β : b → ℝ := hB.eigenvalues
  let dprod : Prod a b → ℝ := fun i => α i.1 * β i.2
  have hA_spec : A = Unitary.conjStarAlgAut ℂ _ UA
      (Matrix.diagonal fun i => (α i : ℂ)) := by
    simpa [UA, α, Function.comp_def] using hA.spectral_theorem
  have hB_spec : B = Unitary.conjStarAlgAut ℂ _ UB
      (Matrix.diagonal fun i => (β i : ℂ)) := by
    simpa [UB, β, Function.comp_def] using hB.spectral_theorem

  have hAB_spec : Matrix.kronecker A B = Unitary.conjStarAlgAut ℂ _ U
      (Matrix.diagonal fun i => (dprod i : ℂ)) := by
    rw [hA_spec, hB_spec]
    simp only [Unitary.conjStarAlgAut_apply, dprod, star_eq_conjTranspose,
      U, Matrix.kronecker, ← Matrix.conjTranspose_kronecker,
      Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal,
      Complex.ofReal_mul]
  have hDprod_self : IsSelfAdjoint fun i : Prod a b => (dprod i : ℂ) := by
    show star ((fun i : Prod a b => (dprod i : ℂ))) = (fun i => (dprod i : ℂ))
    funext i
    show (starRingEnd ℂ) ((dprod i : ℝ) : ℂ) = ((dprod i : ℝ) : ℂ)
    exact Complex.conj_ofReal _
  have hDiagDprod : (Matrix.diagonal fun i => (dprod i : ℂ)).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ hDprod_self

  have hCharpoly :
      (Matrix.kronecker A B).charpoly =
        (Matrix.diagonal fun i => (dprod i : ℂ)).charpoly := by
    rw [hAB_spec, charpoly_conjStarAlgAut]

  have hEigEq :
      (kronecker_isHermitian A B hA hB).eigenvalues =
        hDiagDprod.eigenvalues :=
    (kronecker_isHermitian A B hA hB).eigenvalues_eq_eigenvalues_iff hDiagDprod
      |>.mpr hCharpoly

  show Multiset.map (kronecker_isHermitian A B hA hB).eigenvalues
        Finset.univ.val = _
  rw [hEigEq]

  show eigenvalueMultiset hDiagDprod =
      (eigenvalueMultiset hA).bind fun α_ =>
        (eigenvalueMultiset hB).map fun β_ => α_ * β_
  rw [eigenvalueMultiset_diagonal_ofReal dprod hDiagDprod]

  show Multiset.map dprod (Finset.univ : Finset (Prod a b)).val =
      (Multiset.map hA.eigenvalues (Finset.univ : Finset a).val).bind
        fun α_ => (Multiset.map hB.eigenvalues (Finset.univ : Finset b).val).map
          fun β_ => α_ * β_
  rw [← Finset.univ_product_univ, Finset.product_val]

  show Multiset.map (fun p => α p.1 * β p.2)
        ((Finset.univ : Finset a).val.bind
          fun x => (Finset.univ : Finset b).val.map fun y => (x, y)) = _
  simp only [Multiset.map_bind, Multiset.map_map, Function.comp_def,
    Multiset.bind_map]

  rfl

theorem charpoly_blockDiagonal {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : ι → CMatrix a) :
    (Matrix.blockDiagonal M).charpoly = ∏ x : ι, (M x).charpoly := by
  rw [Matrix.charpoly]
  have hCharm :
      (Matrix.blockDiagonal M).charmatrix =
        Matrix.blockDiagonal fun x => (M x).charmatrix := by
    ext i j n
    rcases i with ⟨ia, xi⟩
    rcases j with ⟨ja, xj⟩
    by_cases hξ : xi = xj
    · subst hξ
      by_cases hia : ia = ja
      · subst hia
        simp [Matrix.blockDiagonal_apply]
      · simp [Matrix.blockDiagonal_apply, hia]
    · have hpair : (ia, xi) ≠ (ja, xj) := by
        intro h
        exact hξ (Prod.mk.inj h).2
      simp [Matrix.blockDiagonal_apply, hξ, hpair]
  rw [hCharm, Matrix.det_blockDiagonal]
  rfl

omit [Fintype a] [DecidableEq a] in

theorem blockDiagonal_isHermitian {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : ι → CMatrix a) (hM : ∀ x, (M x).IsHermitian) :
    (Matrix.blockDiagonal M).IsHermitian := by
  show (Matrix.blockDiagonal M)ᴴ = Matrix.blockDiagonal M
  rw [Matrix.blockDiagonal_conjTranspose]
  exact congrArg Matrix.blockDiagonal (funext fun x => (hM x).eq)

theorem eigenvalueMultiset_blockDiagonal {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : ι → CMatrix a) (hM : ∀ x, (M x).IsHermitian) :
    eigenvalueMultiset (blockDiagonal_isHermitian M hM) =
      Finset.univ.val.bind fun x => eigenvalueMultiset (hM x) := by
  apply Multiset.map_injective (f := RCLike.ofReal (K := ℂ))
    (RCLike.ofReal_injective (K := ℂ))
  unfold eigenvalueMultiset
  rw [Multiset.map_map]
  have hRoots :
      (Matrix.blockDiagonal M).charpoly.roots =
        Finset.univ.val.bind fun x => (M x).charpoly.roots := by
    rw [charpoly_blockDiagonal M]
    exact Polynomial.roots_prod (fun x : ι => (M x).charpoly) Finset.univ
      (Finset.prod_ne_zero_iff.mpr fun x _ => (Matrix.charpoly_monic (M x)).ne_zero)
  rw [← (blockDiagonal_isHermitian M hM).roots_charpoly_eq_eigenvalues, hRoots]
  simp_rw [(hM _).roots_charpoly_eq_eigenvalues]
  simp only [Multiset.map_bind, Multiset.map_map, Function.comp_def]

omit [Fintype a] [DecidableEq a] in

theorem smul_isHermitian_ofReal (c : ℝ) (A : CMatrix a) (hA : A.IsHermitian) :
    ((c : ℂ) • A).IsHermitian :=
  hA.smul (by
    show star ((c : ℂ)) = (c : ℂ)
    simp)

theorem eigenvalueMultiset_smul_ofReal (c : ℝ) (A : CMatrix a)
    (hA : A.IsHermitian) :
    eigenvalueMultiset (smul_isHermitian_ofReal c A hA) =
      Multiset.map (fun (x : ℝ) => c * x) (eigenvalueMultiset hA) := by
  let U : Matrix.unitaryGroup a ℂ := hA.eigenvectorUnitary
  let α : a → ℝ := hA.eigenvalues
  let dscaled : a → ℝ := fun i => c * α i
  have hA_spec : A = Unitary.conjStarAlgAut ℂ _
      U (Matrix.diagonal fun i => (α i : ℂ)) := by
    simpa [U, α, Function.comp_def] using hA.spectral_theorem
  have hScaled_spec : (c : ℂ) • A = Unitary.conjStarAlgAut ℂ _
      U (Matrix.diagonal fun i => (dscaled i : ℂ)) := by
    rw [hA_spec]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [← Matrix.smul_mul (c : ℂ) ((U : CMatrix a) *
      Matrix.diagonal (fun i => (α i : ℂ))) (star (U : CMatrix a))]
    rw [← Matrix.mul_smul (U : CMatrix a) (c : ℂ)
      (Matrix.diagonal (fun i => (α i : ℂ)))]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [dscaled]
    · simp [hij]
  have hD_self : IsSelfAdjoint fun i : a => (dscaled i : ℂ) := by
    show star ((fun i : a => (dscaled i : ℂ))) = (fun i => (dscaled i : ℂ))
    funext i
    exact Complex.conj_ofReal _
  have hDiag : (Matrix.diagonal fun i => (dscaled i : ℂ)).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ hD_self
  have hChar :
      ((c : ℂ) • A).charpoly =
        (Matrix.diagonal fun i => (dscaled i : ℂ)).charpoly := by
    rw [hScaled_spec, charpoly_conjStarAlgAut]
  have hEigEq :
      (smul_isHermitian_ofReal c A hA).eigenvalues = hDiag.eigenvalues :=
    (smul_isHermitian_ofReal c A hA).eigenvalues_eq_eigenvalues_iff hDiag |>.mpr hChar
  show Multiset.map (smul_isHermitian_ofReal c A hA).eigenvalues Finset.univ.val = _
  rw [hEigEq]
  show eigenvalueMultiset hDiag = _
  rw [eigenvalueMultiset_diagonal_ofReal dscaled hDiag]
  simp [eigenvalueMultiset, dscaled, α]

namespace State

theorem eigenvalueMultiset_tensorPower (ρ : State a) :
    (n : ℕ) →
      eigenvalueMultiset ((ρ.tensorPower n).pos.isHermitian) =
        tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n
  | 0 => by

      rw [State.tensorPower_zero, tensorPowerMultiset_zero]
      have hUnit : (State.unit.matrix : CMatrix PUnit).IsHermitian :=
        State.unit.pos.isHermitian

      have hTraceEq : (State.unit.matrix : CMatrix PUnit).trace =
          ∑ i : PUnit, (hUnit.eigenvalues i : ℂ) :=
        hUnit.trace_eq_sum_eigenvalues
      have hTraceOne : (State.unit.matrix : CMatrix PUnit).trace = 1 :=
        State.unit.trace_eq_one
      have hEig : hUnit.eigenvalues PUnit.unit = (1 : ℝ) := by
        have hSum : ∑ i : PUnit, (hUnit.eigenvalues i : ℂ) = 1 := by
          rw [← hTraceEq, hTraceOne]
        simpa using hSum
      show eigenvalueMultiset hUnit = ({1} : Multiset ℝ)
      rw [eigenvalueMultiset]
      simp [hEig]
  | n + 1 => by

      rw [State.tensorPower_succ, tensorPowerMultiset_succ]
      have hIH := eigenvalueMultiset_tensorPower ρ n

      have hKron : eigenvalueMultiset
          (kronecker_isHermitian ρ.matrix (ρ.tensorPower n).matrix
            ρ.pos.isHermitian (ρ.tensorPower n).pos.isHermitian) =
          (eigenvalueMultiset ρ.pos.isHermitian).bind fun α =>
            (eigenvalueMultiset (ρ.tensorPower n).pos.isHermitian).map
              fun β => α * β :=
        eigenvalueMultiset_kronecker ρ.matrix (ρ.tensorPower n).matrix
          ρ.pos.isHermitian (ρ.tensorPower n).pos.isHermitian

      show eigenvalueMultiset (kronecker_isHermitian ρ.matrix (ρ.tensorPower n).matrix
          ρ.pos.isHermitian (ρ.tensorPower n).pos.isHermitian) = _
      rw [hKron, hIH]

end State

lemma multiset_sum_bind {α : Type*} {β : Type*} [AddCommMonoid β]
    (s : Multiset α) (f : α → Multiset β) :
    (s.bind f).sum = (s.map fun a => (f a).sum).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_bind, Multiset.sum_add, ih,
        Multiset.map_cons, Multiset.sum_cons]

lemma multiset_sum_mul_const {α : Type*} {R : Type*} [NonUnitalNonAssocSemiring R]
    (s : Multiset α) (f : α → R) (c : R) :
    (s.map fun a => f a * c).sum = (s.map f).sum * c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [ih, show (f a + (Multiset.map f s).sum) * c =
        f a * c + (Multiset.map f s).sum * c from add_mul _ _ _]

lemma multiset_sum_add_distrib {α : Type*} {R : Type*} [AddCommMonoid R]
    (s : Multiset α) (f g : α → R) :
    (s.map fun a => f a + g a).sum = (s.map f).sum + (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [ih, add_add_add_comm]

namespace State

theorem vonNeumann_reindex {β : Type v} [Fintype β] [DecidableEq β]
    (ρ : State a) (e : a ≃ β) :
    vonNeumann (ρ.reindex e) = vonNeumann ρ := by
  rw [vonNeumann_eq_neg_sum_eigenvalueMultiset,
    vonNeumann_eq_neg_sum_eigenvalueMultiset]
  exact congrArg (fun s : Multiset ℝ => -((s.map xlog2).sum))
    (by simpa [State.reindex] using
      eigenvalueMultiset_reindex ρ.matrix ρ.pos.isHermitian e)

lemma eigenvalueMultiset_sum (ρ : State a) :
    (eigenvalueMultiset ρ.pos.isHermitian).sum = 1 := by
  have hc : ∑ i, ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ) = 1 :=
    ρ.pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans ρ.trace_eq_one
  have hreal : ∑ i, ρ.pos.isHermitian.eigenvalues i = 1 :=
    Complex.ofReal_injective (by simpa using hc)
  show (Multiset.map ρ.pos.isHermitian.eigenvalues Finset.univ.val).sum = 1
  exact (Finset.sum_eq_multiset_sum (s := Finset.univ)
            (f := ρ.pos.isHermitian.eigenvalues)).symm.trans hreal

lemma eigenvalueMultiset_nonneg (ρ : State a) :
    ∀ x ∈ eigenvalueMultiset ρ.pos.isHermitian, 0 ≤ x := by
  rw [eigenvalueMultiset]
  simp only [Multiset.mem_map, Finset.mem_val]
  rintro x ⟨i, _, rfl⟩
  exact ρ.pos.eigenvalues_nonneg i

lemma vonNeumann_eq_neg_sum_xlog2_of_diagonal
    (ρ : State a) (p : a → ℝ)
    (hρ : ρ.matrix = Matrix.diagonal fun i => (p i : ℂ)) :
    vonNeumann ρ = -(∑ i, xlog2 (p i)) := by
  have hD : (Matrix.diagonal fun i => (p i : ℂ)).IsHermitian := hρ ▸ ρ.pos.isHermitian
  have hSpec : eigenvalueMultiset ρ.pos.isHermitian = Multiset.map p Finset.univ.val := by
    rw [eigenvalueMultiset_eq_of_eq hρ ρ.pos.isHermitian hD,
      eigenvalueMultiset_diagonal_ofReal p hD]
  rw [vonNeumann_eq_neg_sum_eigenvalueMultiset, hSpec]
  simp only [Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

private lemma xlog2_mul_log2_self {x : ℝ} (hx : 0 ≤ x) :
    xlog2 x * Real.log 2 = x * Real.log x := by
  by_cases hzx : x = 0
  · simp [xlog2, hzx, Real.log_zero]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzx)
    simp only [xlog2, if_neg (ne_of_gt hxp), log2]
    field_simp

private lemma xlog2_mul_split {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    xlog2 (x * y) * Real.log 2 =
      y * (xlog2 x * Real.log 2) + x * (xlog2 y * Real.log 2) := by
  rw [xlog2_mul_log2_self (mul_nonneg hx hy), xlog2_mul_log2_self hx,
      xlog2_mul_log2_self hy]
  by_cases hzx : x = 0 <;> by_cases hzy : y = 0
  · simp [hzx, hzy, Real.log_zero]
  · simp only [hzx, zero_mul, Real.log_zero, mul_zero]; ring
  · simp only [hzy, mul_zero, Real.log_zero, mul_zero]; ring
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzx)
    have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hzy)
    rw [Real.log_mul (ne_of_gt hxp) (ne_of_gt hyp)]
    ring

private lemma xlog2_sum_inner (t : Multiset ℝ) (x : ℝ)
    (hx : 0 ≤ x) (ht : ∀ y ∈ t, 0 ≤ y) :
    (t.map (fun y => xlog2 (x * y))).sum * Real.log 2 =
      x * ((t.map xlog2).sum * Real.log 2) +
        t.sum * (xlog2 x * Real.log 2) := by

  rw [← multiset_sum_mul_const]

  rw [Multiset.map_congr rfl (fun y hy => xlog2_mul_split hx (ht y hy))]

  rw [multiset_sum_add_distrib]
  ·
    rw [multiset_sum_mul_const, Multiset.map_id']

    rw [Multiset.map_congr rfl (fun y _ =>
        (by ring : x * (xlog2 y * Real.log 2) = xlog2 y * (x * Real.log 2)))]
    rw [multiset_sum_mul_const]
    ring

private lemma xlog2_sum_scaled_state_spectrum (p : ℝ) (ρ : State a) (hp : 0 ≤ p) :
    (Multiset.map (fun (x : ℝ) => xlog2 (p * x))
        (eigenvalueMultiset ρ.pos.isHermitian)).sum =
      p * (Multiset.map xlog2 (eigenvalueMultiset ρ.pos.isHermitian)).sum +
        xlog2 p := by
  let s : Multiset ℝ := eigenvalueMultiset ρ.pos.isHermitian
  have hLog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hScaled :
      (Multiset.map (fun (x : ℝ) => xlog2 (p * x)) s).sum * Real.log 2 =
        (p * (Multiset.map xlog2 s).sum + xlog2 p) * Real.log 2 := by
    have hInner := xlog2_sum_inner s p hp (by
      intro y hy
      exact State.eigenvalueMultiset_nonneg ρ y (by simpa [s] using hy))
    rw [show s.sum = 1 by simpa [s] using State.eigenvalueMultiset_sum ρ] at hInner
    simpa [s, add_mul, mul_assoc] using hInner
  exact mul_right_cancel₀ hLog2 hScaled

private lemma xlog2_sum_cq_block_spectrum {ι : Type v}
    [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (σ : ι → State a)
    (hp : ∀ x, 0 ≤ p x) :
    (Multiset.map xlog2
        (Finset.univ.val.bind fun x =>
          Multiset.map (fun (y : ℝ) => p x * y)
            (eigenvalueMultiset (σ x).pos.isHermitian))).sum =
      ∑ x, (p x *
          (Multiset.map xlog2 (eigenvalueMultiset (σ x).pos.isHermitian)).sum +
        xlog2 (p x)) := by
  rw [Multiset.map_bind, multiset_sum_bind]
  simp only [Multiset.map_map, Function.comp_def]
  rw [Finset.sum_eq_multiset_sum]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun x _ =>
    xlog2_sum_scaled_state_spectrum (p x) (σ x) (hp x))

theorem vonNeumann_eq_shannon_add_average_of_blockDiagonal {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (ρ : State (Prod a ι)) (p : ι → ℝ) (σ : ι → State a)
    (hp : ∀ x, 0 ≤ p x)
    (hρ : ρ.matrix = Matrix.blockDiagonal fun x => (p x : ℂ) • (σ x).matrix) :
    ρ.vonNeumann = -(∑ x, xlog2 (p x)) + ∑ x, p x * (σ x).vonNeumann := by
  let blocks : ι → CMatrix a := fun x => (p x : ℂ) • (σ x).matrix
  let hBlocks : ∀ x, (blocks x).IsHermitian :=
    fun x => smul_isHermitian_ofReal (p x) (σ x).matrix (σ x).pos.isHermitian
  have hBD : (Matrix.blockDiagonal blocks).IsHermitian :=
    blockDiagonal_isHermitian blocks hBlocks
  have hSpec :
      eigenvalueMultiset ρ.pos.isHermitian =
        Finset.univ.val.bind fun x =>
          Multiset.map (fun (y : ℝ) => p x * y)
            (eigenvalueMultiset (σ x).pos.isHermitian) := by
    rw [eigenvalueMultiset_eq_of_eq hρ ρ.pos.isHermitian hBD]
    rw [eigenvalueMultiset_blockDiagonal blocks hBlocks]
    exact Multiset.bind_congr fun x _ => by
      simpa [blocks, hBlocks] using
        eigenvalueMultiset_smul_ofReal (p x) (σ x).matrix (σ x).pos.isHermitian
  rw [vonNeumann_eq_neg_sum_eigenvalueMultiset, hSpec]
  rw [xlog2_sum_cq_block_spectrum p σ hp]
  simp_rw [vonNeumann_eq_neg_sum_eigenvalueMultiset]
  rw [Finset.sum_add_distrib]
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]
  ring_nf

theorem cqState_marginalA_vonNeumann {ι : Type v}
    [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) :
    State.vonNeumann E.cqState.marginalA = -(∑ x, xlog2 ((E.probs x : ℝ))) := by
  have hρ : E.cqState.marginalA.matrix =
      Matrix.diagonal fun x => ((E.probs x : ℝ) : ℂ) := by
    rw [State.marginalA_matrix, Ensemble.partialTraceB_cqState]
  rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal E.cqState.marginalA
      (fun x => (E.probs x : ℝ)) hρ]

theorem cqState_reindex_prodComm_matrix {ι : Type v}
    [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) :
    (E.cqState.reindex (Equiv.prodComm ι a)).matrix =
      Matrix.blockDiagonal fun x => ((E.probs x : ℝ) : ℂ) • (E.states x).matrix := by
  ext i j
  rcases i with ⟨i, x⟩
  rcases j with ⟨j, y⟩
  by_cases hxy : x = y
  · subst hxy
    have hblock := Classical.cqState_block_self E x
    have hentry := congrFun (congrFun hblock i) j
    simpa [State.reindex_matrix, Classical.block, Matrix.blockDiagonal_apply] using hentry
  · have hblock := Classical.cqState_block_ne (E := E) hxy
    have hentry := congrFun (congrFun hblock i) j
    simpa [State.reindex_matrix, Classical.block, Matrix.blockDiagonal_apply, hxy] using hentry

theorem cqState_vonNeumann {ι : Type v}
    [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) :
    State.vonNeumann E.cqState =
      -(∑ x, xlog2 ((E.probs x : ℝ))) +
        ∑ x, (E.probs x : ℝ) * State.vonNeumann (E.states x) := by
  have hswap := State.vonNeumann_reindex E.cqState (Equiv.prodComm ι a)
  rw [← hswap]
  exact State.vonNeumann_eq_shannon_add_average_of_blockDiagonal
    (E.cqState.reindex (Equiv.prodComm ι a))
    (fun x => (E.probs x : ℝ)) E.states
    (fun x => NNReal.coe_nonneg (E.probs x))
    (cqState_reindex_prodComm_matrix E)

private lemma xlog2_sum_kroneckerBind_mul_log2 (s t : Multiset ℝ)
    (hs : ∀ x ∈ s, 0 ≤ x) (ht : ∀ y ∈ t, 0 ≤ y) :
    (Multiset.map xlog2 (s.bind fun x => t.map fun y => x * y)).sum * Real.log 2 =
      t.sum * ((s.map xlog2).sum * Real.log 2) +
        s.sum * ((t.map xlog2).sum * Real.log 2) := by

  rw [Multiset.map_bind, multiset_sum_bind, ← multiset_sum_mul_const]
  rw [Multiset.map_congr rfl (fun x hx =>
      Eq.trans
        (congrArg (fun m => m.sum * Real.log 2)
          (Multiset.map_map xlog2 (fun y => x * y) t))
        (xlog2_sum_inner t x (hs x hx) ht))]
  rw [multiset_sum_add_distrib]
  ·
    rw [multiset_sum_mul_const, Multiset.map_id']

    rw [Multiset.map_congr rfl (fun x _ =>
        (by ring : t.sum * (xlog2 x * Real.log 2) = xlog2 x * (t.sum * Real.log 2)))]
    rw [multiset_sum_mul_const]
    ring

theorem vonNeumann_prod (ρ : State a) (σ : State b) :
    vonNeumann (ρ.prod σ) = vonNeumann ρ + vonNeumann σ := by
  rw [vonNeumann_eq_neg_sum_eigenvalueMultiset,
      vonNeumann_eq_neg_sum_eigenvalueMultiset,
      vonNeumann_eq_neg_sum_eigenvalueMultiset]
  have hspec :
      eigenvalueMultiset (ρ.prod σ).pos.isHermitian =
        (eigenvalueMultiset ρ.pos.isHermitian).bind fun x =>
          (eigenvalueMultiset σ.pos.isHermitian).map fun y => x * y := by
    simpa [State.prod] using
      eigenvalueMultiset_kronecker ρ.matrix σ.matrix
        ρ.pos.isHermitian σ.pos.isHermitian
  rw [hspec]
  let s : Multiset ℝ := eigenvalueMultiset ρ.pos.isHermitian
  let t : Multiset ℝ := eigenvalueMultiset σ.pos.isHermitian
  have hLog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hScale :
      (Multiset.map xlog2 (s.bind fun x => t.map fun y => x * y)).sum *
          Real.log 2 =
        ((s.map xlog2).sum + (t.map xlog2).sum) * Real.log 2 := by
    rw [xlog2_sum_kroneckerBind_mul_log2 s t
        (by simpa [s] using eigenvalueMultiset_nonneg ρ)
        (by simpa [t] using eigenvalueMultiset_nonneg σ)]
    rw [show t.sum = 1 by simpa [t] using eigenvalueMultiset_sum σ]
    rw [show s.sum = 1 by simpa [s] using eigenvalueMultiset_sum ρ]
    ring
  have hEq :
      (Multiset.map xlog2 (s.bind fun x => t.map fun y => x * y)).sum =
        (s.map xlog2).sum + (t.map xlog2).sum :=
    mul_right_cancel₀ hLog2 hScale
  change
    -((Multiset.map xlog2 (s.bind fun x => t.map fun y => x * y)).sum) =
      -(s.map xlog2).sum + -(t.map xlog2).sum
  rw [hEq]
  ring

lemma tensorPowerMultiset_sum (ρ : State a) (n : ℕ) :
    (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n).sum = 1 := by
  induction n with
  | zero => simp [tensorPowerMultiset_zero]
  | succ k ih =>
    rw [tensorPowerMultiset_succ, multiset_sum_bind]

    have hInner : ∀ x, ((tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) k).map
        (fun y => x * y)).sum =
        x * (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) k).sum := by
      intro x
      rw [Multiset.map_congr rfl (fun y _ =>
            (by ring : x * y = y * x)), multiset_sum_mul_const, Multiset.map_id']
      ring
    rw [Multiset.map_congr rfl (fun x _ => hInner x)]
    rw [multiset_sum_mul_const, Multiset.map_id', ih, eigenvalueMultiset_sum]
    ring

lemma tensorPowerMultiset_nonneg (ρ : State a) (n : ℕ) :
    ∀ z ∈ tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n, 0 ≤ z := by
  induction n with
  | zero =>
    simp only [tensorPowerMultiset_zero, Multiset.mem_singleton, forall_eq]
    norm_num
  | succ k ih =>
    intro z hz
    rw [tensorPowerMultiset_succ] at hz
    simp only [Multiset.mem_bind, Multiset.mem_map] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    exact mul_nonneg (eigenvalueMultiset_nonneg ρ x hx) (ih y hy)

private lemma xlog2_sum_tensorPower_mul_log2 (ρ : State a) (n : ℕ) :
    (Multiset.map xlog2
        (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n)).sum
      * Real.log 2 =
      n * ((eigenvalueMultiset ρ.pos.isHermitian).map xlog2).sum * Real.log 2 := by
  induction n with
  | zero =>

    rw [tensorPowerMultiset_zero]
    simp only [Multiset.map_singleton, Multiset.sum_singleton,
      xlog2_mul_log2_self zero_le_one, Real.log_one, Nat.cast_zero, zero_mul, mul_zero]
  | succ k ih =>

    rw [tensorPowerMultiset_succ]

    rw [xlog2_sum_kroneckerBind_mul_log2
        (eigenvalueMultiset ρ.pos.isHermitian)
        (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) k)
        (eigenvalueMultiset_nonneg ρ)
        (tensorPowerMultiset_nonneg ρ k)]

    rw [tensorPowerMultiset_sum, eigenvalueMultiset_sum, ih]
    push_cast; ring

theorem vonNeumann_tensorPower (ρ : State a) (n : ℕ) :
    vonNeumann (ρ.tensorPower n) = n * vonNeumann ρ := by

  rw [vonNeumann_eq_neg_sum_eigenvalueMultiset,
      vonNeumann_eq_neg_sum_eigenvalueMultiset]

  rw [eigenvalueMultiset_tensorPower ρ n]

  have hLog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hScale := xlog2_sum_tensorPower_mul_log2 ρ n

  have hEq : ((tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n).map xlog2).sum =
      n * ((eigenvalueMultiset ρ.pos.isHermitian).map xlog2).sum :=
    mul_right_cancel₀ hLog2 hScale
  rw [hEq]
  ring

end State

theorem cqState_marginalA_vonNeumann {ι : Type v}
    [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) :
    State.vonNeumann E.cqState.marginalA = -(∑ x, xlog2 ((E.probs x : ℝ))) :=
  State.cqState_marginalA_vonNeumann E

theorem cqState_reindex_prodComm_matrix {ι : Type v}
    [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) :
    (E.cqState.reindex (Equiv.prodComm ι a)).matrix =
      Matrix.blockDiagonal fun x => ((E.probs x : ℝ) : ℂ) • (E.states x).matrix :=
  State.cqState_reindex_prodComm_matrix E

theorem cqState_vonNeumann {ι : Type v}
    [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) :
    State.vonNeumann E.cqState =
      -(∑ x, xlog2 ((E.probs x : ℝ))) +
        ∑ x, (E.probs x : ℝ) * State.vonNeumann (E.states x) :=
  State.cqState_vonNeumann E

end

end QITBench
