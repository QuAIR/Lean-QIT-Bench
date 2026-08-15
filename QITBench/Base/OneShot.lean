/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.OneShot

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

def IsProbabilityDistribution
    {X : Type*} [Fintype X]
    (p : X → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ (∑ x, p x) = 1

noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

noncomputable def schmidtEntropy
    {X : Type*} [Fintype X]
    (p : X → ℝ) : ℝ :=
  -∑ x, p x * log2 (p x)

def HasSchmidtCoefficients
    {X : Type*} [Fintype X] [DecidableEq X]
    (psi : PureVector (X × X)) (p : X → ℝ) : Prop :=
  ∀ x y : X,
    psi.amp (x, y) = if x = y then ((Real.sqrt (p x) : ℝ) : ℂ) else 0

structure SEPProtocol
    (A B A' B' : Type*)
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B'] where
  KrausIndex : Type*
  [fintypeKrausIndex : Fintype KrausIndex]
  leftKraus : KrausIndex → Matrix A' A ℂ
  rightKraus : KrausIndex → Matrix B' B ℂ
  tracePreserving :
    MatrixMap.IsTracePreserving
      (MatrixMap.ofKraus fun k : KrausIndex =>
        Matrix.kronecker (leftKraus k) (rightKraus k))

namespace SEPProtocol

variable {A B A' B' : Type*}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype A'] [DecidableEq A']
variable [Fintype B'] [DecidableEq B']

noncomputable def productKraus (P : SEPProtocol A B A' B')
    (k : P.KrausIndex) : Matrix (A' × B') (A × B) ℂ :=
  Matrix.kronecker (P.leftKraus k) (P.rightKraus k)

noncomputable def channel (P : SEPProtocol A B A' B') : Channel (A × B) (A' × B') := by
  letI := P.fintypeKrausIndex
  exact {
    map := MatrixMap.ofKraus P.productKraus
    completelyPositive := MatrixMap.ofKraus_completelyPositive P.productKraus
    tracePreserving := by
      simpa [productKraus] using P.tracePreserving
    mapsPositive := MatrixMap.ofKraus_mapsPositive P.productKraus
  }

end SEPProtocol

noncomputable def matrixSqrt
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) : CMatrix d :=
  CFC.sqrt A

noncomputable def traceNorm
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) : ℝ :=
  Complex.re (Matrix.trace (matrixSqrt (A.conjTranspose * A)))

noncomputable def quantumFidelity
    {d : Type*} [Fintype d] [DecidableEq d]
    (rho sigma : CMatrix d) : ℝ :=
  Complex.re (Matrix.trace (matrixSqrt (matrixSqrt rho * sigma * matrixSqrt rho)))

noncomputable def targetRankAtRate (R : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (Real.rpow (2 : ℝ) ((n : ℝ) * R))

noncomputable def maximallyEntangledVector (M : ℕ) : (Fin M × Fin M) → ℂ :=
  fun ij => if ij.1 = ij.2 then (((1 : ℝ) / Real.sqrt (M : ℝ)) : ℂ) else 0

noncomputable def maximallyEntangledDensity (M : ℕ) : CMatrix (Fin M × Fin M) :=
  rankOneMatrix (maximallyEntangledVector M)

noncomputable def concentrationRate
    (M : ℕ → ℕ)
    (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * log2 (M n)

def AsymptoticRateAtMost
    (entropy : ℝ)
    (M : ℕ → ℕ) : Prop :=
  ∀ R : ℝ,
    entropy < R →
      ∀ᶠ n in Filter.atTop, concentrationRate M n ≤ R

def SchmidtCoefficientsSorted
    {d : ℕ}
    (mu : Fin d → ℝ) : Prop :=
  ∀ i j : Fin d, (i : ℕ) ≤ (j : ℕ) → mu j ≤ mu i

def IsSchmidtProbabilityVector
    {d : ℕ}
    (mu : Fin d → ℝ) : Prop :=
  SchmidtCoefficientsSorted mu ∧
    (∀ i, 0 < mu i) ∧
      (∑ i, mu i) = 1

def largestSchmidtCoefficient
    {d : ℕ}
    (mu : Fin d → ℝ) (hd : 0 < d) : ℝ :=
  mu ⟨0, hd⟩

noncomputable def maximallyEntangledSchmidtCoefficients
    {d : ℕ}
    (M : ℕ) : Fin d → ℝ :=
  fun i => if (i : ℕ) < M then (1 : ℝ) / (M : ℝ) else 0

noncomputable def sumFirst
    {d : ℕ}
    (k : ℕ) (v : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, if (i : ℕ) < k then v i else 0

def MajorizedBy
    {d : ℕ}
    (p q : Fin d → ℝ) : Prop :=
  (∀ k : ℕ, k ≤ d → sumFirst k p ≤ sumFirst k q) ∧
    (∑ i, p i) = ∑ i, q i

noncomputable def CanTransformDeterministicallyBySEP
    {d : ℕ}
    (mu : Fin d → ℝ) (M : ℕ) : Prop :=
  IsSchmidtProbabilityVector mu ∧
    0 < M ∧
      M ≤ d ∧
        MajorizedBy mu (maximallyEntangledSchmidtCoefficients (d := d) M)

end

end QITBench.OneShot
