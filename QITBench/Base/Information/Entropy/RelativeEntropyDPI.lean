/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Information.Entropy.RelativeEntropyTraceLog
public import QITBench.Base.Information.Renyi.RenyiDPI.AlphaToOne

@[expose] public section

open Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator UniformConvergence

namespace QITBench

universe u v

noncomputable section

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

theorem relativeEntropyPSDReferenceTraceLogE_dataProcessing_channel_ge_of_eq_traceLogE
    {b : Type v} [Fintype b] [DecidableEq b]
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (Phi : Channel a b)
    (hIn :
      relativeEntropyPSDReferenceE rho sigma hSigma =
        relativeEntropyPSDReferenceTraceLogE rho sigma hSigma)
    (hOut :
      relativeEntropyPSDReferenceE
          (Phi.applyState rho) (Phi.map sigma) (Phi.mapsPositive sigma hSigma) =
        relativeEntropyPSDReferenceTraceLogE
          (Phi.applyState rho) (Phi.map sigma) (Phi.mapsPositive sigma hSigma)) :
    relativeEntropyPSDReferenceTraceLogE rho sigma hSigma >=
      relativeEntropyPSDReferenceTraceLogE
        (Phi.applyState rho) (Phi.map sigma) (Phi.mapsPositive sigma hSigma) := by
  rw [← hIn, ← hOut]
  exact relativeEntropyPSDReferenceE_dataProcessing_channel_ge rho hSigma Phi

theorem relativeEntropyPSDReferenceTraceLogE_dataProcessing_channel_ge_of_supported_endpoints
    {b : Type v} [Fintype b] [DecidableEq b]
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (Phi : Channel a b)
    (hInEndpoint :
      ∀ hSupport : Matrix.Supports rho.matrix sigma,
        Filter.Tendsto
          (sandwichedRenyiPSDReferenceHighAlphaCurve rho sigma hSigma)
          relativeEntropyHighAlphaRightToOne
          (nhds (relativeEntropyPSDReferenceTraceLogFinite
            rho sigma hSigma hSupport : EReal)))
    (hOutEndpoint :
      ∀ hSupport :
          Matrix.Supports (Phi.applyState rho).matrix (Phi.map sigma),
        Filter.Tendsto
          (sandwichedRenyiPSDReferenceHighAlphaCurve
            (Phi.applyState rho) (Phi.map sigma) (Phi.mapsPositive sigma hSigma))
          relativeEntropyHighAlphaRightToOne
          (nhds (relativeEntropyPSDReferenceTraceLogFinite
            (Phi.applyState rho) (Phi.map sigma) (Phi.mapsPositive sigma hSigma)
            hSupport : EReal))) :
    relativeEntropyPSDReferenceTraceLogE rho sigma hSigma >=
      relativeEntropyPSDReferenceTraceLogE
        (Phi.applyState rho) (Phi.map sigma) (Phi.mapsPositive sigma hSigma) := by
  exact
    relativeEntropyPSDReferenceTraceLogE_dataProcessing_channel_ge_of_eq_traceLogE
      rho hSigma Phi
      (relativeEntropyPSDReferenceE_eq_traceLogE_of_supported_endpoint
        rho hSigma hInEndpoint)
      (relativeEntropyPSDReferenceE_eq_traceLogE_of_supported_endpoint
        (Phi.applyState rho) (Phi.mapsPositive sigma hSigma) hOutEndpoint)

theorem relativeEntropyPSDReferenceTraceLogE_dataProcessing_channel_ge
    {b : Type v} [Fintype b] [DecidableEq b]
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (Phi : Channel a b) :
    relativeEntropyPSDReferenceTraceLogE rho sigma hSigma >=
      relativeEntropyPSDReferenceTraceLogE
        (Phi.applyState rho) (Phi.map sigma) (Phi.mapsPositive sigma hSigma) := by
  exact
    relativeEntropyPSDReferenceTraceLogE_dataProcessing_channel_ge_of_eq_traceLogE
      rho hSigma Phi
      (relativeEntropyPSDReferenceE_eq_traceLogE rho hSigma)
      (relativeEntropyPSDReferenceE_eq_traceLogE
        (Phi.applyState rho) (Phi.mapsPositive sigma hSigma))

theorem relativeEntropy_dataProcessing_channel_ge
    {b : Type v} [Fintype b] [DecidableEq b]
    (rho sigma : State a) (Phi : Channel a b) :
    rho.relativeEntropy sigma >=
      (Phi.applyState rho).relativeEntropy (Phi.applyState sigma) := by
  simpa [relativeEntropy, Channel.applyState] using
    relativeEntropyPSDReferenceTraceLogE_dataProcessing_channel_ge rho sigma.pos Phi

end State

end

end QITBench
