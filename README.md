# Lean-QIT-Bench

[![arXiv](https://img.shields.io/badge/arXiv-2607.21533-b31b1b.svg)](https://arxiv.org/abs/2607.21533)

A Lean benchmark for quantum-information-theory agent provers.

## Contents

- `QITBench/`: Lean benchmark modules and shared foundations.
- `QITBench-TeX/`: TeX problem statements and shared macros.
- Each problem pairs a TeX statement with Lean declarations and a theorem goal;
  some problems also provide public hints.

## Build

Install the pinned Lean toolchain, then run:

```bash
lake build QITBench
```
