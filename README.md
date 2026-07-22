# Lean-QIT-Bench

`Lean-QIT-Bench` is a Lean benchmark for quantum-information-theory agent
provers. This repository is a generated mirror of the reviewed public
benchmark surface.

Each problem provides:

- a TeX statement for human and agent reading;
- Lean definitions and a Lean statement with a `sorry` proof target;
- optional Lean hints when they are part of the published problem.

## Layout

- `QITBench/`: modular Lean statements and the benchmark-local Base library.
- `QITBench-TeX/`: TeX statements and shared macros.
- `lean-toolchain` and `lakefile.toml`: Lean package configuration.

Each Lean problem exposes:

- `QITBench/<Category>/<ProblemName>.lean`: the problem wrapper;
- `QITBench/<Category>/<ProblemName>/Definitions.lean`: supporting definitions;
- `QITBench/<Category>/<ProblemName>/Hints.lean`: optional hints;
- `QITBench/<Category>/<ProblemName>/Statement.lean`: the theorem with the proof target.

An absent `Hints.lean` means that the problem publishes no hints. To check the
complete package, install the pinned Lean toolchain and run:

```bash
lake build
```
