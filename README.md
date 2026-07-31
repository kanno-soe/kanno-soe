[![Lean Action CI](https://github.com/kanno-soe/kanno-soe/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kanno-soe/kanno-soe/actions/workflows/lean_action_ci.yml)

# [Kannō-Sōe Mutual Dependence (KSMD)](https://ksmd-theory.org/)

An axiomatic reconstruction of Zen sayings in an ontology-under-erasure act-grammar.

The project implements a deliberately simplified model for discussing Mahayana Buddhist metaphysics. It is most useful for conditional and independence results: *if* one accepts the model's translation of a claim, a proof can show that the translated claim needs no richer machinery. The conditional matters. Oversimplifying the object proves something about the simplification, not automatically about Buddhism, Nāgārjuna, Jizang, or the world. The account below therefore marks three statuses throughout: **formal model structure**, **a manually supplied interpretation**, and **the philosophical act-grammar laid over that structure**.

## Quickstart

Install [elan](https://github.com/leanprover/elan), then run:

```console
lake build
```

The repository pins Lean 4.31.0. A green build elaborates the complete library
with automatic implicit binders disabled, reduces the structural proof checks
in the kernel, resolves the `#verify_*` anchor tripwires, and compares every
audited declaration against its exact axiom allowlist. CI additionally
regenerates the exposition and checks that the committed generated Markdown has
not drifted from its Lean sources.
