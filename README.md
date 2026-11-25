# Unary maps are restrictions of linear maps, k-ary maps are restrictions of homogeneous maps

Lean 4 formalization of the paper `arXiv:2611.29718`.

The main theorems are listed in `Axioms.lean`:

- Theorem 1: `unary_linear` in `HomBin/Unary.lean`
- Theorem 2: `homogeneous` in `HomBin/Homogeneous.lean`
- Theorem 3(a), Corollary 1: `HomBin/Separable.lean`
- Theorem 3(b): `invInd_not_lowDegree` in `HomBin/Inversion.lean`

Definitions are in `HomBin/Defs.lean`.

## Verify

```sh
curl -L https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source $HOME/.elan/env

git clone https://github.com/roman3017/HomBin
cd HomBin
lake exe cache get
lake build
lake env lean Axioms.lean
```

The last command prints the axioms of each main theorem: only `propext`, `Classical.choice` and
`Quot.sound`. There is no `sorry`. Lean and Mathlib `v4.36.0`.
