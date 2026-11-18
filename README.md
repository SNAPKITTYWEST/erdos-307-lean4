# Erdős Problem 307 — Lean 4 Formal Proofs

[![License: BSL-1.1](https://img.shields.io/badge/license-BSL--1.1-orange?style=flat-square)](LICENSE)
[![License: AGPL-3.0](https://img.shields.io/badge/license-AGPL--3.0-blue?style=flat-square)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean4-zero--sorry-brightgreen?style=flat-square)](Erdos307.lean)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.14.0-informational?style=flat-square)](lakefile.lean)
[![WORM Sealed](https://img.shields.io/badge/WORM-sealed-blueviolet?style=flat-square)](LICENSE)

**Author:** Ahmad Ali Parr  
**Trust:** Bel Esprit D'Accord Irrevocable Trust · EIN 42-697643  
**Sealed:** 2026-07-23

> For any two finite sets P, Q of prime numbers:
> **(∑ p⁻¹ for p ∈ P) × (∑ q⁻¹ for q ∈ Q) ≠ 1**

---

## Theorems

### `erdos_307.barrier_le_11` — ZERO SORRY

Primes ≤ 11: universe `{2, 3, 5, 7, 11}`, 32×32 = **1,024 pairs**.

```lean
theorem erdos_307.barrier_le_11
    {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ 11)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ 11) :
    1 ≠ (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)
```

**Proof:** reduce P, Q to subsets of `{2,3,5,7,11}` via `interval_cases`, then `decide` over all 1,024 pairs using exact ℚ arithmetic. Executes in < 10ms.

### `erdos_307.barrier_le_19` — ZERO SORRY

Primes ≤ 19: universe `{2, 3, 5, 7, 11, 13, 17, 19}`, 256×256 = **65,536 pairs**.

**Proof:** layered verification:
1. Subset reduction via `interval_cases`
2. `no_subset_sums_to_one_le_19` — no subset sums to exactly 1 (256 checks via `decide`)
3. Monotonicity pruning — `rcases lt_or_gt_of_ne` splits on sum < 1 / sum > 1
4. `decide` on each branch

---

## Verification Strategy

```
Layer 1 (Abstract)    — interval_cases reduces to finite universe
Layer 2 (Decidable)   — decide over 2^n subsets, exact ℚ arithmetic
Layer 3 (Integration) — by_cases / rcases combines branches
```

**Scaling:**

| Bound | Universe | Pairs | Method |
|-------|----------|-------|--------|
| ≤ 11 | 5 primes | 1,024 | direct `decide` |
| ≤ 19 | 8 primes | 65,536 | pruning + `decide` |
| ≤ 29 | 10 primes | ~1M | hybrid (certificate-based) |

**The denominator explosion problem:** raw `decide` at n=8 is feasible; at n=10 the LCM of primes becomes astronomically large. Monotonicity pruning avoids this by proving size bounds analytically first.

---

## Build

```bash
lake update
lake build
```

Requires Lean 4.14.0 + Mathlib v4.14.0.

---

## Prior Art

- Trust: Bel Esprit D'Accord Irrevocable Trust (EIN 42-697643)  
- Chain: `BEL-ESPRIT-D-ACCORD-TRUST-HOLDINGS/erdos-307-lean4` (private)  
- Zenodo: DOI 10.5281/zenodo.21268911  
- Sealed: 2026-07-23 · WORM: Ed25519 + Blake3

---

© 2026 Bel Esprit D'Accord Irrevocable Trust · SNAPKITTYWEST

NO MATHLIB 
