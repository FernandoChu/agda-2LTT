# Alternating concrete groups

```agda
module finite-group-theory.alternating-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.cartier-delooping-sign-homomorphismᵉ
open import finite-group-theory.finite-type-groupsᵉ

open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.kernels-homomorphisms-concrete-groupsᵉ
```

</details>

## Idea

Theᵉ alternatingᵉ concreteᵉ groupsᵉ areᵉ theᵉ kernelsᵉ ofᵉ theᵉ concreteᵉ signᵉ
homomorphismᵉ

## Definition

```agda
module _
  (nᵉ : ℕᵉ)
  where

  alternating-Concrete-Groupᵉ : Concrete-Groupᵉ (lsuc (lsuc lzeroᵉ))
  alternating-Concrete-Groupᵉ =
    concrete-group-kernel-hom-Concrete-Groupᵉ
      ( UU-Fin-Groupᵉ lzero nᵉ)
      ( UU-Fin-Groupᵉ (lsuc lzero) 2ᵉ)
      ( cartier-delooping-signᵉ nᵉ)
```