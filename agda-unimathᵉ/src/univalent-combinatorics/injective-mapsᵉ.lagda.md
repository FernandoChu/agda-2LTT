# Injective maps between finite types

```agda
module univalent-combinatorics.injective-mapsᵉ where

open import foundation.injective-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.decidable-dependent-function-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Injectivenessᵉ in theᵉ contextᵉ ofᵉ finiteᵉ typesᵉ enjoysᵉ furtherᵉ properties.ᵉ

## Properties

```agda
is-decidable-is-injective-is-finite'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-finiteᵉ Aᵉ → is-finiteᵉ Bᵉ → is-decidableᵉ ((xᵉ yᵉ : Aᵉ) → Idᵉ (fᵉ xᵉ) (fᵉ yᵉ) → Idᵉ xᵉ yᵉ)
is-decidable-is-injective-is-finite'ᵉ fᵉ HAᵉ HBᵉ =
  is-decidable-Π-is-finiteᵉ HAᵉ
    ( λ xᵉ →
      is-decidable-Π-is-finiteᵉ HAᵉ
        ( λ yᵉ →
          is-decidable-function-typeᵉ
            ( has-decidable-equality-is-finiteᵉ HBᵉ (fᵉ xᵉ) (fᵉ yᵉ))
            ( has-decidable-equality-is-finiteᵉ HAᵉ xᵉ yᵉ)))

is-decidable-is-injective-is-finiteᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-finiteᵉ Aᵉ → is-finiteᵉ Bᵉ → is-decidableᵉ (is-injectiveᵉ fᵉ)
is-decidable-is-injective-is-finiteᵉ fᵉ HAᵉ HBᵉ =
  is-decidable-iffᵉ
    ( λ pᵉ {xᵉ} {yᵉ} → pᵉ xᵉ yᵉ)
    ( λ pᵉ xᵉ yᵉ → pᵉ)
    ( is-decidable-is-injective-is-finite'ᵉ fᵉ HAᵉ HBᵉ)
```