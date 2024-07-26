# Skipping elements in standard finite types

```agda
module univalent-combinatorics.skipping-element-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

```agda
skip-Finᵉ :
  (kᵉ : ℕᵉ) → Finᵉ (succ-ℕᵉ kᵉ) → Finᵉ kᵉ → Finᵉ (succ-ℕᵉ kᵉ)
skip-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) = inlᵉ (skip-Finᵉ kᵉ xᵉ yᵉ)
skip-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ yᵉ) = inrᵉ starᵉ
skip-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) yᵉ = inlᵉ yᵉ

abstract
  is-injective-skip-Finᵉ :
    (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → is-injectiveᵉ (skip-Finᵉ kᵉ xᵉ)
  is-injective-skip-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) {inlᵉ yᵉ} {inlᵉ zᵉ} pᵉ =
    apᵉ
      ( inlᵉ)
      ( is-injective-skip-Finᵉ kᵉ xᵉ
        ( is-injective-is-embᵉ (is-emb-inlᵉ (Finᵉ (succ-ℕᵉ kᵉ)) unitᵉ) pᵉ))
  is-injective-skip-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) {inrᵉ starᵉ} {inrᵉ starᵉ} pᵉ = reflᵉ
  is-injective-skip-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) {yᵉ} {zᵉ} pᵉ =
    is-injective-is-embᵉ (is-emb-inlᵉ (Finᵉ (succ-ℕᵉ kᵉ)) unitᵉ) pᵉ

abstract
  is-emb-skip-Finᵉ :
    (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → is-embᵉ (skip-Finᵉ kᵉ xᵉ)
  is-emb-skip-Finᵉ kᵉ xᵉ =
    is-emb-is-injectiveᵉ
      ( is-set-Finᵉ (succ-ℕᵉ kᵉ))
      ( is-injective-skip-Finᵉ kᵉ xᵉ)

emb-skip-Finᵉ : (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → Finᵉ kᵉ ↪ᵉ Finᵉ (succ-ℕᵉ kᵉ)
pr1ᵉ (emb-skip-Finᵉ kᵉ xᵉ) = skip-Finᵉ kᵉ xᵉ
pr2ᵉ (emb-skip-Finᵉ kᵉ xᵉ) = is-emb-skip-Finᵉ kᵉ xᵉ
```