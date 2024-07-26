# Mere logical equivalences

```agda
module foundation.mere-logical-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunctionᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.mere-functionsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Twoᵉ typesᵉ `A`ᵉ andᵉ `B`ᵉ areᵉ
{{#conceptᵉ "merelyᵉ logicallyᵉ equivalent"ᵉ Disambiguation="types"ᵉ Agda=mere-iffᵉ}}
ifᵉ theᵉ typeᵉ ofᵉ [logicalᵉ equivalences](foundation.logical-equivalences.mdᵉ)
betweenᵉ `A`ᵉ andᵉ `B`ᵉ isᵉ [inhabited](foundation.inhabited-types.md).ᵉ

```text
  mere-iffᵉ Aᵉ Bᵉ :=ᵉ ║(Aᵉ ↔ᵉ B)║₋₁ᵉ
```

## Definitions

### Mere logical equivalence of types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  prop-mere-iffᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  prop-mere-iffᵉ = trunc-Propᵉ (Aᵉ ↔ᵉ Bᵉ)

  mere-iffᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  mere-iffᵉ = type-Propᵉ prop-mere-iffᵉ

  is-prop-mere-iffᵉ : is-propᵉ mere-iffᵉ
  is-prop-mere-iffᵉ = is-prop-type-Propᵉ prop-mere-iffᵉ
```

## Properties

### Mere logical equivalence is a reflexive relation

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  refl-mere-iffᵉ : mere-iffᵉ Aᵉ Aᵉ
  refl-mere-iffᵉ = unit-trunc-Propᵉ id-iffᵉ
```

### Mere logical equivalence is a transitive relation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  transitive-mere-iffᵉ : mere-iffᵉ Bᵉ Cᵉ → mere-iffᵉ Aᵉ Bᵉ → mere-iffᵉ Aᵉ Cᵉ
  transitive-mere-iffᵉ |g|ᵉ =
    rec-trunc-Propᵉ
      ( prop-mere-iffᵉ Aᵉ Cᵉ)
      ( λ fᵉ →
        rec-trunc-Propᵉ
          ( prop-mere-iffᵉ Aᵉ Cᵉ)
          ( λ gᵉ → unit-trunc-Propᵉ (gᵉ ∘iffᵉ fᵉ))
          ( |g|ᵉ))
```

### Mere logical equivalence is a symmetric relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  symmetric-mere-iffᵉ : mere-iffᵉ Aᵉ Bᵉ → mere-iffᵉ Bᵉ Aᵉ
  symmetric-mere-iffᵉ =
    rec-trunc-Propᵉ (prop-mere-iffᵉ Bᵉ Aᵉ) (unit-trunc-Propᵉ ∘ᵉ inv-iffᵉ)
```

### Merely logically equivalent types are coinhabited

Ifᵉ `A`ᵉ andᵉ `B`ᵉ areᵉ merelyᵉ logicallyᵉ equivalentᵉ thenᵉ theyᵉ areᵉ
[coinhabited](foundation.coinhabited-pairs-of-types.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  ev-forward-mere-iff'ᵉ : mere-iffᵉ Aᵉ Bᵉ → Aᵉ → is-inhabitedᵉ Bᵉ
  ev-forward-mere-iff'ᵉ |f|ᵉ aᵉ =
    rec-trunc-Propᵉ
      ( trunc-Propᵉ Bᵉ)
      ( λ fᵉ → unit-trunc-Propᵉ (forward-implicationᵉ fᵉ aᵉ))
      ( |f|ᵉ)

  ev-forward-mere-iffᵉ : mere-iffᵉ Aᵉ Bᵉ → is-inhabitedᵉ Aᵉ → is-inhabitedᵉ Bᵉ
  ev-forward-mere-iffᵉ |f|ᵉ =
    rec-trunc-Propᵉ (trunc-Propᵉ Bᵉ) (ev-forward-mere-iff'ᵉ |f|ᵉ)

  ev-backward-mere-iff'ᵉ : mere-iffᵉ Aᵉ Bᵉ → Bᵉ → is-inhabitedᵉ Aᵉ
  ev-backward-mere-iff'ᵉ |f|ᵉ bᵉ =
    rec-trunc-Propᵉ
      ( trunc-Propᵉ Aᵉ)
      ( λ fᵉ → unit-trunc-Propᵉ (backward-implicationᵉ fᵉ bᵉ))
      ( |f|ᵉ)

  ev-backward-mere-iffᵉ : mere-iffᵉ Aᵉ Bᵉ → is-inhabitedᵉ Bᵉ → is-inhabitedᵉ Aᵉ
  ev-backward-mere-iffᵉ |f|ᵉ =
    rec-trunc-Propᵉ (trunc-Propᵉ Aᵉ) (ev-backward-mere-iff'ᵉ |f|ᵉ)

  is-coinhabited-mere-iffᵉ : mere-iffᵉ Aᵉ Bᵉ → is-inhabitedᵉ Aᵉ ↔ᵉ is-inhabitedᵉ Bᵉ
  is-coinhabited-mere-iffᵉ |f|ᵉ =
    ( ev-forward-mere-iffᵉ |f|ᵉ ,ᵉ ev-backward-mere-iffᵉ |f|ᵉ)
```

### Merely logically equivalent types have bidirectional mere functions

Ifᵉ `A`ᵉ andᵉ `B`ᵉ areᵉ merelyᵉ logicallyᵉ equivalentᵉ thenᵉ weᵉ haveᵉ aᵉ mereᵉ functionᵉ fromᵉ
`A`ᵉ to `B`ᵉ andᵉ aᵉ mereᵉ functionᵉ fromᵉ `B`ᵉ to `A`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  forward-mere-function-mere-iffᵉ : mere-iffᵉ Aᵉ Bᵉ → mere-functionᵉ Aᵉ Bᵉ
  forward-mere-function-mere-iffᵉ =
    rec-trunc-Propᵉ
      ( prop-mere-functionᵉ Aᵉ Bᵉ)
      ( unit-trunc-Propᵉ ∘ᵉ forward-implicationᵉ)

  backward-mere-function-mere-iffᵉ : mere-iffᵉ Aᵉ Bᵉ → mere-functionᵉ Bᵉ Aᵉ
  backward-mere-function-mere-iffᵉ =
    rec-trunc-Propᵉ
      ( prop-mere-functionᵉ Bᵉ Aᵉ)
      ( unit-trunc-Propᵉ ∘ᵉ backward-implicationᵉ)
```

### Mere logical equivalence is equivalent to having bidirectional mere functions

Forᵉ allᵉ typesᵉ weᵉ haveᵉ theᵉ equivalenceᵉ

```text
  (mere-iffᵉ Aᵉ Bᵉ) ≃ᵉ (mere-functionᵉ Aᵉ Bᵉ ×ᵉ mere-functionᵉ Bᵉ A).ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  compute-mere-iffᵉ :
    mere-iffᵉ Aᵉ Bᵉ ≃ᵉ mere-functionᵉ Aᵉ Bᵉ ×ᵉ mere-functionᵉ Bᵉ Aᵉ
  compute-mere-iffᵉ = equiv-product-trunc-Propᵉ (Aᵉ → Bᵉ) (Bᵉ → Aᵉ)
```

## See also

-ᵉ [Mereᵉ functions](foundation.mere-functions.mdᵉ)
-ᵉ [Coinhabitedness](foundation.coinhabited-pairs-of-types.mdᵉ) isᵉ aᵉ relatedᵉ butᵉ
  weakerᵉ notionᵉ thanᵉ mereᵉ logicalᵉ equivalence.ᵉ