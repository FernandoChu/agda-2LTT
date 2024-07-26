# Mere functions

```agda
module foundation.mere-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ
{{#conceptᵉ "mereᵉ functions"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=mere-functionᵉ}} fromᵉ
`A`ᵉ to `B`ᵉ isᵉ theᵉ
[propositionalᵉ truncation](foundation.propositional-truncations.mdᵉ) ofᵉ theᵉ typeᵉ
ofᵉ mapsᵉ fromᵉ `A`ᵉ to `B`.ᵉ

```text
  mere-functionᵉ Aᵉ Bᵉ :=ᵉ ║(Aᵉ → B)║₋₁ᵉ
```

## Definitions

### Mere functions between types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  prop-mere-functionᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  prop-mere-functionᵉ = trunc-Propᵉ (Aᵉ → Bᵉ)

  mere-functionᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  mere-functionᵉ = type-Propᵉ prop-mere-functionᵉ

  is-prop-mere-functionᵉ : is-propᵉ mere-functionᵉ
  is-prop-mere-functionᵉ = is-prop-type-Propᵉ prop-mere-functionᵉ
```

### The evaluation map on mere functions

Ifᵉ weᵉ haveᵉ aᵉ mereᵉ functionᵉ fromᵉ `A`ᵉ to `B`ᵉ andᵉ `A`ᵉ isᵉ inhabited,ᵉ thenᵉ `B`ᵉ isᵉ
inhabited.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  ev-mere-function'ᵉ : (mere-functionᵉ Aᵉ Bᵉ) → Aᵉ → ║ᵉ Bᵉ ║₋₁ᵉ
  ev-mere-function'ᵉ |f|ᵉ aᵉ =
    rec-trunc-Propᵉ (trunc-Propᵉ Bᵉ) (λ fᵉ → unit-trunc-Propᵉ (fᵉ aᵉ)) |f|ᵉ

  ev-mere-functionᵉ : (mere-functionᵉ Aᵉ Bᵉ) → ║ᵉ Aᵉ ║₋₁ᵉ → ║ᵉ Bᵉ ║₋₁ᵉ
  ev-mere-functionᵉ |f|ᵉ |a|ᵉ =
    rec-trunc-Propᵉ (trunc-Propᵉ Bᵉ) (ev-mere-function'ᵉ |f|ᵉ) (|a|ᵉ)
```

### Mere functions form a reflexive relation

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  refl-mere-functionᵉ : mere-functionᵉ Aᵉ Aᵉ
  refl-mere-functionᵉ = unit-trunc-Propᵉ idᵉ
```

### Mere functions form a transitive relation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  transitive-mere-functionᵉ :
    mere-functionᵉ Bᵉ Cᵉ → mere-functionᵉ Aᵉ Bᵉ → mere-functionᵉ Aᵉ Cᵉ
  transitive-mere-functionᵉ |g|ᵉ =
    rec-trunc-Propᵉ
      ( prop-mere-functionᵉ Aᵉ Cᵉ)
      ( λ fᵉ →
        rec-trunc-Propᵉ
          ( prop-mere-functionᵉ Aᵉ Cᵉ)
          ( λ gᵉ → unit-trunc-Propᵉ (gᵉ ∘ᵉ fᵉ))
          ( |g|ᵉ))
```

## See also

-ᵉ [Mereᵉ logicalᵉ equivalences](foundation.mere-logical-equivalences.mdᵉ)