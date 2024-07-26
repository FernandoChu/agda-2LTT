# Constant span diagrams

```agda
module foundation.constant-span-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.span-diagramsᵉ
open import foundation.spansᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "constantᵉ spanᵉ diagram"ᵉ Agda=constant-span-diagramᵉ}} atᵉ aᵉ typeᵉ
`X`ᵉ isᵉ theᵉ [spanᵉ diagram](foundation.span-diagrams.mdᵉ)

```text
      idᵉ       idᵉ
  Xᵉ <-----ᵉ Xᵉ ----->ᵉ X.ᵉ
```

Alternatively,ᵉ aᵉ spanᵉ diagramᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

isᵉ saidᵉ to beᵉ constantᵉ ifᵉ bothᵉ `f`ᵉ andᵉ `g`ᵉ areᵉ
[equivalences](foundation-core.equivalences.md).ᵉ

## Definitions

### Constant span diagrams at a type

```agda
module _
  {l1ᵉ : Level}
  where

  constant-span-diagramᵉ : UUᵉ l1ᵉ → span-diagramᵉ l1ᵉ l1ᵉ l1ᵉ
  pr1ᵉ (constant-span-diagramᵉ Xᵉ) = Xᵉ
  pr1ᵉ (pr2ᵉ (constant-span-diagramᵉ Xᵉ)) = Xᵉ
  pr2ᵉ (pr2ᵉ (constant-span-diagramᵉ Xᵉ)) = id-spanᵉ
```

### The predicate of being a constant span diagram

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  is-constant-span-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-constant-span-diagramᵉ =
    is-equivᵉ (left-map-span-diagramᵉ 𝒮ᵉ) ×ᵉ is-equivᵉ (right-map-span-diagramᵉ 𝒮ᵉ)
```