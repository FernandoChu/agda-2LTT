# Commuting squares of order preserving maps of large posets

```agda
module
  order-theory.commuting-squares-of-order-preserving-maps-large-posetsᵉ
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-mapsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.similarity-of-order-preserving-maps-large-posetsᵉ
```

</details>

## Idea

Aᵉ squareᵉ

```text
        iᵉ
    Pᵉ ----->ᵉ Uᵉ
    |        |
  fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Qᵉ ----->ᵉ Vᵉ
        jᵉ
```

ofᵉ [orderᵉ preservingᵉ maps](order-theory.order-preserving-maps-large-posets.mdᵉ)
betweenᵉ [largeᵉ posets](order-theory.large-posets.mdᵉ) isᵉ saidᵉ to **commute**ᵉ ifᵉ
forᵉ eachᵉ `xᵉ : type-Large-Posetᵉ Pᵉ l`ᵉ theᵉ elementsᵉ

```text
  jᵉ (fᵉ xᵉ) : type-Large-Posetᵉ Vᵉ (γjᵉ (γfᵉ lᵉ))
  gᵉ (iᵉ xᵉ) : type-Large-Posetᵉ Vᵉ (γgᵉ (γiᵉ lᵉ))
```

areᵉ [similar](order-theory.similarity-of-elements-large-posets.md).ᵉ Inᵉ otherᵉ
words,ᵉ weᵉ sayᵉ thatᵉ theᵉ squareᵉ aboveᵉ commutesᵉ ifᵉ theᵉ compositesᵉ `jᵉ ∘ᵉ f`ᵉ andᵉ
`gᵉ ∘ᵉ i`ᵉ areᵉ
[similar](order-theory.similarity-of-order-preserving-maps-large-posets.md).ᵉ

## Definitions

```agda
module _
  {αPᵉ αQᵉ αUᵉ αVᵉ γiᵉ γfᵉ γgᵉ γjᵉ : Level → Level}
  {βPᵉ βQᵉ βUᵉ βVᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Uᵉ : Large-Posetᵉ αUᵉ βUᵉ)
  (Vᵉ : Large-Posetᵉ αVᵉ βVᵉ)
  (iᵉ : hom-Large-Posetᵉ γiᵉ Pᵉ Uᵉ)
  (fᵉ : hom-Large-Posetᵉ γfᵉ Pᵉ Qᵉ)
  (gᵉ : hom-Large-Posetᵉ γgᵉ Uᵉ Vᵉ)
  (jᵉ : hom-Large-Posetᵉ γjᵉ Qᵉ Vᵉ)
  where

  coherence-square-hom-Large-Posetᵉ : UUωᵉ
  coherence-square-hom-Large-Posetᵉ =
    sim-hom-Large-Posetᵉ Pᵉ Vᵉ
      ( comp-hom-Large-Posetᵉ Pᵉ Qᵉ Vᵉ jᵉ fᵉ)
      ( comp-hom-Large-Posetᵉ Pᵉ Uᵉ Vᵉ gᵉ iᵉ)
```