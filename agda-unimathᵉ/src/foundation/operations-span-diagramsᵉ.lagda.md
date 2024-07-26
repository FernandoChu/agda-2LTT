# Operations on span diagrams

```agda
module foundation.operations-span-diagramsᵉ where

open import foundation-core.operations-span-diagramsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalences-arrowsᵉ
open import foundation.operations-spansᵉ
open import foundation.span-diagramsᵉ
open import foundation.spansᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Thisᵉ fileᵉ containsᵉ someᵉ furtherᵉ operationsᵉ onᵉ
[spanᵉ diagrams](foundation.span-diagrams.mdᵉ) thatᵉ produceᵉ newᵉ spanᵉ diagramsᵉ fromᵉ
givenᵉ spanᵉ diagramsᵉ andᵉ possiblyᵉ otherᵉ data.ᵉ Previousᵉ operationsᵉ onᵉ spanᵉ
diagramsᵉ wereᵉ definedᵉ in
[`foundation-core.operations-span-diagrams`](foundation-core.operations-span-diagrams.md).ᵉ

## Definitions

### Concatenating span diagrams and equivalences of arrows on the left

Considerᵉ aᵉ spanᵉ diagramᵉ `𝒮`ᵉ givenᵉ byᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

andᵉ anᵉ [equivalenceᵉ ofᵉ arrows](foundation.equivalences-arrows.mdᵉ)
`hᵉ : equiv-arrowᵉ f'ᵉ f`ᵉ asᵉ indicatedᵉ in theᵉ diagramᵉ

```text
          f'ᵉ
     A'ᵉ <----ᵉ S'ᵉ
     |        |
  h₀ᵉ | ≃ᵉ    ≃ᵉ | h₁ᵉ
     ∨ᵉ        ∨ᵉ
     Aᵉ <-----ᵉ Sᵉ ----->ᵉ B.ᵉ
          fᵉ       gᵉ
```

Thenᵉ weᵉ obtainᵉ aᵉ spanᵉ diagramᵉ `A'ᵉ <-ᵉ S'ᵉ ->ᵉ B`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  {S'ᵉ : UUᵉ l4ᵉ} {A'ᵉ : UUᵉ l5ᵉ} (f'ᵉ : S'ᵉ → A'ᵉ)
  (hᵉ : equiv-arrowᵉ f'ᵉ (left-map-span-diagramᵉ 𝒮ᵉ))
  where

  domain-left-concat-equiv-arrow-span-diagramᵉ : UUᵉ l5ᵉ
  domain-left-concat-equiv-arrow-span-diagramᵉ = A'ᵉ

  codomain-left-concat-equiv-arrow-span-diagramᵉ : UUᵉ l2ᵉ
  codomain-left-concat-equiv-arrow-span-diagramᵉ = codomain-span-diagramᵉ 𝒮ᵉ

  span-left-concat-equiv-arrow-span-diagramᵉ :
    spanᵉ l4ᵉ
      ( domain-left-concat-equiv-arrow-span-diagramᵉ)
      ( codomain-left-concat-equiv-arrow-span-diagramᵉ)
  span-left-concat-equiv-arrow-span-diagramᵉ =
    left-concat-equiv-arrow-spanᵉ (span-span-diagramᵉ 𝒮ᵉ) f'ᵉ hᵉ

  left-concat-equiv-arrow-span-diagramᵉ : span-diagramᵉ l5ᵉ l2ᵉ l4ᵉ
  pr1ᵉ left-concat-equiv-arrow-span-diagramᵉ =
    domain-left-concat-equiv-arrow-span-diagramᵉ
  pr1ᵉ (pr2ᵉ left-concat-equiv-arrow-span-diagramᵉ) =
    codomain-left-concat-equiv-arrow-span-diagramᵉ
  pr2ᵉ (pr2ᵉ left-concat-equiv-arrow-span-diagramᵉ) =
    span-left-concat-equiv-arrow-span-diagramᵉ

  spanning-type-left-concat-equiv-arrow-span-diagramᵉ : UUᵉ l4ᵉ
  spanning-type-left-concat-equiv-arrow-span-diagramᵉ =
    spanning-type-span-diagramᵉ left-concat-equiv-arrow-span-diagramᵉ

  left-map-left-concat-equiv-arrow-span-diagramᵉ :
    spanning-type-left-concat-equiv-arrow-span-diagramᵉ →
    domain-left-concat-equiv-arrow-span-diagramᵉ
  left-map-left-concat-equiv-arrow-span-diagramᵉ =
    left-map-span-diagramᵉ left-concat-equiv-arrow-span-diagramᵉ

  right-map-left-concat-equiv-arrow-span-diagramᵉ :
    spanning-type-left-concat-equiv-arrow-span-diagramᵉ →
    codomain-left-concat-equiv-arrow-span-diagramᵉ
  right-map-left-concat-equiv-arrow-span-diagramᵉ =
    right-map-span-diagramᵉ left-concat-equiv-arrow-span-diagramᵉ
```

### Concatenating span diagrams and equivalences of arrows on the right

Considerᵉ aᵉ spanᵉ diagramᵉ `𝒮`ᵉ givenᵉ byᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

andᵉ aᵉ [equivalenceᵉ ofᵉ arrows](foundation.equivalences-arrows.mdᵉ)
`hᵉ : equiv-arrowᵉ g'ᵉ g`ᵉ asᵉ indicatedᵉ in theᵉ diagramᵉ

```text
               g'ᵉ
           S'ᵉ ---->ᵉ B'ᵉ
           |        |
        h₀ᵉ | ≃ᵉ    ≃ᵉ | h₁ᵉ
           ∨ᵉ        ∨ᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ B.ᵉ
       fᵉ       gᵉ
```

Thenᵉ weᵉ obtainᵉ aᵉ spanᵉ diagramᵉ `Aᵉ <-ᵉ S'ᵉ ->ᵉ B'`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  {S'ᵉ : UUᵉ l4ᵉ} {B'ᵉ : UUᵉ l5ᵉ} (g'ᵉ : S'ᵉ → B'ᵉ)
  (hᵉ : equiv-arrowᵉ g'ᵉ (right-map-span-diagramᵉ 𝒮ᵉ))
  where

  domain-right-concat-equiv-arrow-span-diagramᵉ : UUᵉ l1ᵉ
  domain-right-concat-equiv-arrow-span-diagramᵉ = domain-span-diagramᵉ 𝒮ᵉ

  codomain-right-concat-equiv-arrow-span-diagramᵉ : UUᵉ l5ᵉ
  codomain-right-concat-equiv-arrow-span-diagramᵉ = B'ᵉ

  span-right-concat-equiv-arrow-span-diagramᵉ :
    spanᵉ l4ᵉ
      ( domain-right-concat-equiv-arrow-span-diagramᵉ)
      ( codomain-right-concat-equiv-arrow-span-diagramᵉ)
  span-right-concat-equiv-arrow-span-diagramᵉ =
    right-concat-equiv-arrow-spanᵉ (span-span-diagramᵉ 𝒮ᵉ) g'ᵉ hᵉ

  right-concat-equiv-arrow-span-diagramᵉ : span-diagramᵉ l1ᵉ l5ᵉ l4ᵉ
  pr1ᵉ right-concat-equiv-arrow-span-diagramᵉ =
    domain-right-concat-equiv-arrow-span-diagramᵉ
  pr1ᵉ (pr2ᵉ right-concat-equiv-arrow-span-diagramᵉ) =
    codomain-right-concat-equiv-arrow-span-diagramᵉ
  pr2ᵉ (pr2ᵉ right-concat-equiv-arrow-span-diagramᵉ) =
    span-right-concat-equiv-arrow-span-diagramᵉ

  spanning-type-right-concat-equiv-arrow-span-diagramᵉ : UUᵉ l4ᵉ
  spanning-type-right-concat-equiv-arrow-span-diagramᵉ =
    spanning-type-span-diagramᵉ right-concat-equiv-arrow-span-diagramᵉ

  left-map-right-concat-equiv-arrow-span-diagramᵉ :
    spanning-type-right-concat-equiv-arrow-span-diagramᵉ →
    domain-right-concat-equiv-arrow-span-diagramᵉ
  left-map-right-concat-equiv-arrow-span-diagramᵉ =
    left-map-span-diagramᵉ right-concat-equiv-arrow-span-diagramᵉ

  right-map-right-concat-equiv-arrow-span-diagramᵉ :
    spanning-type-right-concat-equiv-arrow-span-diagramᵉ →
    codomain-right-concat-equiv-arrow-span-diagramᵉ
  right-map-right-concat-equiv-arrow-span-diagramᵉ =
    right-map-span-diagramᵉ right-concat-equiv-arrow-span-diagramᵉ
```