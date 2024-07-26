# Operations on spans

```agda
module foundation.operations-spansᵉ where

open import foundation-core.operations-spansᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalences-arrowsᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.spansᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
```

</details>

## Idea

Thisᵉ fileᵉ containsᵉ someᵉ furtherᵉ operationsᵉ onᵉ [spans](foundation.spans.mdᵉ) thatᵉ
produceᵉ newᵉ spansᵉ fromᵉ givenᵉ spansᵉ andᵉ possiblyᵉ otherᵉ data.ᵉ Previousᵉ operationsᵉ
onᵉ spansᵉ wereᵉ definedᵉ in
[`foundation-core.operations-spans`](foundation-core.operations-spans.md).ᵉ

## Definitions

### Concatenating spans and equivalences of arrows on the left

Considerᵉ aᵉ spanᵉ `s`ᵉ givenᵉ byᵉ

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

Thenᵉ weᵉ obtainᵉ aᵉ spanᵉ `A'ᵉ <-ᵉ S'ᵉ ->ᵉ B`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (sᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ)
  {S'ᵉ : UUᵉ l4ᵉ} {A'ᵉ : UUᵉ l5ᵉ} (f'ᵉ : S'ᵉ → A'ᵉ)
  (hᵉ : equiv-arrowᵉ f'ᵉ (left-map-spanᵉ sᵉ))
  where

  spanning-type-left-concat-equiv-arrow-spanᵉ : UUᵉ l4ᵉ
  spanning-type-left-concat-equiv-arrow-spanᵉ = S'ᵉ

  left-map-left-concat-equiv-arrow-spanᵉ :
    spanning-type-left-concat-equiv-arrow-spanᵉ → A'ᵉ
  left-map-left-concat-equiv-arrow-spanᵉ = f'ᵉ

  right-map-left-concat-equiv-arrow-spanᵉ :
    spanning-type-left-concat-equiv-arrow-spanᵉ → Bᵉ
  right-map-left-concat-equiv-arrow-spanᵉ =
    ( right-map-spanᵉ sᵉ) ∘ᵉ
    ( map-domain-equiv-arrowᵉ f'ᵉ (left-map-spanᵉ sᵉ) hᵉ)

  left-concat-equiv-arrow-spanᵉ :
    spanᵉ l4ᵉ A'ᵉ Bᵉ
  pr1ᵉ left-concat-equiv-arrow-spanᵉ =
    spanning-type-left-concat-equiv-arrow-spanᵉ
  pr1ᵉ (pr2ᵉ left-concat-equiv-arrow-spanᵉ) =
    left-map-left-concat-equiv-arrow-spanᵉ
  pr2ᵉ (pr2ᵉ left-concat-equiv-arrow-spanᵉ) =
    right-map-left-concat-equiv-arrow-spanᵉ
```

### Concatenating spans and equivalences of arrows on the right

Considerᵉ aᵉ spanᵉ `s`ᵉ givenᵉ byᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

andᵉ aᵉ [morphismᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) `hᵉ : hom-arrowᵉ g'ᵉ g`ᵉ
asᵉ indicatedᵉ in theᵉ diagramᵉ

```text
               g'ᵉ
           S'ᵉ ---->ᵉ B'ᵉ
           |        |
        h₀ᵉ | ≃ᵉ    ≃ᵉ | h₁ᵉ
           ∨ᵉ        ∨ᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ B.ᵉ
       fᵉ       gᵉ
```

Thenᵉ weᵉ obtainᵉ aᵉ spanᵉ `Aᵉ <-ᵉ S'ᵉ ->ᵉ B'`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (sᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ)
  {S'ᵉ : UUᵉ l4ᵉ} {B'ᵉ : UUᵉ l5ᵉ} (g'ᵉ : S'ᵉ → B'ᵉ)
  (hᵉ : equiv-arrowᵉ g'ᵉ (right-map-spanᵉ sᵉ))
  where

  spanning-type-right-concat-equiv-arrow-spanᵉ : UUᵉ l4ᵉ
  spanning-type-right-concat-equiv-arrow-spanᵉ = S'ᵉ

  left-map-right-concat-equiv-arrow-spanᵉ :
    spanning-type-right-concat-equiv-arrow-spanᵉ → Aᵉ
  left-map-right-concat-equiv-arrow-spanᵉ =
    ( left-map-spanᵉ sᵉ) ∘ᵉ
    ( map-domain-equiv-arrowᵉ g'ᵉ (right-map-spanᵉ sᵉ) hᵉ)

  right-map-right-concat-equiv-arrow-spanᵉ :
    spanning-type-right-concat-equiv-arrow-spanᵉ → B'ᵉ
  right-map-right-concat-equiv-arrow-spanᵉ = g'ᵉ

  right-concat-equiv-arrow-spanᵉ :
    spanᵉ l4ᵉ Aᵉ B'ᵉ
  pr1ᵉ right-concat-equiv-arrow-spanᵉ =
    spanning-type-right-concat-equiv-arrow-spanᵉ
  pr1ᵉ (pr2ᵉ right-concat-equiv-arrow-spanᵉ) =
    left-map-right-concat-equiv-arrow-spanᵉ
  pr2ᵉ (pr2ᵉ right-concat-equiv-arrow-spanᵉ) =
    right-map-right-concat-equiv-arrow-spanᵉ
```