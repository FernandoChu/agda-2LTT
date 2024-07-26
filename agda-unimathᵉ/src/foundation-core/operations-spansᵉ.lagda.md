# Operations on spans

```agda
module foundation-core.operations-spansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.spansᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
```

</details>

## Idea

Thisᵉ fileᵉ containsᵉ someᵉ operationsᵉ onᵉ [spans](foundation.spans.mdᵉ) thatᵉ produceᵉ
newᵉ spansᵉ fromᵉ givenᵉ spansᵉ andᵉ possiblyᵉ otherᵉ data.ᵉ

## Definitions

### Concatenating spans and maps on both sides

Considerᵉ aᵉ [span](foundation.spans.mdᵉ) `s`ᵉ givenᵉ byᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

andᵉ mapsᵉ `iᵉ : Aᵉ → A'`ᵉ andᵉ `jᵉ : Bᵉ → B'`.ᵉ Theᵉ
{{#conceptᵉ "concatenationᵉ span"ᵉ Disambiguation="span"ᵉ Agda=concat-spanᵉ}} ofᵉ `i`,ᵉ
`s`,ᵉ andᵉ `j`ᵉ isᵉ theᵉ spanᵉ

```text
       iᵉ ∘ᵉ fᵉ     jᵉ ∘ᵉ gᵉ
  A'ᵉ <-------ᵉ Sᵉ ------->ᵉ B.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {A'ᵉ : UUᵉ l2ᵉ}
  {Bᵉ : UUᵉ l3ᵉ} {B'ᵉ : UUᵉ l4ᵉ}
  where

  concat-spanᵉ : spanᵉ l5ᵉ Aᵉ Bᵉ → (Aᵉ → A'ᵉ) → (Bᵉ → B'ᵉ) → spanᵉ l5ᵉ A'ᵉ B'ᵉ
  pr1ᵉ (concat-spanᵉ sᵉ iᵉ jᵉ) = spanning-type-spanᵉ sᵉ
  pr1ᵉ (pr2ᵉ (concat-spanᵉ sᵉ iᵉ jᵉ)) = iᵉ ∘ᵉ left-map-spanᵉ sᵉ
  pr2ᵉ (pr2ᵉ (concat-spanᵉ sᵉ iᵉ jᵉ)) = jᵉ ∘ᵉ right-map-spanᵉ sᵉ
```

### Concatenating spans and maps on the left

Considerᵉ aᵉ [span](foundation.spans.mdᵉ) `s`ᵉ givenᵉ byᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

andᵉ aᵉ mapᵉ `iᵉ : Aᵉ → A'`.ᵉ Theᵉ
{{#conceptᵉ "leftᵉ concatenation"ᵉ Disambiguation="span"ᵉ Agda=left-concat-spanᵉ}} ofᵉ
`s`ᵉ byᵉ `i`ᵉ isᵉ theᵉ spanᵉ

```text
       iᵉ ∘ᵉ fᵉ      gᵉ
  A'ᵉ <-------ᵉ Sᵉ ----->ᵉ B.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {A'ᵉ : UUᵉ l2ᵉ}
  {Bᵉ : UUᵉ l3ᵉ}
  where

  left-concat-spanᵉ : spanᵉ l4ᵉ Aᵉ Bᵉ → (Aᵉ → A'ᵉ) → spanᵉ l4ᵉ A'ᵉ Bᵉ
  left-concat-spanᵉ sᵉ fᵉ = concat-spanᵉ sᵉ fᵉ idᵉ
```

### Concatenating spans and maps on the right

Considerᵉ aᵉ [span](foundation.spans.mdᵉ) `s`ᵉ givenᵉ byᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

andᵉ aᵉ mapᵉ `jᵉ : Bᵉ → B'`.ᵉ Theᵉ
{{#conceptᵉ "rightᵉ concatenation"ᵉ Disambiguation="span"ᵉ Agda=right-concat-spanᵉ}}
ofᵉ `s`ᵉ byᵉ `j`ᵉ isᵉ theᵉ spanᵉ

```text
        fᵉ      jᵉ ∘ᵉ gᵉ
  A'ᵉ <-----ᵉ Sᵉ ------->ᵉ B.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ}
  {Bᵉ : UUᵉ l3ᵉ} {B'ᵉ : UUᵉ l4ᵉ}
  where

  right-concat-spanᵉ : spanᵉ l4ᵉ Aᵉ Bᵉ → (Bᵉ → B'ᵉ) → spanᵉ l4ᵉ Aᵉ B'ᵉ
  right-concat-spanᵉ sᵉ gᵉ = concat-spanᵉ sᵉ idᵉ gᵉ
```

### Concatenating spans and morphisms of arrows on the left

Considerᵉ aᵉ spanᵉ `s`ᵉ givenᵉ byᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

andᵉ aᵉ [morphismᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) `hᵉ : hom-arrowᵉ f'ᵉ f`ᵉ
asᵉ indicatedᵉ in theᵉ diagramᵉ

```text
          f'ᵉ
     A'ᵉ <----ᵉ S'ᵉ
     |        |
  h₀ᵉ |        | h₁ᵉ
     ∨ᵉ        ∨ᵉ
     Aᵉ <-----ᵉ Sᵉ ----->ᵉ B.ᵉ
          fᵉ       gᵉ
```

Thenᵉ weᵉ obtainᵉ aᵉ spanᵉ `A'ᵉ <-ᵉ S'ᵉ ->ᵉ B`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (sᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ)
  {S'ᵉ : UUᵉ l4ᵉ} {A'ᵉ : UUᵉ l5ᵉ} (f'ᵉ : S'ᵉ → A'ᵉ) (hᵉ : hom-arrowᵉ f'ᵉ (left-map-spanᵉ sᵉ))
  where

  spanning-type-left-concat-hom-arrow-spanᵉ : UUᵉ l4ᵉ
  spanning-type-left-concat-hom-arrow-spanᵉ = S'ᵉ

  left-map-left-concat-hom-arrow-spanᵉ :
    spanning-type-left-concat-hom-arrow-spanᵉ → A'ᵉ
  left-map-left-concat-hom-arrow-spanᵉ = f'ᵉ

  right-map-left-concat-hom-arrow-spanᵉ :
    spanning-type-left-concat-hom-arrow-spanᵉ → Bᵉ
  right-map-left-concat-hom-arrow-spanᵉ =
    right-map-spanᵉ sᵉ ∘ᵉ map-domain-hom-arrowᵉ f'ᵉ (left-map-spanᵉ sᵉ) hᵉ

  left-concat-hom-arrow-spanᵉ : spanᵉ l4ᵉ A'ᵉ Bᵉ
  pr1ᵉ left-concat-hom-arrow-spanᵉ = spanning-type-left-concat-hom-arrow-spanᵉ
  pr1ᵉ (pr2ᵉ left-concat-hom-arrow-spanᵉ) = left-map-left-concat-hom-arrow-spanᵉ
  pr2ᵉ (pr2ᵉ left-concat-hom-arrow-spanᵉ) = right-map-left-concat-hom-arrow-spanᵉ
```

### Concatenating spans and morphisms of arrows on the right

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
        h₀ᵉ |        | h₁ᵉ
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
  (hᵉ : hom-arrowᵉ g'ᵉ (right-map-spanᵉ sᵉ))
  where

  spanning-type-right-concat-hom-arrow-spanᵉ : UUᵉ l4ᵉ
  spanning-type-right-concat-hom-arrow-spanᵉ = S'ᵉ

  left-map-right-concat-hom-arrow-spanᵉ :
    spanning-type-right-concat-hom-arrow-spanᵉ → Aᵉ
  left-map-right-concat-hom-arrow-spanᵉ =
    left-map-spanᵉ sᵉ ∘ᵉ map-domain-hom-arrowᵉ g'ᵉ (right-map-spanᵉ sᵉ) hᵉ

  right-map-right-concat-hom-arrow-spanᵉ :
    spanning-type-right-concat-hom-arrow-spanᵉ → B'ᵉ
  right-map-right-concat-hom-arrow-spanᵉ = g'ᵉ

  right-concat-hom-arrow-spanᵉ : spanᵉ l4ᵉ Aᵉ B'ᵉ
  pr1ᵉ right-concat-hom-arrow-spanᵉ = spanning-type-right-concat-hom-arrow-spanᵉ
  pr1ᵉ (pr2ᵉ right-concat-hom-arrow-spanᵉ) = left-map-right-concat-hom-arrow-spanᵉ
  pr2ᵉ (pr2ᵉ right-concat-hom-arrow-spanᵉ) = right-map-right-concat-hom-arrow-spanᵉ
```