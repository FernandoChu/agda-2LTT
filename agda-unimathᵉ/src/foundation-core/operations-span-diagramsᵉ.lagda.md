# Operations on span diagrams

```agda
module foundation-core.operations-span-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.operations-spansᵉ
open import foundation.span-diagramsᵉ
open import foundation.spansᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
```

</details>

## Idea

Thisᵉ fileᵉ containsᵉ someᵉ operationsᵉ onᵉ
[spanᵉ diagrams](foundation.span-diagrams.mdᵉ) thatᵉ produceᵉ newᵉ spanᵉ diagramsᵉ fromᵉ
givenᵉ spanᵉ diagramsᵉ andᵉ possiblyᵉ otherᵉ data.ᵉ

## Definitions

### Concatenating span diagrams and maps on both sides

Considerᵉ aᵉ [spanᵉ diagram](foundation.span-diagrams.mdᵉ) `𝒮`ᵉ givenᵉ byᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

andᵉ mapsᵉ `iᵉ : Aᵉ → A'`ᵉ andᵉ `jᵉ : Bᵉ → B'`.ᵉ Theᵉ
{{#conceptᵉ "concatenation-span-diagram"ᵉ Disambiguation="spanᵉ diagram"ᵉ Agda=concat-span-diagramᵉ}}
ofᵉ `𝒮`,ᵉ `i`,ᵉ andᵉ `j`ᵉ isᵉ theᵉ spanᵉ diagramᵉ

```text
       iᵉ ∘ᵉ fᵉ     jᵉ ∘ᵉ gᵉ
  A'ᵉ <-------ᵉ Sᵉ ------->ᵉ B'.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  where

  concat-span-diagramᵉ :
    (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
    {A'ᵉ : UUᵉ l4ᵉ} (fᵉ : domain-span-diagramᵉ 𝒮ᵉ → A'ᵉ)
    {B'ᵉ : UUᵉ l5ᵉ} (gᵉ : codomain-span-diagramᵉ 𝒮ᵉ → B'ᵉ) →
    span-diagramᵉ l4ᵉ l5ᵉ l3ᵉ
  pr1ᵉ (concat-span-diagramᵉ 𝒮ᵉ {A'ᵉ} fᵉ {B'ᵉ} gᵉ) =
    A'ᵉ
  pr1ᵉ (pr2ᵉ (concat-span-diagramᵉ 𝒮ᵉ {A'ᵉ} fᵉ {B'ᵉ} gᵉ)) =
    B'ᵉ
  pr2ᵉ (pr2ᵉ (concat-span-diagramᵉ 𝒮ᵉ {A'ᵉ} fᵉ {B'ᵉ} gᵉ)) =
    concat-spanᵉ (span-span-diagramᵉ 𝒮ᵉ) fᵉ gᵉ
```

### Concatenating span diagrams and maps on the left

Considerᵉ aᵉ [spanᵉ diagram](foundation.span-diagrams.mdᵉ) `𝒮`ᵉ givenᵉ byᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

andᵉ aᵉ mapᵉ `iᵉ : Aᵉ → A'`.ᵉ Theᵉ
{{#conceptᵉ "leftᵉ concatenation"ᵉ Disambiguation="spanᵉ diagram"ᵉ Agda=left-concat-span-diagramᵉ}}
ofᵉ `𝒮`ᵉ andᵉ `i`ᵉ isᵉ theᵉ spanᵉ diagramᵉ

```text
       iᵉ ∘ᵉ fᵉ      gᵉ
  A'ᵉ <-------ᵉ Sᵉ ----->ᵉ B.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  where

  left-concat-span-diagramᵉ :
    (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ) {A'ᵉ : UUᵉ l4ᵉ} →
    (domain-span-diagramᵉ 𝒮ᵉ → A'ᵉ) → span-diagramᵉ l4ᵉ l2ᵉ l3ᵉ
  left-concat-span-diagramᵉ 𝒮ᵉ fᵉ = concat-span-diagramᵉ 𝒮ᵉ fᵉ idᵉ
```

### Concatenating span diagrams and maps on the right

Considerᵉ aᵉ [spanᵉ diagram](foundation.span-diagrams.mdᵉ) `𝒮`ᵉ givenᵉ byᵉ

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

andᵉ aᵉ mapᵉ `jᵉ : Bᵉ → B'`.ᵉ Theᵉ
{{#conceptᵉ "rightᵉ concatenation"ᵉ Disambiguation="spanᵉ diagram"ᵉ Agda=right-concat-span-diagramᵉ}}
ofᵉ `𝒮`ᵉ byᵉ `j`ᵉ isᵉ theᵉ spanᵉ diagramᵉ

```text
        fᵉ      jᵉ ∘ᵉ gᵉ
  A'ᵉ <-----ᵉ Sᵉ ------->ᵉ B'.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  where

  right-concat-span-diagramᵉ :
    (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ) {B'ᵉ : UUᵉ l4ᵉ} →
    (codomain-span-diagramᵉ 𝒮ᵉ → B'ᵉ) → span-diagramᵉ l1ᵉ l4ᵉ l3ᵉ
  right-concat-span-diagramᵉ 𝒮ᵉ gᵉ = concat-span-diagramᵉ 𝒮ᵉ idᵉ gᵉ
```

### Concatenation of span diagrams and morphisms of arrows on the left

Considerᵉ aᵉ spanᵉ diagramᵉ `𝒮`ᵉ givenᵉ byᵉ

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

Thenᵉ weᵉ obtainᵉ aᵉ spanᵉ diagramᵉ `A'ᵉ <-ᵉ S'ᵉ ->ᵉ B`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  {S'ᵉ : UUᵉ l4ᵉ} {A'ᵉ : UUᵉ l5ᵉ} (f'ᵉ : S'ᵉ → A'ᵉ)
  (hᵉ : hom-arrowᵉ f'ᵉ (left-map-span-diagramᵉ 𝒮ᵉ))
  where

  domain-left-concat-hom-arrow-span-diagramᵉ : UUᵉ l5ᵉ
  domain-left-concat-hom-arrow-span-diagramᵉ = A'ᵉ

  codomain-left-concat-hom-arrow-span-diagramᵉ : UUᵉ l2ᵉ
  codomain-left-concat-hom-arrow-span-diagramᵉ = codomain-span-diagramᵉ 𝒮ᵉ

  span-left-concat-hom-arrow-span-diagramᵉ :
    spanᵉ l4ᵉ
      ( domain-left-concat-hom-arrow-span-diagramᵉ)
      ( codomain-left-concat-hom-arrow-span-diagramᵉ)
  span-left-concat-hom-arrow-span-diagramᵉ =
    left-concat-hom-arrow-spanᵉ
      ( span-span-diagramᵉ 𝒮ᵉ)
      ( f'ᵉ)
      ( hᵉ)

  left-concat-hom-arrow-span-diagramᵉ : span-diagramᵉ l5ᵉ l2ᵉ l4ᵉ
  pr1ᵉ left-concat-hom-arrow-span-diagramᵉ =
    domain-left-concat-hom-arrow-span-diagramᵉ
  pr1ᵉ (pr2ᵉ left-concat-hom-arrow-span-diagramᵉ) =
    codomain-left-concat-hom-arrow-span-diagramᵉ
  pr2ᵉ (pr2ᵉ left-concat-hom-arrow-span-diagramᵉ) =
    span-left-concat-hom-arrow-span-diagramᵉ

  spanning-type-left-concat-hom-arrow-span-diagramᵉ : UUᵉ l4ᵉ
  spanning-type-left-concat-hom-arrow-span-diagramᵉ =
    spanning-type-span-diagramᵉ left-concat-hom-arrow-span-diagramᵉ

  left-map-left-concat-hom-arrow-span-diagramᵉ :
    spanning-type-left-concat-hom-arrow-span-diagramᵉ →
    domain-left-concat-hom-arrow-span-diagramᵉ
  left-map-left-concat-hom-arrow-span-diagramᵉ =
    left-map-span-diagramᵉ left-concat-hom-arrow-span-diagramᵉ

  right-map-left-concat-hom-arrow-span-diagramᵉ :
    spanning-type-left-concat-hom-arrow-span-diagramᵉ →
    codomain-left-concat-hom-arrow-span-diagramᵉ
  right-map-left-concat-hom-arrow-span-diagramᵉ =
    right-map-span-diagramᵉ left-concat-hom-arrow-span-diagramᵉ
```

### Concatenation of span diagrams and morphisms of arrows on the right

Considerᵉ aᵉ spanᵉ diagramᵉ `𝒮`ᵉ givenᵉ byᵉ

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

Thenᵉ weᵉ obtainᵉ aᵉ spanᵉ diagramᵉ `Aᵉ <-ᵉ S'ᵉ ->ᵉ B'`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  {S'ᵉ : UUᵉ l4ᵉ} {B'ᵉ : UUᵉ l5ᵉ} (g'ᵉ : S'ᵉ → B'ᵉ)
  (hᵉ : hom-arrowᵉ g'ᵉ (right-map-span-diagramᵉ 𝒮ᵉ))
  where

  domain-right-concat-hom-arrow-span-diagramᵉ : UUᵉ l1ᵉ
  domain-right-concat-hom-arrow-span-diagramᵉ = domain-span-diagramᵉ 𝒮ᵉ

  codomain-right-concat-hom-arrow-span-diagramᵉ : UUᵉ l5ᵉ
  codomain-right-concat-hom-arrow-span-diagramᵉ = B'ᵉ

  span-right-concat-hom-arrow-span-diagramᵉ :
    spanᵉ l4ᵉ
      ( domain-right-concat-hom-arrow-span-diagramᵉ)
      ( codomain-right-concat-hom-arrow-span-diagramᵉ)
  span-right-concat-hom-arrow-span-diagramᵉ =
    right-concat-hom-arrow-spanᵉ
      ( span-span-diagramᵉ 𝒮ᵉ)
      ( g'ᵉ)
      ( hᵉ)

  right-concat-hom-arrow-span-diagramᵉ : span-diagramᵉ l1ᵉ l5ᵉ l4ᵉ
  pr1ᵉ right-concat-hom-arrow-span-diagramᵉ =
    domain-right-concat-hom-arrow-span-diagramᵉ
  pr1ᵉ (pr2ᵉ right-concat-hom-arrow-span-diagramᵉ) =
    codomain-right-concat-hom-arrow-span-diagramᵉ
  pr2ᵉ (pr2ᵉ right-concat-hom-arrow-span-diagramᵉ) =
    span-right-concat-hom-arrow-span-diagramᵉ

  spanning-type-right-concat-hom-arrow-span-diagramᵉ : UUᵉ l4ᵉ
  spanning-type-right-concat-hom-arrow-span-diagramᵉ =
    spanning-type-span-diagramᵉ right-concat-hom-arrow-span-diagramᵉ

  left-map-right-concat-hom-arrow-span-diagramᵉ :
    spanning-type-right-concat-hom-arrow-span-diagramᵉ →
    domain-right-concat-hom-arrow-span-diagramᵉ
  left-map-right-concat-hom-arrow-span-diagramᵉ =
    left-map-span-diagramᵉ right-concat-hom-arrow-span-diagramᵉ

  right-map-right-concat-hom-arrow-span-diagramᵉ :
    spanning-type-right-concat-hom-arrow-span-diagramᵉ →
    codomain-right-concat-hom-arrow-span-diagramᵉ
  right-map-right-concat-hom-arrow-span-diagramᵉ =
    right-map-span-diagramᵉ right-concat-hom-arrow-span-diagramᵉ
```