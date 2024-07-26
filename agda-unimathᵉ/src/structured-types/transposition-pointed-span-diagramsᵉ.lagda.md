# Transposition of pointed span diagrams

```agda
module structured-types.transposition-pointed-span-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.opposite-pointed-spansᵉ
open import structured-types.pointed-span-diagramsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "trasposition"ᵉ Disambiguation="pointedᵉ spanᵉ diagram"ᵉ Agda=transposition-pointed-span-diagramᵉ}}
ofᵉ aᵉ [pointedᵉ spanᵉ diagram](structured-types.pointed-span-diagrams.mdᵉ)

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

isᵉ theᵉ pointedᵉ spanᵉ diagramᵉ

```text
       gᵉ       fᵉ
  Bᵉ <-----ᵉ Sᵉ ----->ᵉ A.ᵉ
```

Inᵉ otherᵉ words,ᵉ theᵉ transpositionᵉ ofᵉ aᵉ pointedᵉ spanᵉ diagramᵉ `(Aᵉ ,ᵉ Bᵉ ,ᵉ s)`ᵉ isᵉ theᵉ
pointedᵉ spanᵉ diagramᵉ `(Bᵉ ,ᵉ Aᵉ ,ᵉ opposite-pointed-spanᵉ s)`ᵉ where
`opposite-pointed-spanᵉ s`ᵉ isᵉ theᵉ
[opposite](structured-types.opposite-pointed-spans.mdᵉ) ofᵉ theᵉ
[pointedᵉ span](structured-types.pointed-spans.mdᵉ) `s`ᵉ fromᵉ `A`ᵉ to `B`.ᵉ

## Definitions

### Transposition of pointed span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (𝒮ᵉ : pointed-span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  transposition-pointed-span-diagramᵉ : pointed-span-diagramᵉ l2ᵉ l1ᵉ l3ᵉ
  pr1ᵉ transposition-pointed-span-diagramᵉ =
    pointed-codomain-pointed-span-diagramᵉ 𝒮ᵉ
  pr1ᵉ (pr2ᵉ transposition-pointed-span-diagramᵉ) =
    pointed-domain-pointed-span-diagramᵉ 𝒮ᵉ
  pr2ᵉ (pr2ᵉ transposition-pointed-span-diagramᵉ) =
    opposite-pointed-spanᵉ (pointed-span-pointed-span-diagramᵉ 𝒮ᵉ)
```