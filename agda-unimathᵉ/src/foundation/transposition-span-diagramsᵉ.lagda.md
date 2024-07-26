# Transposition of span diagrams

```agda
module foundation.transposition-span-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.opposite-spansᵉ
open import foundation.span-diagramsᵉ
open import foundation.spansᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "trasposition"ᵉ Disambiguation="spanᵉ diagram"ᵉ Agda=transposition-span-diagramᵉ}}
ofᵉ aᵉ [spanᵉ diagram](foundation.span-diagrams.mdᵉ)

```text
       fᵉ       gᵉ
  Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
```

isᵉ theᵉ spanᵉ diagramᵉ

```text
       gᵉ       fᵉ
  Bᵉ <-----ᵉ Sᵉ ----->ᵉ A.ᵉ
```

Inᵉ otherᵉ words,ᵉ theᵉ transpositionᵉ ofᵉ aᵉ spanᵉ diagramᵉ `(Aᵉ ,ᵉ Bᵉ ,ᵉ s)`ᵉ isᵉ theᵉ spanᵉ
diagramᵉ `(Bᵉ ,ᵉ Aᵉ ,ᵉ opposite-spanᵉ s)`ᵉ where `opposite-spanᵉ s`ᵉ isᵉ theᵉ
[opposite](foundation.opposite-spans.mdᵉ) ofᵉ theᵉ [span](foundation.spans.mdᵉ) `s`ᵉ
fromᵉ `A`ᵉ to `B`.ᵉ

## Definitions

### Transposition of span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  transposition-span-diagramᵉ : span-diagramᵉ l2ᵉ l1ᵉ l3ᵉ
  pr1ᵉ transposition-span-diagramᵉ = codomain-span-diagramᵉ 𝒮ᵉ
  pr1ᵉ (pr2ᵉ transposition-span-diagramᵉ) = domain-span-diagramᵉ 𝒮ᵉ
  pr2ᵉ (pr2ᵉ transposition-span-diagramᵉ) = opposite-spanᵉ (span-span-diagramᵉ 𝒮ᵉ)
```