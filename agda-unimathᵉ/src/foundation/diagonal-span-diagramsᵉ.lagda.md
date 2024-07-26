# Diagonal span diagrams

```agda
module foundation.diagonal-span-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.span-diagramsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`.ᵉ Theᵉ
{{#conceptᵉ "diagonalᵉ spanᵉ diagram"ᵉ Agda=diagonal-span-diagramᵉ}} ofᵉ `f`ᵉ isᵉ theᵉ
[spanᵉ diagram](foundation.span-diagrams.mdᵉ)

```text
       fᵉ       fᵉ
  Bᵉ <-----ᵉ Aᵉ ----->ᵉ B.ᵉ
```

## Definitions

### Diagonal span diagrams of maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  diagonal-span-diagramᵉ : span-diagramᵉ l2ᵉ l2ᵉ l1ᵉ
  diagonal-span-diagramᵉ = make-span-diagramᵉ fᵉ fᵉ
```