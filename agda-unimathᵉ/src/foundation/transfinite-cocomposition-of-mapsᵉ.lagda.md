# Transfinite cocomposition of maps

```agda
module foundation.transfinite-cocomposition-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.inverse-sequential-diagramsᵉ
open import foundation.sequential-limitsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ anᵉ
[inverseᵉ sequentialᵉ diagramᵉ ofᵉ types](foundation.inverse-sequential-diagrams.md),ᵉ
i.e.ᵉ aᵉ certainᵉ infiniteᵉ [sequence](foundation.dependent-sequences.mdᵉ) ofᵉ mapsᵉ
`fₙ`ᵉ:

```text
      ⋯ᵉ        fₙᵉ      ⋯ᵉ      f₁ᵉ      f₀ᵉ
  ⋯ᵉ --->ᵉ Aₙ₊₁ᵉ --->ᵉ Aₙᵉ --->ᵉ ⋯ᵉ --->ᵉ A₁ᵉ --->ᵉ A₀,ᵉ
```

weᵉ canᵉ formᵉ theᵉ **transfiniteᵉ cocomposition**ᵉ ofᵉ `f`ᵉ byᵉ takingᵉ theᵉ canonicalᵉ mapᵉ
fromᵉ theᵉ [standardᵉ sequentialᵉ limit](foundation.sequential-limits.mdᵉ) `limₙᵉ Aₙ`ᵉ
intoᵉ `A₀`.ᵉ

## Definitions

### The transfinite cocomposition of an inverse sequential diagram of maps

```agda
module _
  {lᵉ : Level} (fᵉ : inverse-sequential-diagramᵉ lᵉ)
  where

  transfinite-cocompᵉ :
    standard-sequential-limitᵉ fᵉ → family-inverse-sequential-diagramᵉ fᵉ 0
  transfinite-cocompᵉ xᵉ = sequence-standard-sequential-limitᵉ fᵉ xᵉ 0
```

## Table of files about sequential limits

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ sequentialᵉ limitsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/sequential-limits.mdᵉ}}