# Sequentially compact types

```agda
module synthetic-homotopy-theory.sequentially-compact-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
open import synthetic-homotopy-theory.universal-property-sequential-colimitsᵉ
```

</details>

## Idea

Aᵉ **sequentiallyᵉ compactᵉ type**ᵉ isᵉ aᵉ typeᵉ `X`ᵉ suchᵉ thatᵉ exponentiatingᵉ byᵉ `X`ᵉ
commutesᵉ with
[sequentialᵉ colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.mdᵉ)

```text
  colimₙᵉ (Xᵉ → Aₙᵉ) ≃ᵉ (Xᵉ → colimₙᵉ Aₙᵉ)
```

forᵉ everyᵉ [cotower](synthetic-homotopy-theory.sequential-diagrams.mdᵉ) `Aₙ`.ᵉ

## Definitions

### The predicate of being a sequentially compact type

```agda
module _
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ)
  where

  is-sequentially-compactᵉ : UUωᵉ
  is-sequentially-compactᵉ =
    {l2ᵉ l3ᵉ : Level} (Aᵉ : sequential-diagramᵉ l2ᵉ) {A∞ᵉ : UUᵉ l3ᵉ}
    (cᵉ : cocone-sequential-diagramᵉ Aᵉ A∞ᵉ) →
    universal-property-sequential-colimitᵉ cᵉ →
    universal-property-sequential-colimitᵉ
      ( cocone-postcomp-sequential-diagramᵉ Xᵉ Aᵉ cᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ Rij19ᵉ}}