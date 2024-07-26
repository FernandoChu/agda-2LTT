# Flat dependent function types

```agda
{-# OPTIONSᵉ --cohesionᵉ --flat-splitᵉ #-}

module modal-type-theory.flat-dependent-function-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import modal-type-theory.flat-modalityᵉ
```

</details>

## Idea

Weᵉ studyᵉ interactionsᵉ betweenᵉ theᵉ
[flatᵉ modality](modal-type-theory.flat-modality.mdᵉ) andᵉ
[dependentᵉ functionᵉ types](foundation.function-types.md).ᵉ

## Properties

### Flat distributes over dependent function types

```agda
module _
  {@♭ᵉ l1ᵉ l2ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} {@♭ᵉ Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  map-crisp-distributive-flat-Πᵉ : ♭ᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ) → ((@♭ᵉ xᵉ : Aᵉ) → ♭ᵉ (Bᵉ xᵉ))
  map-crisp-distributive-flat-Πᵉ (cons-flatᵉ fᵉ) xᵉ = cons-flatᵉ (fᵉ xᵉ)

module _
  {@♭ᵉ l1ᵉ l2ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} {@♭ᵉ Bᵉ : UUᵉ l2ᵉ}
  where

  map-crisp-distributive-flat-function-typesᵉ : ♭ᵉ (Aᵉ → Bᵉ) → (@♭ᵉ Aᵉ → ♭ᵉ Bᵉ)
  map-crisp-distributive-flat-function-typesᵉ = map-crisp-distributive-flat-Πᵉ

  map-distributive-flat-function-typesᵉ : ♭ᵉ (Aᵉ → Bᵉ) → (♭ᵉ Aᵉ → ♭ᵉ Bᵉ)
  map-distributive-flat-function-typesᵉ fᵉ (cons-flatᵉ xᵉ) =
    map-crisp-distributive-flat-function-typesᵉ fᵉ xᵉ
```

## See also

-ᵉ [Flatᵉ discreteᵉ types](modal-type-theory.flat-discrete-types.mdᵉ) forᵉ typesᵉ thatᵉ
  areᵉ flatᵉ modal.ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ Shu18ᵉ}} {{#referenceᵉ Dlicata335/Cohesion-Agdaᵉ}}