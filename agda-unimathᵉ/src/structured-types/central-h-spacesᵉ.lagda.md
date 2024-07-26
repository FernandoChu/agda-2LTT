# Central H-spaces

```agda
module structured-types.central-h-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Inᵉ [`structured-types.h-spaces`](structured-types.h-spaces.mdᵉ) weᵉ sawᵉ thatᵉ theᵉ
typeᵉ ofᵉ H-spaceᵉ structuresᵉ onᵉ aᵉ
[pointedᵉ type](structured-types.pointed-types.mdᵉ) `A`ᵉ isᵉ equivalentlyᵉ describedᵉ
asᵉ theᵉ typeᵉ ofᵉ [pointedᵉ sections](structured-types.pointed-types.mdᵉ) ofᵉ theᵉ
pointedᵉ evaluationᵉ mapᵉ `(Aᵉ → Aᵉ) →∗ᵉ A`.ᵉ Ifᵉ theᵉ typeᵉ `A`ᵉ isᵉ
[connected](foundation.connected-types.md),ᵉ thenᵉ theᵉ sectionᵉ mapsᵉ to theᵉ
[connectedᵉ component](foundation.connected-components.mdᵉ) ofᵉ `(Aᵉ ≃ᵉ A)`ᵉ atᵉ theᵉ
identityᵉ [equivalence](foundation-core.equivalences.md).ᵉ Anᵉ **evaluativeᵉ
H-space**ᵉ isᵉ aᵉ pointedᵉ typeᵉ suchᵉ thatᵉ theᵉ mapᵉ `ev_ptᵉ : (Aᵉ ≃ᵉ A)_{(idᵉ)} → A`ᵉ isᵉ anᵉ
equivalence.ᵉ

## Definition

```agda
is-central-h-spaceᵉ :
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ) → UUᵉ lᵉ
is-central-h-spaceᵉ Aᵉ =
  is-equivᵉ
    { Aᵉ = type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Aᵉ}
    ( ev-point-Pointed-Typeᵉ Aᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ BCFR23ᵉ}}