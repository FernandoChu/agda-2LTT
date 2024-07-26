# Maps of prespectra

```agda
module synthetic-homotopy-theory.maps-of-prespectraᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.commuting-squares-of-pointed-mapsᵉ
open import structured-types.pointed-mapsᵉ

open import synthetic-homotopy-theory.functoriality-loop-spacesᵉ
open import synthetic-homotopy-theory.prespectraᵉ
```

</details>

## Idea

Aᵉ **mapᵉ ofᵉ prespectra**ᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ aᵉ
[sequence](foundation.dependent-sequences.mdᵉ) ofᵉ
[pointedᵉ maps](structured-types.pointed-maps.mdᵉ)

```text
  fₙᵉ : Aₙᵉ →∗ᵉ Bₙᵉ
```

suchᵉ thatᵉ theᵉ squaresᵉ

```text
        fₙᵉ
  Aₙᵉ -------->ᵉ Bₙᵉ
  |            |
  |            |
  |            |
  ∨ᵉ            ∨ᵉ
  ΩAₙ₊₁ᵉ ----->ᵉ ΩBₙ₊₁ᵉ
        Ωfₙ₊₁ᵉ
```

commuteᵉ in theᵉ categoryᵉ ofᵉ [pointedᵉ types](structured-types.pointed-types.md).ᵉ

## Definition

```agda
coherence-map-Prespectrumᵉ :
  {l1ᵉ l2ᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : Prespectrumᵉ l1ᵉ) (Bᵉ : Prespectrumᵉ l2ᵉ) →
  ( (nᵉ : ℕᵉ) →
    pointed-type-Prespectrumᵉ Aᵉ nᵉ →∗ᵉ pointed-type-Prespectrumᵉ Bᵉ nᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
coherence-map-Prespectrumᵉ nᵉ Aᵉ Bᵉ fᵉ =
  coherence-square-pointed-mapsᵉ
    ( fᵉ nᵉ)
    ( pointed-adjoint-structure-map-Prespectrumᵉ Aᵉ nᵉ)
    ( pointed-adjoint-structure-map-Prespectrumᵉ Bᵉ nᵉ)
    ( pointed-map-Ωᵉ (fᵉ (succ-ℕᵉ nᵉ)))

map-Prespectrumᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Prespectrumᵉ l1ᵉ) (Bᵉ : Prespectrumᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
map-Prespectrumᵉ Aᵉ Bᵉ =
  Σᵉ ( (nᵉ : ℕᵉ) →
      pointed-type-Prespectrumᵉ Aᵉ nᵉ →∗ᵉ pointed-type-Prespectrumᵉ Bᵉ nᵉ)
    ( λ fᵉ → (nᵉ : ℕᵉ) → coherence-map-Prespectrumᵉ nᵉ Aᵉ Bᵉ fᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ May99ᵉ}}