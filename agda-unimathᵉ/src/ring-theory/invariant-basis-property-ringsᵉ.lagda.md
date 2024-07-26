# The invariant basis property of rings

```agda
module ring-theory.invariant-basis-property-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.dependent-products-ringsᵉ
open import ring-theory.isomorphisms-ringsᵉ
open import ring-theory.ringsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ ringᵉ Rᵉ isᵉ saidᵉ to satisfyᵉ theᵉ invariantᵉ basisᵉ propertyᵉ ifᵉ `R^mᵉ ≅ᵉ R^n`ᵉ impliesᵉ
`mᵉ = n`ᵉ forᵉ anyᵉ twoᵉ naturalᵉ numbersᵉ `m`ᵉ andᵉ `n`.ᵉ

## Definition

```agda
invariant-basis-property-Ringᵉ :
  {l1ᵉ : Level} → Ringᵉ l1ᵉ → UUᵉ l1ᵉ
invariant-basis-property-Ringᵉ Rᵉ =
  (mᵉ nᵉ : ℕᵉ) →
  iso-Ringᵉ (Π-Ringᵉ (Finᵉ mᵉ) (λ iᵉ → Rᵉ)) (Π-Ringᵉ (Finᵉ nᵉ) (λ iᵉ → Rᵉ)) →
  Idᵉ mᵉ nᵉ
```