# Endomorphisms

```agda
module foundation.endomorphismsᵉ where

open import foundation-core.endomorphismsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.setsᵉ

open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import structured-types.wild-monoidsᵉ
```

</details>

## Idea

Anᵉ **endomorphism**ᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ mapᵉ `Aᵉ → A`.ᵉ

## Properties

### Endomorphisms form a monoid

```agda
endo-Wild-Monoidᵉ : {lᵉ : Level} → UUᵉ lᵉ → Wild-Monoidᵉ lᵉ
pr1ᵉ (pr1ᵉ (endo-Wild-Monoidᵉ Aᵉ)) = endo-Pointed-Typeᵉ Aᵉ
pr1ᵉ (pr2ᵉ (pr1ᵉ (endo-Wild-Monoidᵉ Aᵉ))) gᵉ fᵉ = gᵉ ∘ᵉ fᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr1ᵉ (endo-Wild-Monoidᵉ Aᵉ)))) fᵉ = reflᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr1ᵉ (endo-Wild-Monoidᵉ Aᵉ))))) fᵉ = reflᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr1ᵉ (endo-Wild-Monoidᵉ Aᵉ))))) = reflᵉ
pr1ᵉ (pr2ᵉ (endo-Wild-Monoidᵉ Aᵉ)) hᵉ gᵉ fᵉ = reflᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (endo-Wild-Monoidᵉ Aᵉ))) gᵉ fᵉ = reflᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (endo-Wild-Monoidᵉ Aᵉ)))) gᵉ fᵉ = reflᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (endo-Wild-Monoidᵉ Aᵉ))))) gᵉ fᵉ = reflᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (endo-Wild-Monoidᵉ Aᵉ))))) = starᵉ

endo-Semigroupᵉ : {lᵉ : Level} → Setᵉ lᵉ → Semigroupᵉ lᵉ
pr1ᵉ (endo-Semigroupᵉ Aᵉ) = endo-Setᵉ Aᵉ
pr1ᵉ (pr2ᵉ (endo-Semigroupᵉ Aᵉ)) gᵉ fᵉ = gᵉ ∘ᵉ fᵉ
pr2ᵉ (pr2ᵉ (endo-Semigroupᵉ Aᵉ)) hᵉ gᵉ fᵉ = reflᵉ

endo-Monoidᵉ : {lᵉ : Level} → Setᵉ lᵉ → Monoidᵉ lᵉ
pr1ᵉ (endo-Monoidᵉ Aᵉ) = endo-Semigroupᵉ Aᵉ
pr1ᵉ (pr2ᵉ (endo-Monoidᵉ Aᵉ)) = idᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (endo-Monoidᵉ Aᵉ))) fᵉ = reflᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (endo-Monoidᵉ Aᵉ))) fᵉ = reflᵉ
```

## See also

-ᵉ Forᵉ endomorphismsᵉ in aᵉ categoryᵉ seeᵉ
  [`category-theory.endomorphisms-in-categories`](category-theory.endomorphisms-in-categories.md).ᵉ