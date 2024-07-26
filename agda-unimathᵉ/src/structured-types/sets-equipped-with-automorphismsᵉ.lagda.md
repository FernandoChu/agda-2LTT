# Sets equipped with automorphisms

```agda
module structured-types.sets-equipped-with-automorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphismsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **setᵉ equippedᵉ with anᵉ automorphism**ᵉ isᵉ aᵉ pairᵉ consistingᵉ ofᵉ aᵉ
[set](foundation.sets.mdᵉ) `A`ᵉ andᵉ anᵉ [automorphism](foundation.automorphisms.mdᵉ)
onᵉ `eᵉ : Aᵉ ≃ᵉ A`.ᵉ

## Definitions

### Sets equipped with automorphisms

```agda
Set-With-Automorphismᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Set-With-Automorphismᵉ lᵉ = Σᵉ (Setᵉ lᵉ) (Autᵉ ∘ᵉ type-Setᵉ)

module _
  {lᵉ : Level} (Aᵉ : Set-With-Automorphismᵉ lᵉ)
  where

  set-Set-With-Automorphismᵉ : Setᵉ lᵉ
  set-Set-With-Automorphismᵉ = pr1ᵉ Aᵉ

  type-Set-With-Automorphismᵉ : UUᵉ lᵉ
  type-Set-With-Automorphismᵉ = type-Setᵉ set-Set-With-Automorphismᵉ

  is-set-type-Set-With-Automorphismᵉ : is-setᵉ type-Set-With-Automorphismᵉ
  is-set-type-Set-With-Automorphismᵉ = is-set-type-Setᵉ set-Set-With-Automorphismᵉ

  aut-Set-With-Automorphismᵉ : Autᵉ type-Set-With-Automorphismᵉ
  aut-Set-With-Automorphismᵉ = pr2ᵉ Aᵉ

  map-Set-With-Automorphismᵉ :
    type-Set-With-Automorphismᵉ → type-Set-With-Automorphismᵉ
  map-Set-With-Automorphismᵉ = map-equivᵉ aut-Set-With-Automorphismᵉ
```