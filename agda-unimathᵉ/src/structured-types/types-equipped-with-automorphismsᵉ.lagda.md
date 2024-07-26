# Types equipped with automorphisms

```agda
module structured-types.types-equipped-with-automorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphismsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.types-equipped-with-endomorphismsᵉ
```

</details>

## Idea

Aᵉ **typeᵉ equippedᵉ with anᵉ automorphism**ᵉ isᵉ aᵉ pairᵉ consistingᵉ ofᵉ aᵉ typeᵉ `A`ᵉ andᵉ
anᵉ [automorphism](foundation.automorphisms.mdᵉ) onᵉ `eᵉ : Aᵉ ≃ᵉ A`.ᵉ

## Definitions

### Types equipped with automorphisms

```agda
Type-With-Automorphismᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Type-With-Automorphismᵉ lᵉ = Σᵉ (UUᵉ lᵉ) (Autᵉ)

module _
  {lᵉ : Level} (Aᵉ : Type-With-Automorphismᵉ lᵉ)
  where

  type-Type-With-Automorphismᵉ : UUᵉ lᵉ
  type-Type-With-Automorphismᵉ = pr1ᵉ Aᵉ

  automorphism-Type-With-Automorphismᵉ : Autᵉ type-Type-With-Automorphismᵉ
  automorphism-Type-With-Automorphismᵉ = pr2ᵉ Aᵉ

  map-Type-With-Automorphismᵉ :
    type-Type-With-Automorphismᵉ → type-Type-With-Automorphismᵉ
  map-Type-With-Automorphismᵉ = map-equivᵉ automorphism-Type-With-Automorphismᵉ

  type-with-endomorphism-Type-With-Automorphismᵉ : Type-With-Endomorphismᵉ lᵉ
  pr1ᵉ type-with-endomorphism-Type-With-Automorphismᵉ =
    type-Type-With-Automorphismᵉ
  pr2ᵉ type-with-endomorphism-Type-With-Automorphismᵉ =
    map-Type-With-Automorphismᵉ
```

### Types equipped with the identity automorphism

```agda
trivial-Type-With-Automorphismᵉ : {lᵉ : Level} → UUᵉ lᵉ → Type-With-Automorphismᵉ lᵉ
pr1ᵉ (trivial-Type-With-Automorphismᵉ Xᵉ) = Xᵉ
pr2ᵉ (trivial-Type-With-Automorphismᵉ Xᵉ) = id-equivᵉ
```

## See also

-ᵉ Setsᵉ equippedᵉ with automorphismsᵉ areᵉ definedᵉ in
  [`structured-types.sets-equipped-with-automorphisms.md`](structured-types.sets-equipped-with-automorphisms.mdᵉ)
-ᵉ Cyclicᵉ typesᵉ areᵉ
  [setsᵉ equippedᵉ with automorphisms](structured-types.sets-equipped-with-automorphisms.mdᵉ)
  ofᵉ whichᵉ theᵉ automorphismᵉ actsᵉ transitively.ᵉ
-ᵉ Theᵉ
  [descentᵉ propertyᵉ ofᵉ theᵉ circle](synthetic-homotopy-theory.descent-circle.mdᵉ)
  showsᵉ thatᵉ typeᵉ familiesᵉ overᵉ theᵉ
  [circle](synthetic-homotopy-theory.circle.mdᵉ) areᵉ
  [equivalently](foundation.equivalences.mdᵉ) describedᵉ asᵉ typesᵉ equippedᵉ with
  automorphisms.ᵉ