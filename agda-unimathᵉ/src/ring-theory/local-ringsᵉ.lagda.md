# Local rings

```agda
module ring-theory.local-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.disjunctionᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.invertible-elements-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Aᵉ localᵉ ringᵉ isᵉ aᵉ ringᵉ suchᵉ thatᵉ wheneverᵉ aᵉ sumᵉ ofᵉ elementsᵉ isᵉ invertible,ᵉ thenᵉ
oneᵉ ofᵉ itsᵉ summandsᵉ isᵉ invertible.ᵉ Thisᵉ impliesᵉ thatᵉ theᵉ noninvertibleᵉ elementsᵉ
formᵉ anᵉ ideal.ᵉ However,ᵉ theᵉ lawᵉ ofᵉ excludedᵉ middleᵉ isᵉ neededᵉ to showᵉ thatᵉ anyᵉ
ringᵉ ofᵉ whichᵉ theᵉ noninvertibleᵉ elementsᵉ formᵉ anᵉ idealᵉ isᵉ aᵉ localᵉ ring.ᵉ

## Definition

```agda
is-local-prop-Ringᵉ : {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) → Propᵉ lᵉ
is-local-prop-Ringᵉ Rᵉ =
  Π-Propᵉ
    ( type-Ringᵉ Rᵉ)
    ( λ aᵉ →
      Π-Propᵉ
        ( type-Ringᵉ Rᵉ)
        ( λ bᵉ →
          function-Propᵉ
            ( is-invertible-element-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ aᵉ bᵉ))
            ( disjunction-Propᵉ
              ( is-invertible-element-prop-Ringᵉ Rᵉ aᵉ)
              ( is-invertible-element-prop-Ringᵉ Rᵉ bᵉ))))

is-local-Ringᵉ : {lᵉ : Level} → Ringᵉ lᵉ → UUᵉ lᵉ
is-local-Ringᵉ Rᵉ = type-Propᵉ (is-local-prop-Ringᵉ Rᵉ)

is-prop-is-local-Ringᵉ : {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) → is-propᵉ (is-local-Ringᵉ Rᵉ)
is-prop-is-local-Ringᵉ Rᵉ = is-prop-type-Propᵉ (is-local-prop-Ringᵉ Rᵉ)

Local-Ringᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Local-Ringᵉ lᵉ = Σᵉ (Ringᵉ lᵉ) is-local-Ringᵉ

module _
  {lᵉ : Level} (Rᵉ : Local-Ringᵉ lᵉ)
  where

  ring-Local-Ringᵉ : Ringᵉ lᵉ
  ring-Local-Ringᵉ = pr1ᵉ Rᵉ

  set-Local-Ringᵉ : Setᵉ lᵉ
  set-Local-Ringᵉ = set-Ringᵉ ring-Local-Ringᵉ

  type-Local-Ringᵉ : UUᵉ lᵉ
  type-Local-Ringᵉ = type-Ringᵉ ring-Local-Ringᵉ

  is-local-ring-Local-Ringᵉ : is-local-Ringᵉ ring-Local-Ringᵉ
  is-local-ring-Local-Ringᵉ = pr2ᵉ Rᵉ
```