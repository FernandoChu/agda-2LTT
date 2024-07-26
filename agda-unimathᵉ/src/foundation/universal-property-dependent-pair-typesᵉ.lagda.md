# The universal property of dependent pair types

```agda
module foundation.universal-property-dependent-pair-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "universalᵉ propertyᵉ ofᵉ dependentᵉ pairᵉ types"ᵉ}} characterizesᵉ ofᵉ
mapsᵉ outᵉ ofᵉ [dependentᵉ pairᵉ types](foundation.dependent-pair-types.md).ᵉ Itᵉ
statesᵉ thatᵉ _uncurriedᵉ_ mapsᵉ `(xᵉ : Σᵉ Aᵉ Bᵉ) → Cᵉ x`ᵉ areᵉ in correspondenceᵉ with
_curriedᵉ_ mapsᵉ `(aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ) → Cᵉ (aᵉ ,ᵉ b)`.ᵉ

## Theorem

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Σᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ}
  where

  abstract
    is-equiv-ev-pairᵉ : is-equivᵉ (ev-pairᵉ {Cᵉ = Cᵉ})
    pr1ᵉ (pr1ᵉ is-equiv-ev-pairᵉ) = ind-Σᵉ
    pr2ᵉ (pr1ᵉ is-equiv-ev-pairᵉ) = refl-htpyᵉ
    pr1ᵉ (pr2ᵉ is-equiv-ev-pairᵉ) = ind-Σᵉ
    pr2ᵉ (pr2ᵉ is-equiv-ev-pairᵉ) fᵉ = eq-htpyᵉ (ind-Σᵉ (λ xᵉ yᵉ → reflᵉ))

  abstract
    is-equiv-ind-Σᵉ : is-equivᵉ (ind-Σᵉ {Cᵉ = Cᵉ})
    is-equiv-ind-Σᵉ = is-equiv-is-sectionᵉ is-equiv-ev-pairᵉ refl-htpyᵉ

  equiv-ev-pairᵉ : ((xᵉ : Σᵉ Aᵉ Bᵉ) → Cᵉ xᵉ) ≃ᵉ ((aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ) → Cᵉ (aᵉ ,ᵉ bᵉ))
  pr1ᵉ equiv-ev-pairᵉ = ev-pairᵉ
  pr2ᵉ equiv-ev-pairᵉ = is-equiv-ev-pairᵉ

  equiv-ind-Σᵉ : ((aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ) → Cᵉ (aᵉ ,ᵉ bᵉ)) ≃ᵉ ((xᵉ : Σᵉ Aᵉ Bᵉ) → Cᵉ xᵉ)
  pr1ᵉ equiv-ind-Σᵉ = ind-Σᵉ
  pr2ᵉ equiv-ind-Σᵉ = is-equiv-ind-Σᵉ
```

## Properties

### Iterated currying

```agda
equiv-ev-pair²ᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  { Xᵉ : UUᵉ l4ᵉ} {Yᵉ : Xᵉ → UUᵉ l5ᵉ}
  { Zᵉ : ( Σᵉ Aᵉ Bᵉ → Cᵉ) → Σᵉ Xᵉ Yᵉ → UUᵉ l6ᵉ} →
  Σᵉ ( Σᵉ Aᵉ Bᵉ → Cᵉ) (λ kᵉ → ( xyᵉ : Σᵉ Xᵉ Yᵉ) → Zᵉ kᵉ xyᵉ) ≃ᵉ
  Σᵉ ( (aᵉ : Aᵉ) → Bᵉ aᵉ → Cᵉ) (λ kᵉ → (xᵉ : Xᵉ) → (yᵉ : Yᵉ xᵉ) → Zᵉ (ind-Σᵉ kᵉ) (xᵉ ,ᵉ yᵉ))
equiv-ev-pair²ᵉ {Xᵉ = Xᵉ} {Yᵉ = Yᵉ} {Zᵉ = Zᵉ} =
  equiv-Σᵉ
    ( λ kᵉ → (xᵉ : Xᵉ) (yᵉ : Yᵉ xᵉ) → Zᵉ (ind-Σᵉ kᵉ) (xᵉ ,ᵉ yᵉ))
    ( equiv-ev-pairᵉ)
    ( λ kᵉ → equiv-ev-pairᵉ)

equiv-ev-pair³ᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ : Level} →
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  { Xᵉ : UUᵉ l4ᵉ} {Yᵉ : Xᵉ → UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  { Uᵉ : UUᵉ l7ᵉ} {Vᵉ : Uᵉ → UUᵉ l8ᵉ}
  { Wᵉ : ((Σᵉ Aᵉ Bᵉ) → Cᵉ) → ((Σᵉ Xᵉ Yᵉ) → Zᵉ) → (Σᵉ Uᵉ Vᵉ) → UUᵉ l9ᵉ} →
  Σᵉ ( (Σᵉ Aᵉ Bᵉ) → Cᵉ)
    ( λ kᵉ →
      Σᵉ ( (Σᵉ Xᵉ Yᵉ) → Zᵉ)
        ( λ lᵉ → ( uvᵉ : Σᵉ Uᵉ Vᵉ) → Wᵉ kᵉ lᵉ uvᵉ)) ≃ᵉ
  Σᵉ ( (aᵉ : Aᵉ) → Bᵉ aᵉ → Cᵉ)
    ( λ kᵉ →
      Σᵉ ( (xᵉ : Xᵉ) → Yᵉ xᵉ → Zᵉ)
        ( λ lᵉ → (uᵉ : Uᵉ) → (vᵉ : Vᵉ uᵉ) → Wᵉ (ind-Σᵉ kᵉ) (ind-Σᵉ lᵉ) (uᵉ ,ᵉ vᵉ)))
equiv-ev-pair³ᵉ {Xᵉ = Xᵉ} {Yᵉ = Yᵉ} {Zᵉ = Zᵉ} {Uᵉ = Uᵉ} {Vᵉ = Vᵉ} {Wᵉ = Wᵉ} =
  equiv-Σᵉ
    ( λ kᵉ →
      Σᵉ ( (xᵉ : Xᵉ) → Yᵉ xᵉ → Zᵉ)
        ( λ lᵉ → (uᵉ : Uᵉ) → (vᵉ : Vᵉ uᵉ) → Wᵉ (ind-Σᵉ kᵉ) (ind-Σᵉ lᵉ) (uᵉ ,ᵉ vᵉ)))
    ( equiv-ev-pairᵉ)
    ( λ kᵉ → equiv-ev-pair²ᵉ)
```