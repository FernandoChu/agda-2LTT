# Universal property of contractible types with respect to pointed types and maps

```agda
module structured-types.pointed-universal-property-contractible-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universal-property-contractible-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Byᵉ definition,ᵉ aᵉ [contractible](foundation-core.contractible-types.mdᵉ) typeᵉ isᵉ
[pointed](structured-types.pointed-types.md).ᵉ Moreover,ᵉ theyᵉ enjoyᵉ aᵉ universalᵉ
propertyᵉ amongᵉ theᵉ pointedᵉ typesᵉ with respectᵉ to
[pointedᵉ maps](structured-types.pointed-maps.mdᵉ):

Aᵉ pointedᵉ typeᵉ `A`ᵉ isᵉ contractibleᵉ ifᵉ forᵉ allᵉ pointedᵉ typesᵉ `X`,ᵉ theᵉ typeᵉ ofᵉ
pointedᵉ mapsᵉ `Aᵉ →∗ᵉ X`ᵉ isᵉ contractible.ᵉ

## Definitions

### The universal property of contractible types with respect to pointed types and maps

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  universal-property-contr-Pointed-Typeᵉ : UUωᵉ
  universal-property-contr-Pointed-Typeᵉ =
    {lᵉ : Level} (Xᵉ : Pointed-Typeᵉ lᵉ) → is-contrᵉ (Aᵉ →∗ᵉ Xᵉ)
```

## Properties

### A contractible type has the universal property of contractible types with respect to pointed types and maps

**Proof:**ᵉ Ifᵉ `A`ᵉ isᵉ contractibleᵉ with aᵉ pointᵉ `aᵉ : A`,ᵉ thenᵉ weᵉ haveᵉ

```text
   ((Aᵉ ,ᵉ aᵉ) →∗ᵉ (Xᵉ ,ᵉ xᵉ))
 ≃ᵉ Σᵉ (Aᵉ → Xᵉ) (λ fᵉ → fᵉ aᵉ ＝ᵉ xᵉ)
 ≃ᵉ Σᵉ Xᵉ (λ yᵉ → yᵉ ＝ᵉ xᵉ)
```

where theᵉ lastᵉ equivalenceᵉ holdsᵉ sinceᵉ `(Aᵉ → Xᵉ) ≃ᵉ X`ᵉ byᵉ theᵉ
[universalᵉ propertyᵉ ofᵉ contractibleᵉ types](foundation.universal-property-contractible-types.md).ᵉ

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ)
  where

  universal-property-contr-is-contr-Pointed-Type'ᵉ :
    is-contrᵉ Aᵉ → universal-property-contr-Pointed-Typeᵉ (Aᵉ ,ᵉ aᵉ)
  universal-property-contr-is-contr-Pointed-Type'ᵉ cᵉ (Xᵉ ,ᵉ xᵉ) =
    is-contr-equivᵉ
      ( Σᵉ Xᵉ (λ yᵉ → yᵉ ＝ᵉ xᵉ))
      ( equiv-Σ-equiv-baseᵉ _ (equiv-universal-property-contrᵉ aᵉ cᵉ Xᵉ))
      ( is-torsorial-Id'ᵉ xᵉ)

module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  universal-property-contr-is-contr-Pointed-Typeᵉ :
    (cᵉ : is-contrᵉ Aᵉ) → universal-property-contr-Pointed-Typeᵉ (Aᵉ ,ᵉ centerᵉ cᵉ)
  universal-property-contr-is-contr-Pointed-Typeᵉ cᵉ =
    universal-property-contr-is-contr-Pointed-Type'ᵉ (centerᵉ cᵉ) cᵉ
```

### A pointed type with the universal property of contractible types with respect to pointed types and maps is contractible

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ)
  where

  is-contr-universal-property-contr-Pointed-Type'ᵉ :
    universal-property-contr-Pointed-Typeᵉ (Aᵉ ,ᵉ aᵉ) → is-contrᵉ Aᵉ
  is-contr-universal-property-contr-Pointed-Type'ᵉ upᵉ =
    is-contr-universal-property-contrᵉ aᵉ
      ( λ Xᵉ →
        is-equiv-htpy-equivᵉ
          ( equivalence-reasoningᵉ
              (Aᵉ → Xᵉ)
              ≃ᵉ Σᵉ (Aᵉ → Xᵉ) (λ fᵉ → Σᵉ Xᵉ (λ xᵉ → fᵉ aᵉ ＝ᵉ xᵉ))
                byᵉ inv-right-unit-law-Σ-is-contrᵉ (λ fᵉ → is-torsorial-Idᵉ (fᵉ aᵉ))
              ≃ᵉ Σᵉ Xᵉ (λ xᵉ → (Aᵉ ,ᵉ aᵉ) →∗ᵉ (Xᵉ ,ᵉ xᵉ))
                byᵉ equiv-left-swap-Σᵉ
              ≃ᵉ Xᵉ
                byᵉ equiv-pr1ᵉ (λ xᵉ → upᵉ (Xᵉ ,ᵉ xᵉ)))
            ( λ fᵉ →
              apᵉ
                ( pr1ᵉ)
                ( invᵉ
                  ( contractionᵉ (is-torsorial-Idᵉ (fᵉ aᵉ)) (pairᵉ (fᵉ aᵉ) reflᵉ)))))

module _
  {l1ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  is-contr-universal-property-contr-Pointed-Typeᵉ :
    universal-property-contr-Pointed-Typeᵉ Aᵉ → is-contrᵉ (type-Pointed-Typeᵉ Aᵉ)
  is-contr-universal-property-contr-Pointed-Typeᵉ =
    is-contr-universal-property-contr-Pointed-Type'ᵉ (point-Pointed-Typeᵉ Aᵉ)
```