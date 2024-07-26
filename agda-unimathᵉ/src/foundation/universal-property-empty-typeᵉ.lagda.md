# The universal property of the empty type

```agda
module foundation.universal-property-empty-typeᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
```

</details>

## Idea

Thereᵉ isᵉ aᵉ uniqueᵉ mapᵉ fromᵉ theᵉ emptyᵉ typeᵉ intoᵉ anyᵉ type.ᵉ Similarly,ᵉ forᵉ anyᵉ typeᵉ
familyᵉ overᵉ anᵉ emptyᵉ type,ᵉ thereᵉ isᵉ aᵉ uniqueᵉ dependentᵉ functionᵉ takingᵉ valuesᵉ in
thisᵉ family.ᵉ

## Properties

```agda
module _
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ)
  where

  dependent-universal-property-emptyᵉ : (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
  dependent-universal-property-emptyᵉ lᵉ =
    (Pᵉ : Aᵉ → UUᵉ lᵉ) → is-contrᵉ ((xᵉ : Aᵉ) → Pᵉ xᵉ)

  universal-property-emptyᵉ : (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
  universal-property-emptyᵉ lᵉ = (Xᵉ : UUᵉ lᵉ) → is-contrᵉ (Aᵉ → Xᵉ)

  universal-property-dependent-universal-property-emptyᵉ :
    ({lᵉ : Level} → dependent-universal-property-emptyᵉ lᵉ) →
    ({lᵉ : Level} → universal-property-emptyᵉ lᵉ)
  universal-property-dependent-universal-property-emptyᵉ dup-emptyᵉ {lᵉ} Xᵉ =
    dup-emptyᵉ {lᵉ} (λ aᵉ → Xᵉ)

  is-empty-universal-property-emptyᵉ :
    ({lᵉ : Level} → universal-property-emptyᵉ lᵉ) → is-emptyᵉ Aᵉ
  is-empty-universal-property-emptyᵉ up-emptyᵉ = centerᵉ (up-emptyᵉ emptyᵉ)

  dependent-universal-property-empty-is-emptyᵉ :
    {lᵉ : Level} (Hᵉ : is-emptyᵉ Aᵉ) → dependent-universal-property-emptyᵉ lᵉ
  pr1ᵉ (dependent-universal-property-empty-is-emptyᵉ {lᵉ} Hᵉ Pᵉ) xᵉ = ex-falsoᵉ (Hᵉ xᵉ)
  pr2ᵉ (dependent-universal-property-empty-is-emptyᵉ {lᵉ} Hᵉ Pᵉ) fᵉ =
    eq-htpyᵉ (λ xᵉ → ex-falsoᵉ (Hᵉ xᵉ))

  universal-property-empty-is-emptyᵉ :
    {lᵉ : Level} (Hᵉ : is-emptyᵉ Aᵉ) → universal-property-emptyᵉ lᵉ
  universal-property-empty-is-emptyᵉ {lᵉ} Hᵉ =
    universal-property-dependent-universal-property-emptyᵉ
      ( dependent-universal-property-empty-is-emptyᵉ Hᵉ)

abstract
  dependent-universal-property-empty'ᵉ :
    {lᵉ : Level} (Pᵉ : emptyᵉ → UUᵉ lᵉ) → is-contrᵉ ((xᵉ : emptyᵉ) → Pᵉ xᵉ)
  pr1ᵉ (dependent-universal-property-empty'ᵉ Pᵉ) = ind-emptyᵉ {Pᵉ = Pᵉ}
  pr2ᵉ (dependent-universal-property-empty'ᵉ Pᵉ) fᵉ = eq-htpyᵉ ind-emptyᵉ

abstract
  universal-property-empty'ᵉ :
    {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-contrᵉ (emptyᵉ → Xᵉ)
  universal-property-empty'ᵉ Xᵉ =
    dependent-universal-property-empty'ᵉ (λ tᵉ → Xᵉ)

abstract
  uniqueness-emptyᵉ :
    {lᵉ : Level} (Yᵉ : UUᵉ lᵉ) →
    ({l'ᵉ : Level} (Xᵉ : UUᵉ l'ᵉ) → is-contrᵉ (Yᵉ → Xᵉ)) →
    is-equivᵉ (ind-emptyᵉ {Pᵉ = λ tᵉ → Yᵉ})
  uniqueness-emptyᵉ Yᵉ Hᵉ =
    is-equiv-is-equiv-precompᵉ ind-emptyᵉ
      ( λ Xᵉ →
        is-equiv-is-contrᵉ
          ( λ gᵉ → gᵉ ∘ᵉ ind-emptyᵉ)
          ( Hᵉ Xᵉ)
          ( universal-property-empty'ᵉ Xᵉ))

abstract
  universal-property-empty-is-equiv-ind-emptyᵉ :
    {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-equivᵉ (ind-emptyᵉ {Pᵉ = λ tᵉ → Xᵉ}) →
    ((l'ᵉ : Level) (Yᵉ : UUᵉ l'ᵉ) → is-contrᵉ (Xᵉ → Yᵉ))
  universal-property-empty-is-equiv-ind-emptyᵉ Xᵉ is-equiv-ind-emptyᵉ l'ᵉ Yᵉ =
    is-contr-is-equivᵉ
      ( emptyᵉ → Yᵉ)
      ( λ fᵉ → fᵉ ∘ᵉ ind-emptyᵉ)
      ( is-equiv-precomp-is-equivᵉ ind-emptyᵉ is-equiv-ind-emptyᵉ Yᵉ)
      ( universal-property-empty'ᵉ Yᵉ)
```