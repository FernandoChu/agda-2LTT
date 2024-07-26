# The universal property of dependent function types

```agda
module foundation.universal-property-dependent-function-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.spans-families-of-typesᵉ
open import foundation.terminal-spans-families-of-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ familyᵉ ofᵉ typesᵉ `B`ᵉ overᵉ `A`.ᵉ Thenᵉ theᵉ dependentᵉ functionᵉ typeᵉ
`(aᵉ : Aᵉ) → Bᵉ a`ᵉ naturallyᵉ hasᵉ theᵉ structureᵉ ofᵉ aᵉ
[span](foundation.spans-families-of-types.mdᵉ) onᵉ theᵉ familyᵉ ofᵉ typesᵉ `B`ᵉ overᵉ
`A`,ᵉ where forᵉ eachᵉ `aᵉ : A`ᵉ theᵉ mapᵉ

```text
  ((xᵉ : Aᵉ) → Bᵉ xᵉ) → Bᵉ aᵉ
```

isᵉ givenᵉ byᵉ evaluationᵉ atᵉ `a`.ᵉ

Aᵉ spanᵉ `𝒮ᵉ :=ᵉ (Sᵉ ,ᵉ f)`ᵉ isᵉ saidᵉ to satisfyᵉ theᵉ
{{#conceptᵉ "universalᵉ propertyᵉ ofᵉ dependentᵉ functionᵉ types"ᵉ Agda=universal-property-dependent-function-typesᵉ}}
ifᵉ forᵉ anyᵉ typeᵉ `T`ᵉ theᵉ mapᵉ

```text
  (Tᵉ → Sᵉ) → ((xᵉ : Aᵉ) → Tᵉ → Bᵉ xᵉ)
```

givenᵉ byᵉ `hᵉ ↦ᵉ λ xᵉ tᵉ → fᵉ xᵉ (hᵉ t)`ᵉ isᵉ anᵉ
[equivalence](foundation-core.equivalences.md).ᵉ Theᵉ dependentᵉ functionᵉ typeᵉ
`(xᵉ : Aᵉ) → Bᵉ x`ᵉ equippedᵉ with theᵉ spanᵉ structureᵉ definedᵉ aboveᵉ satisfiesᵉ theᵉ
universalᵉ propertyᵉ ofᵉ dependentᵉ functionᵉ types.ᵉ

Inᵉ
[`foundation.dependent-function-types`](foundation.dependent-function-types.mdᵉ)
weᵉ showᵉ thatᵉ dependentᵉ functionᵉ typesᵉ satisfyᵉ theᵉ universalᵉ propertyᵉ ofᵉ
dependentᵉ functionᵉ types.ᵉ Inᵉ thisᵉ fileᵉ weᵉ alsoᵉ showᵉ thatᵉ theᵉ universalᵉ propertyᵉ
ofᵉ dependentᵉ functionᵉ typesᵉ isᵉ equivalentᵉ to beingᵉ aᵉ
[terminalᵉ span](foundation.terminal-spans-families-of-types.mdᵉ) onᵉ theᵉ typeᵉ
familyᵉ `B`.ᵉ

## Definitions

### The universal property of dependent function types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (𝒮ᵉ : span-type-familyᵉ l3ᵉ Bᵉ)
  where

  ev-span-type-familyᵉ :
    {lᵉ : Level} (Tᵉ : UUᵉ lᵉ) →
    (Tᵉ → spanning-type-span-type-familyᵉ 𝒮ᵉ) → (xᵉ : Aᵉ) → Tᵉ → Bᵉ xᵉ
  ev-span-type-familyᵉ Tᵉ hᵉ xᵉ tᵉ = map-span-type-familyᵉ 𝒮ᵉ xᵉ (hᵉ tᵉ)

  universal-property-dependent-function-typesᵉ : UUωᵉ
  universal-property-dependent-function-typesᵉ =
    {lᵉ : Level} (Tᵉ : UUᵉ lᵉ) → is-equivᵉ (ev-span-type-familyᵉ Tᵉ)
```

## Properties

### A span on a family of types satisfies the universal property of dependent function types if and only if it is terminal

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (𝒮ᵉ : span-type-familyᵉ l3ᵉ Bᵉ)
  where

  abstract
    is-terminal-universal-property-dependent-function-typesᵉ :
      universal-property-dependent-function-typesᵉ 𝒮ᵉ →
      is-terminal-span-type-familyᵉ 𝒮ᵉ
    is-terminal-universal-property-dependent-function-typesᵉ Uᵉ 𝒯ᵉ =
      is-contr-equiv'ᵉ _
        ( equiv-totᵉ
          ( λ hᵉ →
            ( equiv-Π-equiv-familyᵉ
              ( λ aᵉ →
                ( equiv-Π-equiv-familyᵉ (λ tᵉ → equiv-invᵉ _ _)) ∘eᵉ
                ( equiv-funextᵉ))) ∘eᵉ
            ( equiv-funextᵉ)))
        ( is-contr-map-is-equivᵉ
          ( Uᵉ (spanning-type-span-type-familyᵉ 𝒯ᵉ))
          ( map-span-type-familyᵉ 𝒯ᵉ))

  abstract
    universal-property-dependent-function-types-is-terminalᵉ :
      is-terminal-span-type-familyᵉ 𝒮ᵉ →
      universal-property-dependent-function-typesᵉ 𝒮ᵉ
    universal-property-dependent-function-types-is-terminalᵉ Uᵉ Tᵉ =
      is-equiv-is-contr-mapᵉ
        ( λ gᵉ →
          is-contr-equivᵉ _
            ( equiv-totᵉ
              ( λ hᵉ →
                ( equiv-Π-equiv-familyᵉ
                  ( λ aᵉ →
                    ( equiv-Π-equiv-familyᵉ (λ tᵉ → equiv-invᵉ _ _)) ∘eᵉ
                    ( equiv-funextᵉ))) ∘eᵉ
                ( equiv-funextᵉ)))
            ( Uᵉ (Tᵉ ,ᵉ gᵉ)))
```

## See also

-ᵉ [Dependentᵉ functionᵉ types](foundation.dependent-function-types.mdᵉ)