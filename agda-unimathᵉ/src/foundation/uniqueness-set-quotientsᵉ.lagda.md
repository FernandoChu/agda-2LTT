# The uniqueness of set quotients

```agda
module foundation.uniqueness-set-quotientsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalence-relationsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.precomposition-functionsᵉ
```

</details>

## Idea

Theᵉ universalᵉ propertyᵉ ofᵉ setᵉ quotientsᵉ impliesᵉ thatᵉ setᵉ quotientsᵉ areᵉ uniquelyᵉ
unique.ᵉ

## Properties

### Uniqueness of set quotients

```agda
precomp-comp-Set-Quotientᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (Bᵉ : Setᵉ l3ᵉ) (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ))
  (Cᵉ : Setᵉ l4ᵉ) (gᵉ : hom-Setᵉ Bᵉ Cᵉ)
  (Dᵉ : Setᵉ l5ᵉ) (hᵉ : hom-Setᵉ Cᵉ Dᵉ) →
  ( precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Dᵉ (hᵉ ∘ᵉ gᵉ)) ＝ᵉ
  ( precomp-Set-Quotientᵉ Rᵉ Cᵉ (precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Cᵉ gᵉ) Dᵉ hᵉ)
precomp-comp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Cᵉ gᵉ Dᵉ hᵉ =
  eq-htpy-reflecting-map-equivalence-relationᵉ Rᵉ Dᵉ
    ( precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Dᵉ (hᵉ ∘ᵉ gᵉ))
    ( precomp-Set-Quotientᵉ Rᵉ Cᵉ (precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Cᵉ gᵉ) Dᵉ hᵉ)
    ( refl-htpyᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (Bᵉ : Setᵉ l3ᵉ) (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ))
  (Cᵉ : Setᵉ l4ᵉ) (gᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Cᵉ))
  {hᵉ : type-Setᵉ Bᵉ → type-Setᵉ Cᵉ}
  (Hᵉ :
    (hᵉ ∘ᵉ map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ) ~ᵉ
    map-reflecting-map-equivalence-relationᵉ Rᵉ gᵉ)
  where

  map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ :
    is-set-quotientᵉ Rᵉ Bᵉ fᵉ →
    is-set-quotientᵉ Rᵉ Cᵉ gᵉ →
    type-Setᵉ Cᵉ → type-Setᵉ Bᵉ
  map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ =
    map-universal-property-set-quotient-is-set-quotientᵉ Rᵉ Cᵉ gᵉ Ugᵉ Bᵉ fᵉ

  is-section-map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ :
    ( Ufᵉ : is-set-quotientᵉ Rᵉ Bᵉ fᵉ) →
    ( Ugᵉ : is-set-quotientᵉ Rᵉ Cᵉ gᵉ) →
    ( hᵉ ∘ᵉ map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ) ~ᵉ idᵉ
  is-section-map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ =
    htpy-eqᵉ
      ( is-injective-is-equivᵉ
      ( Ugᵉ Cᵉ)
      { hᵉ ∘ᵉ map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ}
      { idᵉ}
      ( ( precomp-comp-Set-Quotientᵉ Rᵉ Cᵉ gᵉ Bᵉ
          ( map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ)
          ( Cᵉ)
          ( hᵉ)) ∙ᵉ
        ( ( apᵉ
            ( λ tᵉ → precomp-Set-Quotientᵉ Rᵉ Bᵉ tᵉ Cᵉ hᵉ)
            ( eq-htpy-reflecting-map-equivalence-relationᵉ Rᵉ Bᵉ
              ( precomp-Set-Quotientᵉ Rᵉ Cᵉ gᵉ Bᵉ
                ( map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ))
              ( fᵉ)
              ( triangle-universal-property-set-quotient-is-set-quotientᵉ
                Rᵉ Cᵉ gᵉ Ugᵉ Bᵉ fᵉ))) ∙ᵉ
          ( ( eq-htpy-reflecting-map-equivalence-relationᵉ Rᵉ Cᵉ
              ( precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Cᵉ hᵉ) gᵉ Hᵉ) ∙ᵉ
            ( invᵉ (precomp-id-Set-Quotientᵉ Rᵉ Cᵉ gᵉ))))))

  is-retraction-map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ :
    ( Ufᵉ : is-set-quotientᵉ Rᵉ Bᵉ fᵉ) →
    ( Ugᵉ : is-set-quotientᵉ Rᵉ Cᵉ gᵉ) →
    ( map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ ∘ᵉ hᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ =
    htpy-eqᵉ
      ( is-injective-is-equivᵉ
      ( Ufᵉ Bᵉ)
      { map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ ∘ᵉ hᵉ}
      { idᵉ}
      ( ( precomp-comp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Cᵉ hᵉ Bᵉ
          ( map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ)) ∙ᵉ
        ( ( apᵉ
            ( λ tᵉ →
              precomp-Set-Quotientᵉ Rᵉ Cᵉ tᵉ Bᵉ
                ( map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ))
            ( eq-htpy-reflecting-map-equivalence-relationᵉ Rᵉ Cᵉ
              ( precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Cᵉ hᵉ)
              ( gᵉ)
              ( Hᵉ))) ∙ᵉ
          ( ( eq-htpy-reflecting-map-equivalence-relationᵉ Rᵉ Bᵉ
              ( precomp-Set-Quotientᵉ Rᵉ Cᵉ gᵉ Bᵉ
                ( map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ))
              ( fᵉ)
              ( triangle-universal-property-set-quotient-is-set-quotientᵉ
                Rᵉ Cᵉ gᵉ Ugᵉ Bᵉ fᵉ)) ∙ᵉ
            ( invᵉ (precomp-id-Set-Quotientᵉ Rᵉ Bᵉ fᵉ))))))

  is-equiv-is-set-quotient-is-set-quotientᵉ :
    is-set-quotientᵉ Rᵉ Bᵉ fᵉ →
    is-set-quotientᵉ Rᵉ Cᵉ gᵉ →
    is-equivᵉ hᵉ
  is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ)
      ( is-section-map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ)
      ( is-retraction-map-inv-is-equiv-is-set-quotient-is-set-quotientᵉ Ufᵉ Ugᵉ)

  is-set-quotient-is-set-quotient-is-equivᵉ :
    is-equivᵉ hᵉ → is-set-quotientᵉ Rᵉ Bᵉ fᵉ → is-set-quotientᵉ Rᵉ Cᵉ gᵉ
  is-set-quotient-is-set-quotient-is-equivᵉ Eᵉ Ufᵉ {lᵉ} Xᵉ =
    is-equiv-left-map-triangleᵉ
      ( precomp-Set-Quotientᵉ Rᵉ Cᵉ gᵉ Xᵉ)
      ( precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Xᵉ)
      ( precompᵉ hᵉ (type-Setᵉ Xᵉ))
      ( λ kᵉ →
        eq-htpy-reflecting-map-equivalence-relationᵉ Rᵉ Xᵉ
          ( precomp-Set-Quotientᵉ Rᵉ Cᵉ gᵉ Xᵉ kᵉ)
          ( precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Xᵉ (kᵉ ∘ᵉ hᵉ))
          ( inv-htpyᵉ (kᵉ ·lᵉ Hᵉ)))
      ( is-equiv-precomp-is-equivᵉ hᵉ Eᵉ (type-Setᵉ Xᵉ))
      ( Ufᵉ Xᵉ)

  is-set-quotient-is-equiv-is-set-quotientᵉ :
    is-set-quotientᵉ Rᵉ Cᵉ gᵉ → is-equivᵉ hᵉ → is-set-quotientᵉ Rᵉ Bᵉ fᵉ
  is-set-quotient-is-equiv-is-set-quotientᵉ Ugᵉ Eᵉ {lᵉ} Xᵉ =
    is-equiv-right-map-triangleᵉ
      ( precomp-Set-Quotientᵉ Rᵉ Cᵉ gᵉ Xᵉ)
      ( precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Xᵉ)
      ( precompᵉ hᵉ (type-Setᵉ Xᵉ))
      ( λ kᵉ →
        eq-htpy-reflecting-map-equivalence-relationᵉ Rᵉ Xᵉ
          ( precomp-Set-Quotientᵉ Rᵉ Cᵉ gᵉ Xᵉ kᵉ)
          ( precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Xᵉ (kᵉ ∘ᵉ hᵉ))
          ( inv-htpyᵉ (kᵉ ·lᵉ Hᵉ)))
      ( Ugᵉ Xᵉ)
      ( is-equiv-precomp-is-equivᵉ hᵉ Eᵉ (type-Setᵉ Xᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (Bᵉ : Setᵉ l3ᵉ) (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ))
  (Ufᵉ : is-set-quotientᵉ Rᵉ Bᵉ fᵉ)
  (Cᵉ : Setᵉ l4ᵉ) (gᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Cᵉ))
  (Ugᵉ : is-set-quotientᵉ Rᵉ Cᵉ gᵉ)
  where

  uniqueness-set-quotientᵉ :
    is-contrᵉ
      ( Σᵉ ( type-Setᵉ Bᵉ ≃ᵉ type-Setᵉ Cᵉ)
          ( λ eᵉ →
            ( map-equivᵉ eᵉ ∘ᵉ map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ) ~ᵉ
            ( map-reflecting-map-equivalence-relationᵉ Rᵉ gᵉ)))
  uniqueness-set-quotientᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( universal-property-set-quotient-is-set-quotientᵉ Rᵉ Bᵉ fᵉ Ufᵉ Cᵉ gᵉ)
      ( is-property-is-equivᵉ)
      ( map-universal-property-set-quotient-is-set-quotientᵉ Rᵉ Bᵉ fᵉ Ufᵉ Cᵉ gᵉ)
      ( triangle-universal-property-set-quotient-is-set-quotientᵉ Rᵉ Bᵉ fᵉ Ufᵉ Cᵉ gᵉ)
      ( is-equiv-is-set-quotient-is-set-quotientᵉ Rᵉ Bᵉ fᵉ Cᵉ gᵉ
        ( triangle-universal-property-set-quotient-is-set-quotientᵉ
          Rᵉ Bᵉ fᵉ Ufᵉ Cᵉ gᵉ)
        ( Ufᵉ)
        ( Ugᵉ))

  equiv-uniqueness-set-quotientᵉ : type-Setᵉ Bᵉ ≃ᵉ type-Setᵉ Cᵉ
  equiv-uniqueness-set-quotientᵉ =
    pr1ᵉ (centerᵉ uniqueness-set-quotientᵉ)

  map-equiv-uniqueness-set-quotientᵉ : type-Setᵉ Bᵉ → type-Setᵉ Cᵉ
  map-equiv-uniqueness-set-quotientᵉ = map-equivᵉ equiv-uniqueness-set-quotientᵉ

  triangle-uniqueness-set-quotientᵉ :
    ( map-equiv-uniqueness-set-quotientᵉ ∘ᵉ
      map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ) ~ᵉ
    ( map-reflecting-map-equivalence-relationᵉ Rᵉ gᵉ)
  triangle-uniqueness-set-quotientᵉ =
    pr2ᵉ (centerᵉ uniqueness-set-quotientᵉ)
```