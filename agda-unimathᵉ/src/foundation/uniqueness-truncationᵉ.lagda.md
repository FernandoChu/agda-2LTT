# Uniqueness of the truncations

```agda
module foundation.uniqueness-truncationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Theᵉ universalᵉ propertyᵉ ofᵉ `n`-truncationsᵉ impliesᵉ thatᵉ `n`-truncationsᵉ areᵉ
determinedᵉ uniquelyᵉ upᵉ to aᵉ uniqueᵉ equivalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ}
  (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) (fᵉ : Aᵉ → type-Truncated-Typeᵉ Bᵉ)
  (Cᵉ : Truncated-Typeᵉ l3ᵉ kᵉ) (gᵉ : Aᵉ → type-Truncated-Typeᵉ Cᵉ)
  {hᵉ : type-hom-Truncated-Typeᵉ kᵉ Bᵉ Cᵉ} (Hᵉ : (hᵉ ∘ᵉ fᵉ) ~ᵉ gᵉ)
  where

{-ᵉ

  abstract
    is-equiv-is-truncation-is-truncationᵉ :
      is-truncationᵉ Bᵉ fᵉ → is-truncationᵉ Cᵉ gᵉ → is-equivᵉ hᵉ
    is-equiv-is-truncation-is-truncationᵉ Kᵉ Lᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-is-equivᵉ (Lᵉ Bᵉ) fᵉ)
        ( {!!ᵉ})
        {!!ᵉ}

      is-equiv-is-invertibleᵉ
        ( pr1ᵉ (centerᵉ Kᵉ))
        ( htpy-eqᵉ
          ( is-injective-is-equivᵉ
            ( Ugᵉ Cᵉ)
            { hᵉ ∘ᵉ kᵉ}
            { idᵉ}
            ( ( precomp-comp-Set-Quotientᵉ Rᵉ Cᵉ gᵉ Bᵉ kᵉ Cᵉ hᵉ) ∙ᵉ
              ( ( apᵉ (λ tᵉ → precomp-Set-Quotientᵉ Rᵉ Bᵉ tᵉ Cᵉ hᵉ) αᵉ) ∙ᵉ
                ( ( eq-htpy-reflecting-map-equivalence-relationᵉ Rᵉ Cᵉ
                    ( precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Cᵉ hᵉ) gᵉ Hᵉ) ∙ᵉ
                  ( invᵉ (precomp-id-Set-Quotientᵉ Rᵉ Cᵉ gᵉ)))))))
        ( htpy-eqᵉ
          ( is-injective-is-equivᵉ
            ( Ufᵉ Bᵉ)
            { kᵉ ∘ᵉ hᵉ}
            { idᵉ}
            ( ( precomp-comp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Cᵉ hᵉ Bᵉ kᵉ) ∙ᵉ
              ( ( apᵉ
                  ( λ tᵉ → precomp-Set-Quotientᵉ Rᵉ Cᵉ tᵉ Bᵉ kᵉ)
                  ( eq-htpy-reflecting-map-equivalence-relationᵉ Rᵉ Cᵉ
                    ( precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Cᵉ hᵉ) gᵉ Hᵉ)) ∙ᵉ
                ( ( αᵉ) ∙ᵉ
                  ( invᵉ (precomp-id-Set-Quotientᵉ Rᵉ Bᵉ fᵉ)))))))
      where
      Kᵉ : is-contrᵉ
            ( Σᵉ ( type-hom-Setᵉ Cᵉ Bᵉ)
                ( λ hᵉ →
                  ( hᵉ ∘ᵉ map-reflecting-map-equivalence-relationᵉ Rᵉ gᵉ) ~ᵉ
                  ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ)))
      Kᵉ = universal-property-set-quotient-is-set-quotientᵉ Rᵉ Cᵉ gᵉ Ugᵉ Bᵉ fᵉ
      kᵉ : type-Setᵉ Cᵉ → type-Setᵉ Bᵉ
      kᵉ = pr1ᵉ (centerᵉ Kᵉ)
      αᵉ : Idᵉ (precomp-Set-Quotientᵉ Rᵉ Cᵉ gᵉ Bᵉ kᵉ) fᵉ
      αᵉ = eq-htpy-reflecting-map-equivalence-relationᵉ Rᵉ Bᵉ
            ( precomp-Set-Quotientᵉ Rᵉ Cᵉ gᵉ Bᵉ kᵉ)
            ( fᵉ)
            ( pr2ᵉ (centerᵉ Kᵉ))
            -ᵉ}
```

### Uniqueness of set truncations

```agda
{-ᵉ
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ)
  (Cᵉ : Setᵉ l3ᵉ) (gᵉ : Aᵉ → type-Setᵉ Cᵉ) {hᵉ : type-hom-Setᵉ Bᵉ Cᵉ}
  (Hᵉ : (hᵉ ∘ᵉ fᵉ) ~ᵉ gᵉ)
  where

  abstract
    is-equiv-is-set-truncation-is-set-truncationᵉ :
      ({lᵉ : Level} → is-set-truncationᵉ lᵉ Bᵉ fᵉ) →
      ({lᵉ : Level} → is-set-truncationᵉ lᵉ Cᵉ gᵉ) →
      is-equivᵉ hᵉ
    is-equiv-is-set-truncation-is-set-truncationᵉ Sfᵉ Sgᵉ =
      is-equiv-is-set-quotient-is-set-quotientᵉ
        ( mere-eq-equivalence-relationᵉ Aᵉ)
        ( Bᵉ)
        ( reflecting-map-mere-eqᵉ Bᵉ fᵉ)
        ( Cᵉ)
        ( reflecting-map-mere-eqᵉ Cᵉ gᵉ)
        ( Hᵉ)
        ( λ {lᵉ} → is-set-quotient-is-set-truncationᵉ Bᵉ fᵉ Sfᵉ)
        ( λ {lᵉ} → is-set-quotient-is-set-truncationᵉ Cᵉ gᵉ Sgᵉ)

  abstract
    is-set-truncation-is-equiv-is-set-truncationᵉ :
      ({lᵉ : Level} → is-set-truncationᵉ lᵉ Cᵉ gᵉ) → is-equivᵉ hᵉ →
      {lᵉ : Level} → is-set-truncationᵉ lᵉ Bᵉ fᵉ
    is-set-truncation-is-equiv-is-set-truncationᵉ Sgᵉ Ehᵉ =
      is-set-truncation-is-set-quotientᵉ Bᵉ fᵉ
        ( is-set-quotient-is-equiv-is-set-quotientᵉ
          ( mere-eq-equivalence-relationᵉ Aᵉ)
          ( Bᵉ)
          ( reflecting-map-mere-eqᵉ Bᵉ fᵉ)
          ( Cᵉ)
          ( reflecting-map-mere-eqᵉ Cᵉ gᵉ)
          ( Hᵉ)
          ( is-set-quotient-is-set-truncationᵉ Cᵉ gᵉ Sgᵉ)
          ( Ehᵉ))

  abstract
    is-set-truncation-is-set-truncation-is-equivᵉ :
      is-equivᵉ hᵉ → ({lᵉ : Level} → is-set-truncationᵉ lᵉ Bᵉ fᵉ) →
      {lᵉ : Level} → is-set-truncationᵉ lᵉ Cᵉ gᵉ
    is-set-truncation-is-set-truncation-is-equivᵉ Ehᵉ Sfᵉ =
      is-set-truncation-is-set-quotientᵉ Cᵉ gᵉ
        ( is-set-quotient-is-set-quotient-is-equivᵉ
          ( mere-eq-equivalence-relationᵉ Aᵉ)
          ( Bᵉ)
          ( reflecting-map-mere-eqᵉ Bᵉ fᵉ)
          ( Cᵉ)
          ( reflecting-map-mere-eqᵉ Cᵉ gᵉ)
          ( Hᵉ)
          ( Ehᵉ)
          ( is-set-quotient-is-set-truncationᵉ Bᵉ fᵉ Sfᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ)
  (Cᵉ : Setᵉ l3ᵉ) (gᵉ : Aᵉ → type-Setᵉ Cᵉ)
  (Sfᵉ : {lᵉ : Level} → is-set-truncationᵉ lᵉ Bᵉ fᵉ)
  (Sgᵉ : {lᵉ : Level} → is-set-truncationᵉ lᵉ Cᵉ gᵉ)
  where

  abstract
    uniqueness-set-truncationᵉ :
      is-contrᵉ (Σᵉ (type-Setᵉ Bᵉ ≃ᵉ type-Setᵉ Cᵉ) (λ eᵉ → (map-equivᵉ eᵉ ∘ᵉ fᵉ) ~ᵉ gᵉ))
    uniqueness-set-truncationᵉ =
      uniqueness-set-quotientᵉ
        ( mere-eq-equivalence-relationᵉ Aᵉ)
        ( Bᵉ)
        ( reflecting-map-mere-eqᵉ Bᵉ fᵉ)
        ( is-set-quotient-is-set-truncationᵉ Bᵉ fᵉ Sfᵉ)
        ( Cᵉ)
        ( reflecting-map-mere-eqᵉ Cᵉ gᵉ)
        ( is-set-quotient-is-set-truncationᵉ Cᵉ gᵉ Sgᵉ)

  equiv-uniqueness-set-truncationᵉ : type-Setᵉ Bᵉ ≃ᵉ type-Setᵉ Cᵉ
  equiv-uniqueness-set-truncationᵉ =
    pr1ᵉ (centerᵉ uniqueness-set-truncationᵉ)

  map-equiv-uniqueness-set-truncationᵉ : type-Setᵉ Bᵉ → type-Setᵉ Cᵉ
  map-equiv-uniqueness-set-truncationᵉ =
    map-equivᵉ equiv-uniqueness-set-truncationᵉ

  triangle-uniqueness-set-truncationᵉ :
    (map-equiv-uniqueness-set-truncationᵉ ∘ᵉ fᵉ) ~ᵉ gᵉ
  triangle-uniqueness-set-truncationᵉ =
    pr2ᵉ (centerᵉ uniqueness-set-truncationᵉ)
-ᵉ}
```