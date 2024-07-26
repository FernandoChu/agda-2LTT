# The universal property of truncations

```agda
module foundation.universal-property-truncationᵉ where

open import foundation-core.universal-property-truncationᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.type-arithmetic-dependent-function-typesᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universal-property-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Properties

### A map `f : A → B` is a `k+1`-truncation if and only if it is surjective and `ap f : (x ＝ y) → (f x ＝ f y)` is a `k`-truncation for all `x y : A`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Truncated-Typeᵉ l2ᵉ (succ-𝕋ᵉ kᵉ))
  {fᵉ : Aᵉ → type-Truncated-Typeᵉ Bᵉ} (Hᵉ : is-surjectiveᵉ fᵉ)
  ( Kᵉ :
    (xᵉ yᵉ : Aᵉ) → is-truncationᵉ (Id-Truncated-Typeᵉ Bᵉ (fᵉ xᵉ) (fᵉ yᵉ)) (apᵉ fᵉ {xᵉ} {yᵉ}))
  where

  unique-extension-fiber-is-truncation-is-truncation-apᵉ :
    {lᵉ : Level} (Cᵉ : Truncated-Typeᵉ lᵉ (succ-𝕋ᵉ kᵉ))
    (gᵉ : Aᵉ → type-Truncated-Typeᵉ Cᵉ) (yᵉ : type-Truncated-Typeᵉ Bᵉ) →
    is-contrᵉ
      ( Σᵉ ( type-Truncated-Typeᵉ Cᵉ)
          ( λ zᵉ → (tᵉ : fiberᵉ fᵉ yᵉ) → gᵉ (pr1ᵉ tᵉ) ＝ᵉ zᵉ))
  unique-extension-fiber-is-truncation-is-truncation-apᵉ Cᵉ gᵉ =
    apply-dependent-universal-property-surjection-is-surjectiveᵉ fᵉ Hᵉ
      ( λ yᵉ → is-contr-Propᵉ _)
      ( λ xᵉ →
        is-contr-equivᵉ
          ( Σᵉ (type-Truncated-Typeᵉ Cᵉ) (λ zᵉ → gᵉ xᵉ ＝ᵉ zᵉ))
          ( equiv-totᵉ
            ( λ zᵉ →
              ( ( equiv-ev-refl'ᵉ xᵉ) ∘eᵉ
                ( equiv-Π-equiv-familyᵉ
                  ( λ x'ᵉ →
                    equiv-is-truncationᵉ
                      ( Id-Truncated-Typeᵉ Bᵉ (fᵉ x'ᵉ) (fᵉ xᵉ))
                      ( apᵉ fᵉ)
                      ( Kᵉ x'ᵉ xᵉ)
                      ( Id-Truncated-Typeᵉ Cᵉ (gᵉ x'ᵉ) zᵉ)))) ∘eᵉ
              ( equiv-ev-pairᵉ)))
          ( is-torsorial-Idᵉ (gᵉ xᵉ)))

  is-truncation-is-truncation-apᵉ :
    is-truncationᵉ Bᵉ fᵉ
  is-truncation-is-truncation-apᵉ Cᵉ =
    is-equiv-is-contr-mapᵉ
      ( λ gᵉ →
        is-contr-equiv'ᵉ
          ( (yᵉ : type-Truncated-Typeᵉ Bᵉ) →
            Σᵉ ( type-Truncated-Typeᵉ Cᵉ)
              ( λ zᵉ → (tᵉ : fiberᵉ fᵉ yᵉ) → (gᵉ (pr1ᵉ tᵉ) ＝ᵉ zᵉ)))
          ( ( equiv-totᵉ
              ( λ hᵉ →
                ( ( ( inv-equivᵉ (equiv-funextᵉ)) ∘eᵉ
                    ( equiv-Π-equiv-familyᵉ
                      ( λ xᵉ →
                        equiv-invᵉ (gᵉ xᵉ) (hᵉ (fᵉ xᵉ)) ∘eᵉ equiv-ev-reflᵉ (fᵉ xᵉ)))) ∘eᵉ
                  ( equiv-swap-Πᵉ)) ∘eᵉ
                ( equiv-Π-equiv-familyᵉ (λ xᵉ → equiv-ev-pairᵉ)))) ∘eᵉ
            ( distributive-Π-Σᵉ))
          ( is-contr-Πᵉ
            ( unique-extension-fiber-is-truncation-is-truncation-apᵉ Cᵉ gᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Truncated-Typeᵉ l2ᵉ (succ-𝕋ᵉ kᵉ))
  {fᵉ : Aᵉ → type-Truncated-Typeᵉ Bᵉ}
  where

  is-surjective-is-truncationᵉ :
    is-truncationᵉ Bᵉ fᵉ → is-surjectiveᵉ fᵉ
  is-surjective-is-truncationᵉ Hᵉ =
    map-inv-is-equivᵉ
      ( dependent-universal-property-truncation-is-truncationᵉ Bᵉ fᵉ Hᵉ
        ( λ yᵉ → truncated-type-trunc-Propᵉ kᵉ (fiberᵉ fᵉ yᵉ)))
      ( λ xᵉ → unit-trunc-Propᵉ (pairᵉ xᵉ reflᵉ))
```