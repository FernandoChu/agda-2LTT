# The universal property of coproduct types

```agda
module foundation.universal-property-coproduct-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-functionsᵉ
```

</details>

## Idea

Theᵉ universalᵉ propertyᵉ andᵉ dependentᵉ universalᵉ propertyᵉ ofᵉ coproductᵉ typesᵉ
characterizeᵉ mapsᵉ andᵉ dependentᵉ functionsᵉ outᵉ ofᵉ coproductᵉ types.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  ev-inl-inrᵉ :
    {l3ᵉ : Level} (Pᵉ : Aᵉ +ᵉ Bᵉ → UUᵉ l3ᵉ) →
    ((tᵉ : Aᵉ +ᵉ Bᵉ) → Pᵉ tᵉ) → ((xᵉ : Aᵉ) → Pᵉ (inlᵉ xᵉ)) ×ᵉ ((yᵉ : Bᵉ) → Pᵉ (inrᵉ yᵉ))
  pr1ᵉ (ev-inl-inrᵉ Pᵉ sᵉ) xᵉ = sᵉ (inlᵉ xᵉ)
  pr2ᵉ (ev-inl-inrᵉ Pᵉ sᵉ) yᵉ = sᵉ (inrᵉ yᵉ)

  dependent-universal-property-coproductᵉ :
    {l3ᵉ : Level} (Pᵉ : Aᵉ +ᵉ Bᵉ → UUᵉ l3ᵉ) → is-equivᵉ (ev-inl-inrᵉ Pᵉ)
  dependent-universal-property-coproductᵉ Pᵉ =
    is-equiv-is-invertibleᵉ
      ( λ pᵉ → ind-coproductᵉ Pᵉ (pr1ᵉ pᵉ) (pr2ᵉ pᵉ))
      ( ind-Σᵉ (λ fᵉ gᵉ → eq-pairᵉ reflᵉ reflᵉ))
      ( λ sᵉ → eq-htpyᵉ (ind-coproductᵉ _ refl-htpyᵉ refl-htpyᵉ))

  equiv-dependent-universal-property-coproductᵉ :
    {l3ᵉ : Level} (Pᵉ : Aᵉ +ᵉ Bᵉ → UUᵉ l3ᵉ) →
    ((xᵉ : Aᵉ +ᵉ Bᵉ) → Pᵉ xᵉ) ≃ᵉ (((aᵉ : Aᵉ) → Pᵉ (inlᵉ aᵉ)) ×ᵉ ((bᵉ : Bᵉ) → Pᵉ (inrᵉ bᵉ)))
  pr1ᵉ (equiv-dependent-universal-property-coproductᵉ Pᵉ) = ev-inl-inrᵉ Pᵉ
  pr2ᵉ (equiv-dependent-universal-property-coproductᵉ Pᵉ) =
    dependent-universal-property-coproductᵉ Pᵉ

  abstract
    universal-property-coproductᵉ :
      {l3ᵉ : Level} (Xᵉ : UUᵉ l3ᵉ) → is-equivᵉ (ev-inl-inrᵉ (λ _ → Xᵉ))
    universal-property-coproductᵉ Xᵉ =
      dependent-universal-property-coproductᵉ (λ _ → Xᵉ)

  equiv-universal-property-coproductᵉ :
    {l3ᵉ : Level} (Xᵉ : UUᵉ l3ᵉ) → (Aᵉ +ᵉ Bᵉ → Xᵉ) ≃ᵉ ((Aᵉ → Xᵉ) ×ᵉ (Bᵉ → Xᵉ))
  equiv-universal-property-coproductᵉ Xᵉ =
    equiv-dependent-universal-property-coproductᵉ (λ _ → Xᵉ)

  abstract
    uniqueness-coproductᵉ :
      {l3ᵉ : Level} {Yᵉ : UUᵉ l3ᵉ} (iᵉ : Aᵉ → Yᵉ) (jᵉ : Bᵉ → Yᵉ) →
      ( {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) →
        is-equivᵉ (λ (sᵉ : Yᵉ → Xᵉ) → pair'ᵉ (sᵉ ∘ᵉ iᵉ) (sᵉ ∘ᵉ jᵉ))) →
      is-equivᵉ (rec-coproductᵉ iᵉ jᵉ)
    uniqueness-coproductᵉ iᵉ jᵉ Hᵉ =
      is-equiv-is-equiv-precompᵉ
        ( rec-coproductᵉ iᵉ jᵉ)
        ( λ Xᵉ →
          is-equiv-right-factorᵉ
            ( ev-inl-inrᵉ (λ _ → Xᵉ))
            ( precompᵉ (rec-coproductᵉ iᵉ jᵉ) Xᵉ)
            ( universal-property-coproductᵉ Xᵉ)
            ( Hᵉ Xᵉ))

  abstract
    universal-property-coproduct-is-equiv-rec-coproductᵉ :
      {l3ᵉ : Level} (Xᵉ : UUᵉ l3ᵉ) (iᵉ : Aᵉ → Xᵉ) (jᵉ : Bᵉ → Xᵉ) →
      is-equivᵉ (rec-coproductᵉ iᵉ jᵉ) →
      (l4ᵉ : Level) (Yᵉ : UUᵉ l4ᵉ) →
      is-equivᵉ (λ (sᵉ : Xᵉ → Yᵉ) → pair'ᵉ (sᵉ ∘ᵉ iᵉ) (sᵉ ∘ᵉ jᵉ))
    universal-property-coproduct-is-equiv-rec-coproductᵉ Xᵉ iᵉ jᵉ Hᵉ lᵉ Yᵉ =
      is-equiv-compᵉ
        ( ev-inl-inrᵉ (λ _ → Yᵉ))
        ( precompᵉ (rec-coproductᵉ iᵉ jᵉ) Yᵉ)
        ( is-equiv-precomp-is-equivᵉ
          ( rec-coproductᵉ iᵉ jᵉ)
          ( Hᵉ)
          ( Yᵉ))
        ( universal-property-coproductᵉ Yᵉ)
```