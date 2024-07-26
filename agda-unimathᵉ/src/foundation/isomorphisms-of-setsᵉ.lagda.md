# Isomorphisms of sets

```agda
module foundation.isomorphisms-of-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Idea

Sinceᵉ equalityᵉ ofᵉ elementsᵉ in aᵉ setᵉ isᵉ aᵉ proposition,ᵉ isomorphismsᵉ ofᵉ setsᵉ areᵉ
equivalentᵉ to equivalencesᵉ ofᵉ setsᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) (Bᵉ : Setᵉ l2ᵉ)
  where

  is-iso-Setᵉ : (fᵉ : hom-Setᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-Setᵉ fᵉ = Σᵉ (hom-Setᵉ Bᵉ Aᵉ) (λ gᵉ → ((fᵉ ∘ᵉ gᵉ) ＝ᵉ idᵉ) ×ᵉ ((gᵉ ∘ᵉ fᵉ) ＝ᵉ idᵉ))

  iso-Setᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  iso-Setᵉ = Σᵉ (hom-Setᵉ Aᵉ Bᵉ) is-iso-Setᵉ

  map-iso-Setᵉ : iso-Setᵉ → type-Setᵉ Aᵉ → type-Setᵉ Bᵉ
  map-iso-Setᵉ = pr1ᵉ

  is-iso-map-iso-Setᵉ : (fᵉ : iso-Setᵉ) → is-iso-Setᵉ (map-iso-Setᵉ fᵉ)
  is-iso-map-iso-Setᵉ = pr2ᵉ

  is-proof-irrelevant-is-iso-Setᵉ :
    (fᵉ : hom-Setᵉ Aᵉ Bᵉ) → is-proof-irrelevantᵉ (is-iso-Setᵉ fᵉ)
  pr1ᵉ (is-proof-irrelevant-is-iso-Setᵉ fᵉ Hᵉ) = Hᵉ
  pr2ᵉ (is-proof-irrelevant-is-iso-Setᵉ fᵉ (gᵉ ,ᵉ pᵉ ,ᵉ qᵉ)) (g'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) =
    eq-type-subtypeᵉ
      ( λ hᵉ →
        product-Propᵉ
          ( Id-Propᵉ (hom-set-Setᵉ Bᵉ Bᵉ) (fᵉ ∘ᵉ hᵉ) idᵉ)
          ( Id-Propᵉ (hom-set-Setᵉ Aᵉ Aᵉ) (hᵉ ∘ᵉ fᵉ) idᵉ))
      ( ( apᵉ (λ hᵉ → gᵉ ∘ᵉ hᵉ) (invᵉ p'ᵉ)) ∙ᵉ
        ( apᵉ (λ hᵉ → hᵉ ∘ᵉ g'ᵉ) qᵉ))

  is-prop-is-iso-Setᵉ : (fᵉ : hom-Setᵉ Aᵉ Bᵉ) → is-propᵉ (is-iso-Setᵉ fᵉ)
  is-prop-is-iso-Setᵉ fᵉ =
    is-prop-is-proof-irrelevantᵉ (is-proof-irrelevant-is-iso-Setᵉ fᵉ)

  is-iso-is-equiv-Setᵉ : {fᵉ : hom-Setᵉ Aᵉ Bᵉ} → is-equivᵉ fᵉ → is-iso-Setᵉ fᵉ
  pr1ᵉ (is-iso-is-equiv-Setᵉ Hᵉ) = map-inv-is-equivᵉ Hᵉ
  pr1ᵉ (pr2ᵉ (is-iso-is-equiv-Setᵉ Hᵉ)) = eq-htpyᵉ (is-section-map-inv-is-equivᵉ Hᵉ)
  pr2ᵉ (pr2ᵉ (is-iso-is-equiv-Setᵉ Hᵉ)) = eq-htpyᵉ (is-retraction-map-inv-is-equivᵉ Hᵉ)

  is-equiv-is-iso-Setᵉ : {fᵉ : hom-Setᵉ Aᵉ Bᵉ} → is-iso-Setᵉ fᵉ → is-equivᵉ fᵉ
  is-equiv-is-iso-Setᵉ Hᵉ =
    is-equiv-is-invertibleᵉ
      ( pr1ᵉ Hᵉ)
      ( htpy-eqᵉ (pr1ᵉ (pr2ᵉ Hᵉ)))
      ( htpy-eqᵉ (pr2ᵉ (pr2ᵉ Hᵉ)))

  iso-equiv-Setᵉ : equiv-Setᵉ Aᵉ Bᵉ → iso-Setᵉ
  pr1ᵉ (iso-equiv-Setᵉ eᵉ) = map-equivᵉ eᵉ
  pr2ᵉ (iso-equiv-Setᵉ eᵉ) = is-iso-is-equiv-Setᵉ (is-equiv-map-equivᵉ eᵉ)

  equiv-iso-Setᵉ : iso-Setᵉ → equiv-Setᵉ Aᵉ Bᵉ
  pr1ᵉ (equiv-iso-Setᵉ fᵉ) = map-iso-Setᵉ fᵉ
  pr2ᵉ (equiv-iso-Setᵉ fᵉ) = is-equiv-is-iso-Setᵉ (is-iso-map-iso-Setᵉ fᵉ)

  equiv-iso-equiv-Setᵉ : equiv-Setᵉ Aᵉ Bᵉ ≃ᵉ iso-Setᵉ
  equiv-iso-equiv-Setᵉ =
    equiv-type-subtypeᵉ
      ( is-property-is-equivᵉ)
      ( is-prop-is-iso-Setᵉ)
      ( λ fᵉ → is-iso-is-equiv-Setᵉ)
      ( λ fᵉ → is-equiv-is-iso-Setᵉ)
```