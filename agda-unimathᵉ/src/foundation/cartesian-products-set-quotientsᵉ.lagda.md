# Cartesian products of set quotients

```agda
module foundation.cartesian-products-set-quotientsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.products-equivalence-relationsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.set-quotientsᵉ
open import foundation.setsᵉ
open import foundation.uniqueness-set-quotientsᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalence-relationsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Givenᵉ twoᵉ typesᵉ `A`ᵉ andᵉ `B`,ᵉ equippedᵉ with equivalenceᵉ relationsᵉ `R`ᵉ andᵉ `S`,ᵉ
respectively,ᵉ theᵉ cartesianᵉ productᵉ ofᵉ theirᵉ setᵉ quotientsᵉ isᵉ theᵉ setᵉ quotientᵉ
ofᵉ theirᵉ product.ᵉ

## Definition

### The product of two relations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  where

  product-set-quotient-Setᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  product-set-quotient-Setᵉ = product-Setᵉ (quotient-Setᵉ Rᵉ) (quotient-Setᵉ Sᵉ)

  product-set-quotientᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  product-set-quotientᵉ = pr1ᵉ product-set-quotient-Setᵉ

  is-set-product-set-quotientᵉ : is-setᵉ product-set-quotientᵉ
  is-set-product-set-quotientᵉ = pr2ᵉ product-set-quotient-Setᵉ

  product-set-quotient-mapᵉ : (Aᵉ ×ᵉ Bᵉ) → product-set-quotientᵉ
  product-set-quotient-mapᵉ (aᵉ ,ᵉ bᵉ) =
    pairᵉ (quotient-mapᵉ Rᵉ aᵉ) (quotient-mapᵉ Sᵉ bᵉ)

  reflecting-map-product-quotient-mapᵉ :
    reflecting-map-equivalence-relationᵉ
      ( product-equivalence-relationᵉ Rᵉ Sᵉ)
      ( product-set-quotientᵉ)
  reflecting-map-product-quotient-mapᵉ =
    pairᵉ
      product-set-quotient-mapᵉ
      ( λ (pᵉ ,ᵉ qᵉ) →
        ( eq-pairᵉ
          ( apply-effectiveness-quotient-map'ᵉ Rᵉ pᵉ)
          ( apply-effectiveness-quotient-map'ᵉ Sᵉ qᵉ)))
```

## Properties

### The product of sets quotients is a set quotient

```agda
  inv-precomp-set-quotient-product-set-quotientᵉ :
    {lᵉ : Level}
    (Xᵉ : Setᵉ lᵉ) →
    reflecting-map-equivalence-relationᵉ
      ( product-equivalence-relationᵉ Rᵉ Sᵉ)
      ( type-Setᵉ Xᵉ) →
    hom-Setᵉ product-set-quotient-Setᵉ Xᵉ
  inv-precomp-set-quotient-product-set-quotientᵉ Xᵉ (fᵉ ,ᵉ Hᵉ) (qaᵉ ,ᵉ qbᵉ) =
    inv-precomp-set-quotientᵉ
      ( Rᵉ)
      ( hom-set-Setᵉ (quotient-Setᵉ Sᵉ) Xᵉ)
      ( pairᵉ
        ( λ aᵉ qb'ᵉ →
          inv-precomp-set-quotientᵉ Sᵉ Xᵉ
            ( pairᵉ
              (λ bᵉ → fᵉ (aᵉ ,ᵉ bᵉ))
              (λ pᵉ → Hᵉ (refl-equivalence-relationᵉ Rᵉ aᵉ ,ᵉ pᵉ)))
            qb'ᵉ)
        ( λ {a1ᵉ} {a2ᵉ} pᵉ →
          ( apᵉ (inv-precomp-set-quotientᵉ Sᵉ Xᵉ)
            ( eq-pair-Σᵉ
              ( eq-htpyᵉ (λ bᵉ → Hᵉ (pᵉ ,ᵉ refl-equivalence-relationᵉ Sᵉ bᵉ)))
              ( eq-is-propᵉ
                ( is-prop-reflects-equivalence-relationᵉ Sᵉ Xᵉ _))))))
      ( qaᵉ)
      ( qbᵉ)

  is-section-inv-precomp-set-quotient-product-set-quotientᵉ :
    { lᵉ : Level}
    ( Xᵉ : Setᵉ lᵉ) →
    ( precomp-Set-Quotientᵉ
      ( product-equivalence-relationᵉ Rᵉ Sᵉ)
      ( product-set-quotient-Setᵉ)
      ( reflecting-map-product-quotient-mapᵉ)
      ( Xᵉ) ∘ᵉ
      ( inv-precomp-set-quotient-product-set-quotientᵉ Xᵉ)) ~ᵉ
    ( idᵉ)
  is-section-inv-precomp-set-quotient-product-set-quotientᵉ Xᵉ (fᵉ ,ᵉ Hᵉ) =
    eq-pair-Σᵉ
      ( eq-htpyᵉ
        ( λ (aᵉ ,ᵉ bᵉ) →
          ( htpy-eqᵉ
            ( is-section-inv-precomp-set-quotientᵉ Rᵉ
              ( hom-set-Setᵉ (quotient-Setᵉ Sᵉ) Xᵉ) _ aᵉ)
            ( quotient-mapᵉ Sᵉ bᵉ) ∙ᵉ
          ( is-section-inv-precomp-set-quotientᵉ Sᵉ Xᵉ _ bᵉ))))
      ( eq-is-propᵉ
        ( is-prop-reflects-equivalence-relationᵉ
          ( product-equivalence-relationᵉ Rᵉ Sᵉ) Xᵉ fᵉ))

  is-retraction-inv-precomp-set-quotient-product-set-quotientᵉ :
    { lᵉ : Level}
    ( Xᵉ : Setᵉ lᵉ) →
    ( ( inv-precomp-set-quotient-product-set-quotientᵉ Xᵉ) ∘ᵉ
      ( precomp-Set-Quotientᵉ
        ( product-equivalence-relationᵉ Rᵉ Sᵉ)
        ( product-set-quotient-Setᵉ)
        ( reflecting-map-product-quotient-mapᵉ)
        ( Xᵉ))) ~ᵉ
    ( idᵉ)
  is-retraction-inv-precomp-set-quotient-product-set-quotientᵉ Xᵉ fᵉ =
    ( eq-htpyᵉ
      ( λ (qaᵉ ,ᵉ qbᵉ) →
        htpy-eqᵉ
        ( htpy-eqᵉ
          ( apᵉ
            ( inv-precomp-set-quotientᵉ
              ( Rᵉ)
              ( hom-set-Setᵉ (quotient-Setᵉ Sᵉ) Xᵉ))
              ( eq-pair-Σᵉ
                ( eq-htpyᵉ λ aᵉ →
                  ( apᵉ
                    ( inv-precomp-set-quotientᵉ Sᵉ Xᵉ)
                    ( eq-pair-eq-fiberᵉ
                      ( eq-is-propᵉ
                        ( is-prop-reflects-equivalence-relationᵉ Sᵉ Xᵉ _)))) ∙ᵉ
                    ( is-retraction-inv-precomp-set-quotientᵉ Sᵉ Xᵉ _))
                ( eq-is-propᵉ
                  ( is-prop-reflects-equivalence-relationᵉ Rᵉ
                    ( hom-set-Setᵉ (quotient-Setᵉ Sᵉ) Xᵉ) _))) ∙ᵉ
            ( is-retraction-inv-precomp-set-quotientᵉ Rᵉ
                ( hom-set-Setᵉ (quotient-Setᵉ Sᵉ) Xᵉ)
                ( λ qaᵉ qbᵉ → fᵉ (qaᵉ ,ᵉ qbᵉ))))
          ( qaᵉ))
          ( qbᵉ)))

  is-set-quotient-product-set-quotientᵉ :
    is-set-quotientᵉ
      ( product-equivalence-relationᵉ Rᵉ Sᵉ)
      ( product-set-quotient-Setᵉ)
      ( reflecting-map-product-quotient-mapᵉ)
  pr1ᵉ (pr1ᵉ (is-set-quotient-product-set-quotientᵉ Xᵉ)) =
    inv-precomp-set-quotient-product-set-quotientᵉ Xᵉ
  pr2ᵉ (pr1ᵉ (is-set-quotient-product-set-quotientᵉ Xᵉ)) =
    is-section-inv-precomp-set-quotient-product-set-quotientᵉ Xᵉ
  pr1ᵉ (pr2ᵉ (is-set-quotient-product-set-quotientᵉ Xᵉ)) =
    inv-precomp-set-quotient-product-set-quotientᵉ Xᵉ
  pr2ᵉ (pr2ᵉ (is-set-quotient-product-set-quotientᵉ Xᵉ)) =
    is-retraction-inv-precomp-set-quotient-product-set-quotientᵉ Xᵉ

  quotient-productᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  quotient-productᵉ = quotient-Setᵉ (product-equivalence-relationᵉ Rᵉ Sᵉ)

  type-quotient-productᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  type-quotient-productᵉ = pr1ᵉ quotient-productᵉ

  equiv-quotient-product-product-set-quotientᵉ :
    product-set-quotientᵉ ≃ᵉ type-Setᵉ (quotient-productᵉ)
  equiv-quotient-product-product-set-quotientᵉ =
    equiv-uniqueness-set-quotientᵉ
      ( product-equivalence-relationᵉ Rᵉ Sᵉ)
      ( product-set-quotient-Setᵉ)
      ( reflecting-map-product-quotient-mapᵉ)
      ( is-set-quotient-product-set-quotientᵉ)
      ( quotient-productᵉ)
      ( reflecting-map-quotient-mapᵉ (product-equivalence-relationᵉ Rᵉ Sᵉ))
      ( is-set-quotient-set-quotientᵉ (product-equivalence-relationᵉ Rᵉ Sᵉ))

  triangle-uniqueness-product-set-quotientᵉ :
    ( map-equivᵉ equiv-quotient-product-product-set-quotientᵉ ∘ᵉ
      product-set-quotient-mapᵉ) ~ᵉ
    quotient-mapᵉ (product-equivalence-relationᵉ Rᵉ Sᵉ)
  triangle-uniqueness-product-set-quotientᵉ =
    triangle-uniqueness-set-quotientᵉ
      ( product-equivalence-relationᵉ Rᵉ Sᵉ)
      ( product-set-quotient-Setᵉ)
      ( reflecting-map-product-quotient-mapᵉ)
      ( is-set-quotient-product-set-quotientᵉ)
      ( quotient-productᵉ)
      ( reflecting-map-quotient-mapᵉ (product-equivalence-relationᵉ Rᵉ Sᵉ))
      ( is-set-quotient-set-quotientᵉ (product-equivalence-relationᵉ Rᵉ Sᵉ))
```