# Dependent pushout-products

```agda
module synthetic-homotopy-theory.dependent-pushout-productsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Theᵉ **dependentᵉ pushout-product**ᵉ isᵉ aᵉ generalizationᵉ ofᵉ theᵉ
[pushout-product](synthetic-homotopy-theory.pushout-products.md).ᵉ Considerᵉ aᵉ mapᵉ
`fᵉ : Aᵉ → B`ᵉ andᵉ aᵉ familyᵉ ofᵉ mapsᵉ `gᵉ : (xᵉ : Xᵉ) → Bᵉ xᵉ → Yᵉ x`.ᵉ Theᵉ **dependentᵉ
pushout-product**ᵉ isᵉ theᵉ [cogapᵉ map](synthetic-homotopy-theory.pushouts.mdᵉ) ofᵉ
theᵉ [commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
                       Σᵉ fᵉ idᵉ
          Σᵉ Aᵉ (Bᵉ ∘ᵉ fᵉ) -------->ᵉ Σᵉ Xᵉ Bᵉ
               |                  |
  Σᵉ idᵉ (gᵉ ∘ᵉ fᵉ) |                  | Σᵉ idᵉ gᵉ
               ∨ᵉ                  ∨ᵉ
          Σᵉ Aᵉ (Yᵉ ∘ᵉ fᵉ) -------->ᵉ Σᵉ Xᵉ Y.ᵉ
                       Σᵉ fᵉ idᵉ
```

Theᵉ [fiber](foundation-core.fibers-of-maps.mdᵉ) ofᵉ theᵉ dependentᵉ pushoutᵉ productᵉ
atᵉ `(xᵉ ,ᵉ y)`ᵉ isᵉ [equivalent](foundation-core.equivalences.mdᵉ) to theᵉ joinᵉ ofᵉ
fibersᵉ

```text
  fiberᵉ fᵉ xᵉ *ᵉ fiberᵉ (gᵉ xᵉ) yᵉ
```

Aᵉ specialᵉ caseᵉ isᵉ ofᵉ interest,ᵉ where `Y`ᵉ isᵉ theᵉ familyᵉ ofᵉ contractibleᵉ types,ᵉ
andᵉ `B`ᵉ isᵉ aᵉ familyᵉ ofᵉ propositions.ᵉ

## Definitions

### Dependent pushout-products

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Bᵉ : Xᵉ → UUᵉ l3ᵉ} {Yᵉ : Xᵉ → UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : (xᵉ : Xᵉ) → Bᵉ xᵉ → Yᵉ xᵉ)
  where

  domain-dependent-pushout-productᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  domain-dependent-pushout-productᵉ =
    pushoutᵉ
      ( map-Σᵉ (Yᵉ ∘ᵉ fᵉ) idᵉ (gᵉ ∘ᵉ fᵉ))
      ( map-Σᵉ Bᵉ fᵉ (λ aᵉ → idᵉ))

  cocone-dependent-pushout-productᵉ :
    coconeᵉ
      ( map-Σᵉ (Yᵉ ∘ᵉ fᵉ) idᵉ (gᵉ ∘ᵉ fᵉ))
      ( map-Σᵉ Bᵉ fᵉ (λ aᵉ → idᵉ))
      ( Σᵉ Xᵉ Yᵉ)
  pr1ᵉ cocone-dependent-pushout-productᵉ = map-Σᵉ Yᵉ fᵉ (λ aᵉ → idᵉ)
  pr1ᵉ (pr2ᵉ cocone-dependent-pushout-productᵉ) = map-Σᵉ Yᵉ idᵉ gᵉ
  pr2ᵉ (pr2ᵉ cocone-dependent-pushout-productᵉ) = refl-htpyᵉ

  abstract
    uniqueness-dependent-pushout-productᵉ :
      is-contrᵉ
        ( Σᵉ ( domain-dependent-pushout-productᵉ → Σᵉ Xᵉ Yᵉ)
            ( λ hᵉ →
              htpy-coconeᵉ
                ( map-Σᵉ (Yᵉ ∘ᵉ fᵉ) idᵉ (gᵉ ∘ᵉ fᵉ))
                ( map-Σᵉ Bᵉ fᵉ (λ aᵉ → idᵉ))
                ( cocone-mapᵉ
                  ( map-Σᵉ (Yᵉ ∘ᵉ fᵉ) idᵉ (gᵉ ∘ᵉ fᵉ))
                  ( map-Σᵉ Bᵉ fᵉ (λ aᵉ → idᵉ))
                  ( cocone-pushoutᵉ
                    ( map-Σᵉ (Yᵉ ∘ᵉ fᵉ) idᵉ (gᵉ ∘ᵉ fᵉ))
                    ( map-Σᵉ Bᵉ fᵉ (λ aᵉ → idᵉ)))
                  ( hᵉ))
                ( cocone-dependent-pushout-productᵉ)))
    uniqueness-dependent-pushout-productᵉ =
      uniqueness-map-universal-property-pushoutᵉ
        ( map-Σᵉ (Yᵉ ∘ᵉ fᵉ) idᵉ (gᵉ ∘ᵉ fᵉ))
        ( map-Σᵉ Bᵉ fᵉ (λ aᵉ → idᵉ))
        ( cocone-pushoutᵉ (map-Σᵉ (Yᵉ ∘ᵉ fᵉ) idᵉ (gᵉ ∘ᵉ fᵉ)) (map-Σᵉ Bᵉ fᵉ (λ aᵉ → idᵉ)))
        ( up-pushoutᵉ (map-Σᵉ (Yᵉ ∘ᵉ fᵉ) idᵉ (gᵉ ∘ᵉ fᵉ)) (map-Σᵉ Bᵉ fᵉ (λ aᵉ → idᵉ)))
        ( cocone-dependent-pushout-productᵉ)

  abstract
    dependent-pushout-productᵉ : domain-dependent-pushout-productᵉ → Σᵉ Xᵉ Yᵉ
    dependent-pushout-productᵉ =
      pr1ᵉ (centerᵉ uniqueness-dependent-pushout-productᵉ)

    compute-inl-dependent-pushout-productᵉ :
      ( dependent-pushout-productᵉ ∘ᵉ
        inl-pushoutᵉ (map-Σᵉ (Yᵉ ∘ᵉ fᵉ) idᵉ (gᵉ ∘ᵉ fᵉ)) (map-Σᵉ Bᵉ fᵉ (λ aᵉ → idᵉ))) ~ᵉ
      ( map-Σᵉ Yᵉ fᵉ (λ aᵉ → idᵉ))
    compute-inl-dependent-pushout-productᵉ =
      pr1ᵉ (pr2ᵉ (centerᵉ uniqueness-dependent-pushout-productᵉ))

    compute-inr-dependent-pushout-productᵉ :
      ( dependent-pushout-productᵉ ∘ᵉ
        inr-pushoutᵉ (map-Σᵉ (Yᵉ ∘ᵉ fᵉ) idᵉ (gᵉ ∘ᵉ fᵉ)) (map-Σᵉ Bᵉ fᵉ (λ aᵉ → idᵉ))) ~ᵉ
      map-Σᵉ Yᵉ idᵉ gᵉ
    compute-inr-dependent-pushout-productᵉ =
      pr1ᵉ (pr2ᵉ (pr2ᵉ (centerᵉ uniqueness-dependent-pushout-productᵉ)))

    compute-glue-dependent-pushout-productᵉ :
      statement-coherence-htpy-coconeᵉ
        ( map-Σᵉ (Yᵉ ∘ᵉ fᵉ) idᵉ (gᵉ ∘ᵉ fᵉ))
        ( map-Σᵉ Bᵉ fᵉ (λ aᵉ → idᵉ))
        ( cocone-mapᵉ
          ( map-Σᵉ (Yᵉ ∘ᵉ fᵉ) idᵉ (gᵉ ∘ᵉ fᵉ))
          ( map-Σᵉ Bᵉ fᵉ (λ aᵉ → idᵉ))
          ( cocone-pushoutᵉ (map-Σᵉ (Yᵉ ∘ᵉ fᵉ) idᵉ (gᵉ ∘ᵉ fᵉ)) (map-Σᵉ Bᵉ fᵉ (λ aᵉ → idᵉ)))
          ( dependent-pushout-productᵉ))
        ( cocone-dependent-pushout-productᵉ)
        ( compute-inl-dependent-pushout-productᵉ)
        ( compute-inr-dependent-pushout-productᵉ)
    compute-glue-dependent-pushout-productᵉ =
      pr2ᵉ (pr2ᵉ (pr2ᵉ (centerᵉ uniqueness-dependent-pushout-productᵉ)))
```