# The universal property of fiber products

```agda
module foundation.universal-property-fiber-productsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.pullbacksᵉ
open import foundation-core.universal-property-pullbacksᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "fiberwiseᵉ product"ᵉ Disambiguation="types"ᵉ}} ofᵉ twoᵉ familiesᵉ `P`ᵉ
andᵉ `Q`ᵉ overᵉ aᵉ typeᵉ `X`ᵉ isᵉ theᵉ familyᵉ ofᵉ typesᵉ `(Pᵉ xᵉ) ×ᵉ (Qᵉ x)`ᵉ overᵉ `X`.ᵉ
Similarly,ᵉ theᵉ fiberᵉ productᵉ ofᵉ twoᵉ mapsᵉ `fᵉ : Aᵉ → X`ᵉ andᵉ `gᵉ : Bᵉ → X`ᵉ isᵉ theᵉ typeᵉ
`Σᵉ Xᵉ (λ xᵉ → fiberᵉ fᵉ xᵉ ×ᵉ fiberᵉ gᵉ x)`,ᵉ whichᵉ fitsᵉ in aᵉ
[pullback](foundation-core.pullbacks.mdᵉ) diagramᵉ onᵉ `f`ᵉ andᵉ `g`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : Xᵉ → UUᵉ l2ᵉ) (Qᵉ : Xᵉ → UUᵉ l3ᵉ)
  where

  cone-fiberwise-productᵉ :
    coneᵉ (pr1ᵉ {Bᵉ = Pᵉ}) (pr1ᵉ {Bᵉ = Qᵉ}) (Σᵉ Xᵉ (λ xᵉ → (Pᵉ xᵉ) ×ᵉ (Qᵉ xᵉ)))
  pr1ᵉ cone-fiberwise-productᵉ = totᵉ (λ _ → pr1ᵉ)
  pr1ᵉ (pr2ᵉ cone-fiberwise-productᵉ) = totᵉ (λ _ → pr2ᵉ)
  pr2ᵉ (pr2ᵉ cone-fiberwise-productᵉ) = refl-htpyᵉ
```

Weᵉ willᵉ showᵉ thatᵉ theᵉ fiberwiseᵉ productᵉ isᵉ aᵉ pullbackᵉ byᵉ showingᵉ thatᵉ theᵉ gapᵉ
mapᵉ isᵉ anᵉ equivalence.ᵉ Weᵉ do thisᵉ byᵉ directlyᵉ constructᵉ anᵉ inverseᵉ to theᵉ gapᵉ
map.ᵉ

```agda
  gap-fiberwise-productᵉ :
    Σᵉ Xᵉ (λ xᵉ → (Pᵉ xᵉ) ×ᵉ (Qᵉ xᵉ)) → standard-pullbackᵉ (pr1ᵉ {Bᵉ = Pᵉ}) (pr1ᵉ {Bᵉ = Qᵉ})
  gap-fiberwise-productᵉ = gapᵉ pr1ᵉ pr1ᵉ cone-fiberwise-productᵉ

  inv-gap-fiberwise-productᵉ :
    standard-pullbackᵉ (pr1ᵉ {Bᵉ = Pᵉ}) (pr1ᵉ {Bᵉ = Qᵉ}) → Σᵉ Xᵉ (λ xᵉ → (Pᵉ xᵉ) ×ᵉ (Qᵉ xᵉ))
  pr1ᵉ (inv-gap-fiberwise-productᵉ ((xᵉ ,ᵉ pᵉ) ,ᵉ (.xᵉ ,ᵉ qᵉ) ,ᵉ reflᵉ)) = xᵉ
  pr1ᵉ (pr2ᵉ (inv-gap-fiberwise-productᵉ ((xᵉ ,ᵉ pᵉ) ,ᵉ (.xᵉ ,ᵉ qᵉ) ,ᵉ reflᵉ))) = pᵉ
  pr2ᵉ (pr2ᵉ (inv-gap-fiberwise-productᵉ ((xᵉ ,ᵉ pᵉ) ,ᵉ (.xᵉ ,ᵉ qᵉ) ,ᵉ reflᵉ))) = qᵉ

  abstract
    is-section-inv-gap-fiberwise-productᵉ :
      (gap-fiberwise-productᵉ ∘ᵉ inv-gap-fiberwise-productᵉ) ~ᵉ idᵉ
    is-section-inv-gap-fiberwise-productᵉ ((xᵉ ,ᵉ pᵉ) ,ᵉ (.xᵉ ,ᵉ qᵉ) ,ᵉ reflᵉ) = reflᵉ

  abstract
    is-retraction-inv-gap-fiberwise-productᵉ :
      (inv-gap-fiberwise-productᵉ ∘ᵉ gap-fiberwise-productᵉ) ~ᵉ idᵉ
    is-retraction-inv-gap-fiberwise-productᵉ (xᵉ ,ᵉ pᵉ ,ᵉ qᵉ) = reflᵉ

  abstract
    is-pullback-fiberwise-productᵉ :
      is-pullbackᵉ (pr1ᵉ {Bᵉ = Pᵉ}) (pr1ᵉ {Bᵉ = Qᵉ}) cone-fiberwise-productᵉ
    is-pullback-fiberwise-productᵉ =
      is-equiv-is-invertibleᵉ
        inv-gap-fiberwise-productᵉ
        is-section-inv-gap-fiberwise-productᵉ
        is-retraction-inv-gap-fiberwise-productᵉ

  abstract
    universal-property-pullback-fiberwise-productᵉ :
      universal-property-pullbackᵉ
        ( pr1ᵉ {Bᵉ = Pᵉ})
        ( pr1ᵉ {Bᵉ = Qᵉ})
        ( cone-fiberwise-productᵉ)
    universal-property-pullback-fiberwise-productᵉ =
      universal-property-pullback-is-pullbackᵉ pr1ᵉ pr1ᵉ
        cone-fiberwise-productᵉ
        is-pullback-fiberwise-productᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  cone-total-product-fibersᵉ : coneᵉ fᵉ gᵉ (Σᵉ Xᵉ (λ xᵉ → (fiberᵉ fᵉ xᵉ) ×ᵉ (fiberᵉ gᵉ xᵉ)))
  pr1ᵉ cone-total-product-fibersᵉ (xᵉ ,ᵉ (aᵉ ,ᵉ pᵉ) ,ᵉ (bᵉ ,ᵉ qᵉ)) = aᵉ
  pr1ᵉ (pr2ᵉ cone-total-product-fibersᵉ) (xᵉ ,ᵉ (aᵉ ,ᵉ pᵉ) ,ᵉ (bᵉ ,ᵉ qᵉ)) = bᵉ
  pr2ᵉ (pr2ᵉ cone-total-product-fibersᵉ) (xᵉ ,ᵉ (aᵉ ,ᵉ pᵉ) ,ᵉ (bᵉ ,ᵉ qᵉ)) = pᵉ ∙ᵉ invᵉ qᵉ

  gap-total-product-fibersᵉ :
    Σᵉ Xᵉ (λ xᵉ → (fiberᵉ fᵉ xᵉ) ×ᵉ (fiberᵉ gᵉ xᵉ)) → standard-pullbackᵉ fᵉ gᵉ
  gap-total-product-fibersᵉ = gapᵉ fᵉ gᵉ cone-total-product-fibersᵉ

  inv-gap-total-product-fibersᵉ :
    standard-pullbackᵉ fᵉ gᵉ → Σᵉ Xᵉ (λ xᵉ → (fiberᵉ fᵉ xᵉ) ×ᵉ (fiberᵉ gᵉ xᵉ))
  pr1ᵉ (inv-gap-total-product-fibersᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ)) = gᵉ bᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (inv-gap-total-product-fibersᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ)))) = aᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ (inv-gap-total-product-fibersᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ)))) = pᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (inv-gap-total-product-fibersᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ)))) = bᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (inv-gap-total-product-fibersᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ)))) = reflᵉ

  abstract
    is-section-inv-gap-total-product-fibersᵉ :
      (gap-total-product-fibersᵉ ∘ᵉ inv-gap-total-product-fibersᵉ) ~ᵉ idᵉ
    is-section-inv-gap-total-product-fibersᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ) =
      map-extensionality-standard-pullbackᵉ fᵉ gᵉ reflᵉ reflᵉ
        ( invᵉ right-unitᵉ ∙ᵉ invᵉ right-unitᵉ)

  abstract
    is-retraction-inv-gap-total-product-fibersᵉ :
      (inv-gap-total-product-fibersᵉ ∘ᵉ gap-total-product-fibersᵉ) ~ᵉ idᵉ
    is-retraction-inv-gap-total-product-fibersᵉ (.(gᵉ bᵉ) ,ᵉ (aᵉ ,ᵉ pᵉ) ,ᵉ (bᵉ ,ᵉ reflᵉ)) =
      eq-pair-eq-fiberᵉ (eq-pairᵉ (eq-pair-eq-fiberᵉ right-unitᵉ) reflᵉ)

  abstract
    is-pullback-total-product-fibersᵉ :
      is-pullbackᵉ fᵉ gᵉ cone-total-product-fibersᵉ
    is-pullback-total-product-fibersᵉ =
      is-equiv-is-invertibleᵉ
        inv-gap-total-product-fibersᵉ
        is-section-inv-gap-total-product-fibersᵉ
        is-retraction-inv-gap-total-product-fibersᵉ
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}