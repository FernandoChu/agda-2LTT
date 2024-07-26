# Path-split maps

```agda
module foundation-core.path-split-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coherently-invertible-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ saidᵉ to beᵉ **pathᵉ split**ᵉ ifᵉ itᵉ hasᵉ aᵉ
[section](foundation-core.sections.mdᵉ) andᵉ itsᵉ
[actionᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
`xᵉ ＝ᵉ yᵉ → fᵉ xᵉ ＝ᵉ fᵉ y`ᵉ hasᵉ aᵉ sectionᵉ forᵉ eachᵉ `xᵉ yᵉ : A`.ᵉ Byᵉ theᵉ
[fundamentalᵉ theoremᵉ ofᵉ identityᵉ types](foundation.fundamental-theorem-of-identity-types.md),ᵉ
itᵉ followsᵉ thatᵉ aᵉ mapᵉ isᵉ path-splitᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ anᵉ
[equivalence](foundation-core.equivalences.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-path-splitᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-path-splitᵉ = sectionᵉ fᵉ ×ᵉ ((xᵉ yᵉ : Aᵉ) → sectionᵉ (apᵉ fᵉ {xᵉ = xᵉ} {yᵉ = yᵉ}))
```

## Properties

### A map is path-split if and only if it is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-path-split-is-equivᵉ : is-equivᵉ fᵉ → is-path-splitᵉ fᵉ
    pr1ᵉ (is-path-split-is-equivᵉ is-equiv-fᵉ) = pr1ᵉ is-equiv-fᵉ
    pr2ᵉ (is-path-split-is-equivᵉ is-equiv-fᵉ) xᵉ yᵉ =
      pr1ᵉ (is-emb-is-equivᵉ is-equiv-fᵉ xᵉ yᵉ)

  abstract
    is-coherently-invertible-is-path-splitᵉ :
      is-path-splitᵉ fᵉ → is-coherently-invertibleᵉ fᵉ
    pr1ᵉ (is-coherently-invertible-is-path-splitᵉ ((gᵉ ,ᵉ Gᵉ) ,ᵉ sᵉ)) =
      gᵉ
    pr1ᵉ (pr2ᵉ (is-coherently-invertible-is-path-splitᵉ ((gᵉ ,ᵉ Gᵉ) ,ᵉ sᵉ))) =
      Gᵉ
    pr1ᵉ (pr2ᵉ (pr2ᵉ (is-coherently-invertible-is-path-splitᵉ ((gᵉ ,ᵉ Gᵉ) ,ᵉ sᵉ)))) xᵉ =
      pr1ᵉ (sᵉ (gᵉ (fᵉ xᵉ)) xᵉ) (Gᵉ (fᵉ xᵉ))
    pr2ᵉ (pr2ᵉ (pr2ᵉ (is-coherently-invertible-is-path-splitᵉ ((gᵉ ,ᵉ Gᵉ) ,ᵉ sᵉ)))) xᵉ =
      invᵉ (pr2ᵉ (sᵉ (gᵉ (fᵉ xᵉ)) xᵉ) (Gᵉ (fᵉ xᵉ)))

  abstract
    is-equiv-is-path-splitᵉ : is-path-splitᵉ fᵉ → is-equivᵉ fᵉ
    is-equiv-is-path-splitᵉ =
      is-equiv-is-coherently-invertibleᵉ ∘ᵉ
      is-coherently-invertible-is-path-splitᵉ
```

## See also

-ᵉ Forᵉ theᵉ notionᵉ ofᵉ biinvertibleᵉ mapsᵉ seeᵉ
  [`foundation.equivalences`](foundation.equivalences.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ coherentlyᵉ invertibleᵉ maps,ᵉ alsoᵉ knownᵉ asᵉ half-adjointᵉ
  equivalences,ᵉ seeᵉ
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ mapsᵉ with contractibleᵉ fibersᵉ seeᵉ
  [`foundation.contractible-maps`](foundation.contractible-maps.md).ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ UF13ᵉ}} {{#referenceᵉ Shu14UniversalPropertiesᵉ}}