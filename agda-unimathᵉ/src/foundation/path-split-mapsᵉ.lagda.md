# Path-split maps

```agda
module foundation.path-split-mapsᵉ where

open import foundation-core.path-split-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Properties

### Being path-split is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-prop-is-path-splitᵉ : (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (is-path-splitᵉ fᵉ)
    is-prop-is-path-splitᵉ fᵉ =
      is-prop-is-proof-irrelevantᵉ
        ( λ is-path-split-fᵉ →
          ( is-contr-productᵉ
            ( is-contr-section-is-equivᵉ
              ( is-equiv-is-path-splitᵉ fᵉ is-path-split-fᵉ))
            ( is-contr-iterated-Πᵉ 2
              ( λ xᵉ yᵉ →
                is-contr-section-is-equivᵉ
                  ( is-emb-is-equivᵉ
                    ( is-equiv-is-path-splitᵉ fᵉ is-path-split-fᵉ) xᵉ yᵉ)))))

  abstract
    is-equiv-is-path-split-is-equivᵉ :
      (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ (is-path-split-is-equivᵉ fᵉ)
    is-equiv-is-path-split-is-equivᵉ fᵉ =
      is-equiv-has-converse-is-propᵉ
        ( is-property-is-equivᵉ fᵉ)
        ( is-prop-is-path-splitᵉ fᵉ)
        ( is-equiv-is-path-splitᵉ fᵉ)

  equiv-is-path-split-is-equivᵉ : (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ fᵉ ≃ᵉ is-path-splitᵉ fᵉ
  equiv-is-path-split-is-equivᵉ fᵉ =
    pairᵉ (is-path-split-is-equivᵉ fᵉ) (is-equiv-is-path-split-is-equivᵉ fᵉ)

  abstract
    is-equiv-is-equiv-is-path-splitᵉ :
      (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ (is-equiv-is-path-splitᵉ fᵉ)
    is-equiv-is-equiv-is-path-splitᵉ fᵉ =
      is-equiv-has-converse-is-propᵉ
        ( is-prop-is-path-splitᵉ fᵉ)
        ( is-property-is-equivᵉ fᵉ)
        ( is-path-split-is-equivᵉ fᵉ)

  equiv-is-equiv-is-path-splitᵉ : (fᵉ : Aᵉ → Bᵉ) → is-path-splitᵉ fᵉ ≃ᵉ is-equivᵉ fᵉ
  equiv-is-equiv-is-path-splitᵉ fᵉ =
    ( is-equiv-is-path-splitᵉ fᵉ ,ᵉ is-equiv-is-equiv-is-path-splitᵉ fᵉ)
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