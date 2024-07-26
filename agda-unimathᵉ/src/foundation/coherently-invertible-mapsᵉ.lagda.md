# Coherently invertible maps

```agda
module foundation.coherently-invertible-mapsᵉ where

open import foundation-core.coherently-invertible-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Properties

### Coherently invertible maps have a contractible type of sections

**Proof:**ᵉ Sinceᵉ coherentlyᵉ invertibleᵉ mapsᵉ areᵉ
[contractibleᵉ maps](foundation.contractible-maps.md),ᵉ andᵉ productsᵉ ofᵉ
[contractibleᵉ types](foundation-core.contractible-types.mdᵉ) areᵉ contractible,ᵉ itᵉ
followsᵉ thatᵉ theᵉ typeᵉ

```text
  (bᵉ : Bᵉ) → fiberᵉ fᵉ bᵉ
```

isᵉ contractible,ᵉ forᵉ anyᵉ coherentlyᵉ invertibleᵉ mapᵉ `f`.ᵉ However,ᵉ byᵉ theᵉ
[typeᵉ theoreticᵉ principleᵉ ofᵉ choice](foundation.type-theoretic-principle-of-choice.mdᵉ)
itᵉ followsᵉ thatᵉ thisᵉ typeᵉ isᵉ equivalentᵉ to theᵉ typeᵉ

```text
  Σᵉ (Bᵉ → Aᵉ) (λ gᵉ → (bᵉ : Bᵉ) → fᵉ (gᵉ bᵉ) ＝ᵉ b),ᵉ
```

whichᵉ isᵉ theᵉ typeᵉ ofᵉ [sections](foundation.sections.mdᵉ) ofᵉ `f`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-contr-section-is-coherently-invertibleᵉ :
      {fᵉ : Aᵉ → Bᵉ} → is-coherently-invertibleᵉ fᵉ → is-contrᵉ (sectionᵉ fᵉ)
    is-contr-section-is-coherently-invertibleᵉ {fᵉ} Fᵉ =
      is-contr-equiv'ᵉ
        ( (bᵉ : Bᵉ) → fiberᵉ fᵉ bᵉ)
        ( distributive-Π-Σᵉ)
        ( is-contr-Πᵉ (is-contr-map-is-coherently-invertibleᵉ Fᵉ))
```

### Being coherently invertible is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-proof-irrelevant-is-coherently-invertibleᵉ :
      is-proof-irrelevantᵉ (is-coherently-invertibleᵉ fᵉ)
    is-proof-irrelevant-is-coherently-invertibleᵉ Hᵉ =
      is-contr-equiv'ᵉ
        ( _)
        ( associative-Σᵉ _ _ _)
        ( is-contr-Σᵉ
          ( is-contr-section-is-coherently-invertibleᵉ Hᵉ)
          ( section-is-coherently-invertibleᵉ Hᵉ)
          ( is-contr-equiv'ᵉ
            ( _)
            ( distributive-Π-Σᵉ)
            ( is-contr-Πᵉ
              ( λ xᵉ →
                is-contr-equiv'ᵉ
                  ( _)
                  ( equiv-totᵉ
                    ( λ pᵉ →
                      equiv-invᵉ
                        ( apᵉ fᵉ pᵉ)
                        ( is-section-map-inv-is-coherently-invertibleᵉ Hᵉ (fᵉ xᵉ))))
                  ( is-contr-map-is-coherently-invertibleᵉ
                    ( is-coherently-invertible-ap-is-coherently-invertibleᵉ Hᵉ)
                    ( is-section-map-inv-is-coherently-invertibleᵉ Hᵉ (fᵉ xᵉ)))))))

  abstract
    is-prop-is-coherently-invertibleᵉ : is-propᵉ (is-coherently-invertibleᵉ fᵉ)
    is-prop-is-coherently-invertibleᵉ =
      is-prop-is-proof-irrelevantᵉ is-proof-irrelevant-is-coherently-invertibleᵉ

  abstract
    is-equiv-is-coherently-invertible-is-equivᵉ :
      is-equivᵉ (is-coherently-invertible-is-equivᵉ {fᵉ = fᵉ})
    is-equiv-is-coherently-invertible-is-equivᵉ =
      is-equiv-has-converse-is-propᵉ
        ( is-property-is-equivᵉ fᵉ)
        ( is-prop-is-coherently-invertibleᵉ)
        ( is-equiv-is-coherently-invertibleᵉ)
```

### Being transpose coherently invertible is a property

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ UF13ᵉ}}

## See also

-ᵉ Forᵉ theᵉ notionᵉ ofᵉ biinvertibleᵉ mapsᵉ seeᵉ
  [`foundation.equivalences`](foundation.equivalences.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ mapsᵉ with contractibleᵉ fibersᵉ seeᵉ
  [`foundation.contractible-maps`](foundation.contractible-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ path-splitᵉ mapsᵉ seeᵉ
  [`foundation.path-split-maps`](foundation.path-split-maps.md).ᵉ