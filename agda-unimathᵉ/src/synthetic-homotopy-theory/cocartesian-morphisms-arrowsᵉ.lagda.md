# Cocartesian morphisms of arrows

```agda
module synthetic-homotopy-theory.cocartesian-morphisms-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Aᵉ [morphismᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) `hᵉ : fᵉ → g`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "cocartesian"ᵉ Disambiguation="morphismᵉ ofᵉ arrows"ᵉ Agda=is-cocartesian-hom-arrowᵉ}}
ifᵉ theᵉ [commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
        iᵉ
    Aᵉ ----->ᵉ Xᵉ
    |        |
  fᵉ |   hᵉ    | gᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
        jᵉ
```

isᵉ aᵉ [pushout](synthetic-homotopy-theory.pushouts.mdᵉ) square.ᵉ Inᵉ thisᵉ instance,ᵉ
weᵉ alsoᵉ sayᵉ thatᵉ `g`ᵉ isᵉ aᵉ
{{#conceptᵉ "cobaseᵉ change"ᵉ Disambiguation="mapsᵉ ofᵉ types"ᵉ}} ofᵉ `f`.ᵉ

## Definitions

### The predicate of being a cocartesian morphism of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  is-cocartesian-hom-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-cocartesian-hom-arrowᵉ =
    is-pushoutᵉ fᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ hᵉ) (cocone-hom-arrowᵉ fᵉ gᵉ hᵉ)

  is-prop-is-cocartesian-hom-arrowᵉ : is-propᵉ is-cocartesian-hom-arrowᵉ
  is-prop-is-cocartesian-hom-arrowᵉ =
    is-prop-is-pushoutᵉ fᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ hᵉ) (cocone-hom-arrowᵉ fᵉ gᵉ hᵉ)

  is-cocartesian-hom-arrow-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-cocartesian-hom-arrow-Propᵉ = is-cocartesian-hom-arrowᵉ
  pr2ᵉ is-cocartesian-hom-arrow-Propᵉ = is-prop-is-cocartesian-hom-arrowᵉ
```

### The type of cocartesian morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  cocartesian-hom-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  cocartesian-hom-arrowᵉ = Σᵉ (hom-arrowᵉ fᵉ gᵉ) (is-cocartesian-hom-arrowᵉ fᵉ gᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : cocartesian-hom-arrowᵉ fᵉ gᵉ)
  where

  hom-arrow-cocartesian-hom-arrowᵉ : hom-arrowᵉ fᵉ gᵉ
  hom-arrow-cocartesian-hom-arrowᵉ = pr1ᵉ hᵉ

  is-cocartesian-cocartesian-hom-arrowᵉ :
    is-cocartesian-hom-arrowᵉ fᵉ gᵉ hom-arrow-cocartesian-hom-arrowᵉ
  is-cocartesian-cocartesian-hom-arrowᵉ = pr2ᵉ hᵉ

  map-domain-cocartesian-hom-arrowᵉ : Aᵉ → Xᵉ
  map-domain-cocartesian-hom-arrowᵉ =
    map-domain-hom-arrowᵉ fᵉ gᵉ hom-arrow-cocartesian-hom-arrowᵉ

  map-codomain-cocartesian-hom-arrowᵉ : Bᵉ → Yᵉ
  map-codomain-cocartesian-hom-arrowᵉ =
    map-codomain-hom-arrowᵉ fᵉ gᵉ hom-arrow-cocartesian-hom-arrowᵉ

  coh-cocartesian-hom-arrowᵉ :
    coherence-square-mapsᵉ
      ( map-domain-cocartesian-hom-arrowᵉ)
      ( fᵉ)
      ( gᵉ)
      ( map-codomain-cocartesian-hom-arrowᵉ)
  coh-cocartesian-hom-arrowᵉ =
    coh-hom-arrowᵉ fᵉ gᵉ hom-arrow-cocartesian-hom-arrowᵉ

  cocone-cocartesian-hom-arrowᵉ :
    coconeᵉ fᵉ map-domain-cocartesian-hom-arrowᵉ Yᵉ
  cocone-cocartesian-hom-arrowᵉ =
    cocone-hom-arrowᵉ fᵉ gᵉ hom-arrow-cocartesian-hom-arrowᵉ

  universal-property-cocartesian-hom-arrowᵉ :
    universal-property-pushoutᵉ
      ( fᵉ)
      ( map-domain-cocartesian-hom-arrowᵉ)
      ( cocone-cocartesian-hom-arrowᵉ)
  universal-property-cocartesian-hom-arrowᵉ =
    universal-property-pushout-is-pushoutᵉ
      ( fᵉ)
      ( map-domain-cocartesian-hom-arrowᵉ)
      ( cocone-cocartesian-hom-arrowᵉ)
      ( is-cocartesian-cocartesian-hom-arrowᵉ)
```

## See also

-ᵉ [Cartesianᵉ morphismsᵉ ofᵉ arrows](foundation.cartesian-morphisms-arrows.mdᵉ) forᵉ
  theᵉ dual.ᵉ