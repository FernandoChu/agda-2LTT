# Cartesian morphisms of arrows

```agda
module foundation.cartesian-morphisms-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.commuting-triangles-of-morphisms-arrowsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.coproducts-pullbacksᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-products-pullbacksᵉ
open import foundation.dependent-sums-pullbacksᵉ
open import foundation.diagonal-maps-cartesian-products-of-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopies-morphisms-arrowsᵉ
open import foundation.identity-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.postcomposition-pullbacksᵉ
open import foundation.products-pullbacksᵉ
open import foundation.pullbacksᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.universal-property-pullbacksᵉ
```

</details>

## Idea

Aᵉ [morphismᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) `hᵉ : fᵉ → g`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "cartesian"ᵉ Disambiguation="morphismᵉ ofᵉ arrows"ᵉ Agda=is-cartesian-hom-arrowᵉ}}
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

isᵉ aᵉ [pullback](foundation.pullbacks.mdᵉ) square.ᵉ Inᵉ thisᵉ instance,ᵉ weᵉ alsoᵉ sayᵉ
thatᵉ `f`ᵉ isᵉ aᵉ {{#conceptᵉ "baseᵉ change"ᵉ Disambiguation="mapsᵉ ofᵉ types"ᵉ}} ofᵉ `g`.ᵉ

## Definitions

### The predicate of being a cartesian morphism of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  is-cartesian-hom-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-cartesian-hom-arrowᵉ =
    is-pullbackᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ hᵉ) gᵉ (cone-hom-arrowᵉ fᵉ gᵉ hᵉ)

  is-prop-is-cartesian-hom-arrowᵉ : is-propᵉ is-cartesian-hom-arrowᵉ
  is-prop-is-cartesian-hom-arrowᵉ =
    is-prop-is-pullbackᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ hᵉ) gᵉ (cone-hom-arrowᵉ fᵉ gᵉ hᵉ)

  is-cartesian-hom-arrow-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-cartesian-hom-arrow-Propᵉ = is-cartesian-hom-arrowᵉ
  pr2ᵉ is-cartesian-hom-arrow-Propᵉ = is-prop-is-cartesian-hom-arrowᵉ
```

### The type of cartesian morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  cartesian-hom-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  cartesian-hom-arrowᵉ = Σᵉ (hom-arrowᵉ fᵉ gᵉ) (is-cartesian-hom-arrowᵉ fᵉ gᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : cartesian-hom-arrowᵉ fᵉ gᵉ)
  where

  hom-arrow-cartesian-hom-arrowᵉ : hom-arrowᵉ fᵉ gᵉ
  hom-arrow-cartesian-hom-arrowᵉ = pr1ᵉ hᵉ

  is-cartesian-cartesian-hom-arrowᵉ :
    is-cartesian-hom-arrowᵉ fᵉ gᵉ hom-arrow-cartesian-hom-arrowᵉ
  is-cartesian-cartesian-hom-arrowᵉ = pr2ᵉ hᵉ

  map-domain-cartesian-hom-arrowᵉ : Aᵉ → Xᵉ
  map-domain-cartesian-hom-arrowᵉ =
    map-domain-hom-arrowᵉ fᵉ gᵉ hom-arrow-cartesian-hom-arrowᵉ

  map-codomain-cartesian-hom-arrowᵉ : Bᵉ → Yᵉ
  map-codomain-cartesian-hom-arrowᵉ =
    map-codomain-hom-arrowᵉ fᵉ gᵉ hom-arrow-cartesian-hom-arrowᵉ

  coh-cartesian-hom-arrowᵉ :
    coherence-square-mapsᵉ
      ( map-domain-cartesian-hom-arrowᵉ)
      ( fᵉ)
      ( gᵉ)
      ( map-codomain-cartesian-hom-arrowᵉ)
  coh-cartesian-hom-arrowᵉ =
    coh-hom-arrowᵉ fᵉ gᵉ hom-arrow-cartesian-hom-arrowᵉ

  cone-cartesian-hom-arrowᵉ :
    coneᵉ map-codomain-cartesian-hom-arrowᵉ gᵉ Aᵉ
  cone-cartesian-hom-arrowᵉ =
    cone-hom-arrowᵉ fᵉ gᵉ hom-arrow-cartesian-hom-arrowᵉ

  universal-property-cartesian-hom-arrowᵉ :
    universal-property-pullbackᵉ
      ( map-codomain-cartesian-hom-arrowᵉ)
      ( gᵉ)
      ( cone-cartesian-hom-arrowᵉ)
  universal-property-cartesian-hom-arrowᵉ =
    universal-property-pullback-is-pullbackᵉ
      ( map-codomain-cartesian-hom-arrowᵉ)
      ( gᵉ)
      ( cone-cartesian-hom-arrowᵉ)
      ( is-cartesian-cartesian-hom-arrowᵉ)
```

## Properties

### Cartesian morphisms of arrows arising from standard pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  standard-pullback-cartesian-hom-arrowᵉ :
    cartesian-hom-arrowᵉ vertical-map-standard-pullbackᵉ gᵉ
  standard-pullback-cartesian-hom-arrowᵉ =
    ( hom-arrow-coneᵉ fᵉ gᵉ (cone-standard-pullbackᵉ fᵉ gᵉ) ,ᵉ is-equiv-idᵉ)
```

### Cartesian morphisms of arrows arising from fibers

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (yᵉ : Bᵉ)
  where

  fiber-cartesian-hom-arrowᵉ :
    cartesian-hom-arrowᵉ (terminal-mapᵉ (fiberᵉ fᵉ yᵉ)) fᵉ
  pr1ᵉ fiber-cartesian-hom-arrowᵉ =
    hom-arrow-coneᵉ (pointᵉ yᵉ) fᵉ (swap-coneᵉ fᵉ (pointᵉ yᵉ) (cone-fiberᵉ fᵉ yᵉ))
  pr2ᵉ fiber-cartesian-hom-arrowᵉ =
    is-pullback-swap-coneᵉ fᵉ (pointᵉ yᵉ)
      ( cone-fiberᵉ fᵉ yᵉ)
      ( is-pullback-cone-fiberᵉ fᵉ yᵉ)
```

### Transposing cartesian morphisms of arrows

Theᵉ {{#conceptᵉ "transposition"ᵉ Disambiguation="cartesianᵉ morphismᵉ ofᵉ arrows"ᵉ}}
ofᵉ aᵉ cartesianᵉ morphismᵉ ofᵉ arrowsᵉ

```text
        iᵉ
    Aᵉ ----->ᵉ Xᵉ
    | ⌟ᵉ      |
  fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
        jᵉ
```

isᵉ theᵉ cartesianᵉ morphismᵉ ofᵉ arrowsᵉ

```text
        fᵉ
    Aᵉ ----->ᵉ Bᵉ
    | ⌟ᵉ      |
  iᵉ |        | jᵉ
    ∨ᵉ        ∨ᵉ
    Xᵉ ----->ᵉ Y.ᵉ
        gᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : cartesian-hom-arrowᵉ fᵉ gᵉ)
  where

  is-cartesian-transpose-cartesian-hom-arrowᵉ :
    is-cartesian-hom-arrowᵉ
      ( map-domain-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( map-codomain-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( transpose-hom-arrowᵉ fᵉ gᵉ (hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ))
  is-cartesian-transpose-cartesian-hom-arrowᵉ =
    is-pullback-swap-coneᵉ
      ( map-codomain-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( gᵉ)
      ( cone-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( is-cartesian-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)

  transpose-cartesian-hom-arrowᵉ :
    cartesian-hom-arrowᵉ
      ( map-domain-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( map-codomain-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
  transpose-cartesian-hom-arrowᵉ =
    ( transpose-hom-arrowᵉ fᵉ gᵉ (hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ) ,ᵉ
      is-cartesian-transpose-cartesian-hom-arrowᵉ)
```

### If the target of a cartesian morphism is an equivalence then so is the source

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : cartesian-hom-arrowᵉ fᵉ gᵉ)
  where

  is-equiv-source-is-equiv-target-cartesian-hom-arrowᵉ : is-equivᵉ gᵉ → is-equivᵉ fᵉ
  is-equiv-source-is-equiv-target-cartesian-hom-arrowᵉ Gᵉ =
    is-equiv-vertical-map-is-pullbackᵉ
      ( map-codomain-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( gᵉ)
      ( cone-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( Gᵉ)
      ( is-cartesian-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
```

### If the target and source of a morphism of arrows are equivalences then the morphism is cartesian

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  is-cartesian-hom-arrow-is-equiv-source-is-equiv-targetᵉ :
    is-equivᵉ gᵉ → is-equivᵉ fᵉ → is-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ
  is-cartesian-hom-arrow-is-equiv-source-is-equiv-targetᵉ =
    is-pullback-is-equiv-vertical-mapsᵉ
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( gᵉ)
      ( cone-hom-arrowᵉ fᵉ gᵉ αᵉ)
```

### Cartesian morphisms of arrows are preserved under homotopies of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  where

  abstract
    is-cartesian-hom-arrow-htpyᵉ :
      {fᵉ f'ᵉ : Aᵉ → Bᵉ} (F'ᵉ : f'ᵉ ~ᵉ fᵉ) {gᵉ g'ᵉ : Xᵉ → Yᵉ} (Gᵉ : gᵉ ~ᵉ g'ᵉ)
      (αᵉ : hom-arrowᵉ fᵉ gᵉ) →
      is-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ →
      is-cartesian-hom-arrowᵉ f'ᵉ g'ᵉ (hom-arrow-htpyᵉ F'ᵉ Gᵉ αᵉ)
    is-cartesian-hom-arrow-htpyᵉ {fᵉ} F'ᵉ {gᵉ} Gᵉ αᵉ =
      is-pullback-htpyᵉ
        ( refl-htpyᵉ)
        ( inv-htpyᵉ Gᵉ)
        ( cone-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( ( F'ᵉ) ,ᵉ
          ( refl-htpyᵉ) ,ᵉ
          ( ( assoc-htpyᵉ
              ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ ·lᵉ F'ᵉ ∙hᵉ coh-hom-arrowᵉ fᵉ gᵉ αᵉ)
              ( Gᵉ ·rᵉ map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)
              ( inv-htpyᵉ (Gᵉ ·rᵉ map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ))) ∙hᵉ
            ( ap-concat-htpyᵉ
              ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ ·lᵉ F'ᵉ ∙hᵉ coh-hom-arrowᵉ fᵉ gᵉ αᵉ)
              ( right-inv-htpyᵉ Gᵉ ·rᵉ map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)) ∙hᵉ
            ( right-unit-htpyᵉ) ∙hᵉ
            ( ap-concat-htpy'ᵉ (coh-hom-arrowᵉ fᵉ gᵉ αᵉ) inv-htpy-right-unit-htpyᵉ)))

  cartesian-hom-arrow-htpyᵉ :
    {fᵉ f'ᵉ : Aᵉ → Bᵉ} (F'ᵉ : f'ᵉ ~ᵉ fᵉ) {gᵉ g'ᵉ : Xᵉ → Yᵉ} (Gᵉ : gᵉ ~ᵉ g'ᵉ) →
    cartesian-hom-arrowᵉ fᵉ gᵉ → cartesian-hom-arrowᵉ f'ᵉ g'ᵉ
  cartesian-hom-arrow-htpyᵉ F'ᵉ Gᵉ (αᵉ ,ᵉ Hᵉ) =
    ( hom-arrow-htpyᵉ F'ᵉ Gᵉ αᵉ ,ᵉ is-cartesian-hom-arrow-htpyᵉ F'ᵉ Gᵉ αᵉ Hᵉ)
```

### Cartesian morphisms of arrows are preserved under homotopies of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  abstract
    is-cartesian-htpy-hom-arrowᵉ :
      (αᵉ βᵉ : hom-arrowᵉ fᵉ gᵉ)
      (Hᵉ : htpy-hom-arrowᵉ fᵉ gᵉ βᵉ αᵉ) →
      is-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ →
      is-cartesian-hom-arrowᵉ fᵉ gᵉ βᵉ
    is-cartesian-htpy-hom-arrowᵉ αᵉ βᵉ Hᵉ =
      is-pullback-htpyᵉ
        ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ βᵉ αᵉ Hᵉ)
        ( refl-htpyᵉ)
        ( cone-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( htpy-parallell-cone-htpy-hom-arrowᵉ fᵉ gᵉ βᵉ αᵉ Hᵉ)
```

### The identity cartesian morphism of arrows

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  is-cartesian-id-hom-arrowᵉ : is-cartesian-hom-arrowᵉ fᵉ fᵉ id-hom-arrowᵉ
  is-cartesian-id-hom-arrowᵉ =
    is-pullback-is-equiv-horizontal-mapsᵉ idᵉ fᵉ
      ( fᵉ ,ᵉ idᵉ ,ᵉ refl-htpyᵉ)
      ( is-equiv-idᵉ)
      ( is-equiv-idᵉ)

  id-cartesian-hom-arrowᵉ : cartesian-hom-arrowᵉ fᵉ fᵉ
  id-cartesian-hom-arrowᵉ = (id-hom-arrowᵉ ,ᵉ is-cartesian-id-hom-arrowᵉ)
```

### Composition of cartesian morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ) (bᵉ : hom-arrowᵉ gᵉ hᵉ) (aᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  is-cartesian-comp-hom-arrowᵉ :
    is-cartesian-hom-arrowᵉ gᵉ hᵉ bᵉ →
    is-cartesian-hom-arrowᵉ fᵉ gᵉ aᵉ →
    is-cartesian-hom-arrowᵉ fᵉ hᵉ (comp-hom-arrowᵉ fᵉ gᵉ hᵉ bᵉ aᵉ)
  is-cartesian-comp-hom-arrowᵉ =
    is-pullback-rectangle-is-pullback-left-squareᵉ
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ aᵉ)
      ( map-codomain-hom-arrowᵉ gᵉ hᵉ bᵉ)
      ( hᵉ)
      ( cone-hom-arrowᵉ gᵉ hᵉ bᵉ)
      ( cone-hom-arrowᵉ fᵉ gᵉ aᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ)
  (bᵉ : cartesian-hom-arrowᵉ gᵉ hᵉ) (aᵉ : cartesian-hom-arrowᵉ fᵉ gᵉ)
  where

  comp-cartesian-hom-arrowᵉ : cartesian-hom-arrowᵉ fᵉ hᵉ
  comp-cartesian-hom-arrowᵉ =
    ( ( comp-hom-arrowᵉ fᵉ gᵉ hᵉ
        ( hom-arrow-cartesian-hom-arrowᵉ gᵉ hᵉ bᵉ)
        ( hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ aᵉ)) ,ᵉ
      ( is-cartesian-comp-hom-arrowᵉ fᵉ gᵉ hᵉ
        ( hom-arrow-cartesian-hom-arrowᵉ gᵉ hᵉ bᵉ)
        ( hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ aᵉ)
        ( is-cartesian-cartesian-hom-arrowᵉ gᵉ hᵉ bᵉ)
        ( is-cartesian-cartesian-hom-arrowᵉ fᵉ gᵉ aᵉ)))
```

### Left cancellation of cartesian morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ) (bᵉ : hom-arrowᵉ gᵉ hᵉ) (aᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  is-cartesian-hom-arrow-right-factorᵉ :
    is-cartesian-hom-arrowᵉ gᵉ hᵉ bᵉ →
    is-cartesian-hom-arrowᵉ fᵉ hᵉ (comp-hom-arrowᵉ fᵉ gᵉ hᵉ bᵉ aᵉ) →
    is-cartesian-hom-arrowᵉ fᵉ gᵉ aᵉ
  is-cartesian-hom-arrow-right-factorᵉ =
    is-pullback-left-square-is-pullback-rectangleᵉ
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ aᵉ)
      ( map-codomain-hom-arrowᵉ gᵉ hᵉ bᵉ)
      ( hᵉ)
      ( cone-hom-arrowᵉ gᵉ hᵉ bᵉ)
      ( cone-hom-arrowᵉ fᵉ gᵉ aᵉ)
```

### The left morphism in a commuting triangle of morphisms of arrows is cartesian if the other two are

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ)
  (leftᵉ : hom-arrowᵉ fᵉ hᵉ) (rightᵉ : hom-arrowᵉ gᵉ hᵉ) (topᵉ : hom-arrowᵉ fᵉ gᵉ)
  (Hᵉ : coherence-triangle-hom-arrowᵉ fᵉ gᵉ hᵉ leftᵉ rightᵉ topᵉ)
  where

  abstract
    is-cartesian-left-hom-arrow-triangleᵉ :
      is-cartesian-hom-arrowᵉ gᵉ hᵉ rightᵉ →
      is-cartesian-hom-arrowᵉ fᵉ gᵉ topᵉ →
      is-cartesian-hom-arrowᵉ fᵉ hᵉ leftᵉ
    is-cartesian-left-hom-arrow-triangleᵉ Rᵉ Tᵉ =
      is-cartesian-htpy-hom-arrowᵉ fᵉ hᵉ
        ( comp-hom-arrowᵉ fᵉ gᵉ hᵉ rightᵉ topᵉ)
        ( leftᵉ)
        ( Hᵉ)
        ( is-cartesian-comp-hom-arrowᵉ fᵉ gᵉ hᵉ rightᵉ topᵉ Rᵉ Tᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ)
  (topᵉ : cartesian-hom-arrowᵉ fᵉ gᵉ)
  (leftᵉ : hom-arrowᵉ fᵉ hᵉ)
  (rightᵉ : cartesian-hom-arrowᵉ gᵉ hᵉ)
  (Hᵉ :
    coherence-triangle-hom-arrowᵉ fᵉ gᵉ hᵉ
      ( leftᵉ)
      ( hom-arrow-cartesian-hom-arrowᵉ gᵉ hᵉ rightᵉ)
      ( hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ topᵉ))
  where

  abstract
    is-cartesian-left-cartesian-hom-arrow-triangleᵉ :
      is-cartesian-hom-arrowᵉ fᵉ hᵉ leftᵉ
    is-cartesian-left-cartesian-hom-arrow-triangleᵉ =
      is-cartesian-left-hom-arrow-triangleᵉ fᵉ gᵉ hᵉ
        ( leftᵉ)
        ( hom-arrow-cartesian-hom-arrowᵉ gᵉ hᵉ rightᵉ)
        ( hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ topᵉ)
        ( Hᵉ)
        ( is-cartesian-cartesian-hom-arrowᵉ gᵉ hᵉ rightᵉ)
        ( is-cartesian-cartesian-hom-arrowᵉ fᵉ gᵉ topᵉ)
```

### The top morphism in a commuting triangle of morphisms of arrows is cartesian if the other two are

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ)
  (leftᵉ : hom-arrowᵉ fᵉ hᵉ) (rightᵉ : hom-arrowᵉ gᵉ hᵉ) (topᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  abstract
    is-cartesian-top-hom-arrow-triangle'ᵉ :
      (Hᵉ : coherence-triangle-hom-arrow'ᵉ fᵉ gᵉ hᵉ leftᵉ rightᵉ topᵉ) →
      is-cartesian-hom-arrowᵉ gᵉ hᵉ rightᵉ →
      is-cartesian-hom-arrowᵉ fᵉ hᵉ leftᵉ →
      is-cartesian-hom-arrowᵉ fᵉ gᵉ topᵉ
    is-cartesian-top-hom-arrow-triangle'ᵉ Hᵉ Rᵉ Lᵉ =
      is-cartesian-hom-arrow-right-factorᵉ fᵉ gᵉ hᵉ rightᵉ topᵉ Rᵉ
        ( is-cartesian-htpy-hom-arrowᵉ fᵉ hᵉ
          ( leftᵉ)
          ( comp-hom-arrowᵉ fᵉ gᵉ hᵉ rightᵉ topᵉ)
          ( Hᵉ)
          ( Lᵉ))

  abstract
    is-cartesian-top-hom-arrow-triangleᵉ :
      (Hᵉ : coherence-triangle-hom-arrowᵉ fᵉ gᵉ hᵉ leftᵉ rightᵉ topᵉ) →
      is-cartesian-hom-arrowᵉ gᵉ hᵉ rightᵉ →
      is-cartesian-hom-arrowᵉ fᵉ hᵉ leftᵉ →
      is-cartesian-hom-arrowᵉ fᵉ gᵉ topᵉ
    is-cartesian-top-hom-arrow-triangleᵉ Hᵉ =
      is-cartesian-top-hom-arrow-triangle'ᵉ
        ( inv-htpy-hom-arrowᵉ fᵉ hᵉ leftᵉ (comp-hom-arrowᵉ fᵉ gᵉ hᵉ rightᵉ topᵉ) Hᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ)
  (topᵉ : hom-arrowᵉ fᵉ gᵉ)
  (leftᵉ : cartesian-hom-arrowᵉ fᵉ hᵉ)
  (rightᵉ : cartesian-hom-arrowᵉ gᵉ hᵉ)
  where

  abstract
    is-cartesian-top-cartesian-hom-arrow-triangle'ᵉ :
      (Hᵉ :
        coherence-triangle-hom-arrow'ᵉ fᵉ gᵉ hᵉ
          ( hom-arrow-cartesian-hom-arrowᵉ fᵉ hᵉ leftᵉ)
          ( hom-arrow-cartesian-hom-arrowᵉ gᵉ hᵉ rightᵉ)
          ( topᵉ)) →
      is-cartesian-hom-arrowᵉ fᵉ gᵉ topᵉ
    is-cartesian-top-cartesian-hom-arrow-triangle'ᵉ Hᵉ =
      is-cartesian-top-hom-arrow-triangle'ᵉ fᵉ gᵉ hᵉ
        ( hom-arrow-cartesian-hom-arrowᵉ fᵉ hᵉ leftᵉ)
        ( hom-arrow-cartesian-hom-arrowᵉ gᵉ hᵉ rightᵉ)
        ( topᵉ)
        ( Hᵉ)
        ( is-cartesian-cartesian-hom-arrowᵉ gᵉ hᵉ rightᵉ)
        ( is-cartesian-cartesian-hom-arrowᵉ fᵉ hᵉ leftᵉ)

  abstract
    is-cartesian-top-cartesian-hom-arrow-triangleᵉ :
      (Hᵉ :
        coherence-triangle-hom-arrowᵉ fᵉ gᵉ hᵉ
          ( hom-arrow-cartesian-hom-arrowᵉ fᵉ hᵉ leftᵉ)
          ( hom-arrow-cartesian-hom-arrowᵉ gᵉ hᵉ rightᵉ)
          ( topᵉ)) →
      is-cartesian-hom-arrowᵉ fᵉ gᵉ topᵉ
    is-cartesian-top-cartesian-hom-arrow-triangleᵉ Hᵉ =
      is-cartesian-top-hom-arrow-triangleᵉ fᵉ gᵉ hᵉ
        ( hom-arrow-cartesian-hom-arrowᵉ fᵉ hᵉ leftᵉ)
        ( hom-arrow-cartesian-hom-arrowᵉ gᵉ hᵉ rightᵉ)
        ( topᵉ)
        ( Hᵉ)
        ( is-cartesian-cartesian-hom-arrowᵉ gᵉ hᵉ rightᵉ)
        ( is-cartesian-cartesian-hom-arrowᵉ fᵉ hᵉ leftᵉ)
```

### Dependent products of cartesian morphisms of arrows

Givenᵉ aᵉ familyᵉ ofᵉ cartesianᵉ morphismsᵉ ofᵉ arrowsᵉ `αᵢᵉ : fᵢᵉ → gᵢ`,ᵉ thenᵉ thereᵉ isᵉ aᵉ
cartesianᵉ morphismᵉ ofᵉ arrowsᵉ `map-Πᵉ fᵉ → map-Πᵉ g`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Iᵉ : UUᵉ l5ᵉ} {Aᵉ : Iᵉ → UUᵉ l1ᵉ} {Bᵉ : Iᵉ → UUᵉ l2ᵉ} {Xᵉ : Iᵉ → UUᵉ l3ᵉ} {Yᵉ : Iᵉ → UUᵉ l4ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ) (gᵉ : (iᵉ : Iᵉ) → Xᵉ iᵉ → Yᵉ iᵉ)
  (αᵉ : (iᵉ : Iᵉ) → cartesian-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ))
  where

  hom-arrow-Π-cartesian-hom-arrowᵉ :
    hom-arrowᵉ (map-Πᵉ fᵉ) (map-Πᵉ gᵉ)
  hom-arrow-Π-cartesian-hom-arrowᵉ =
    Π-hom-arrowᵉ fᵉ gᵉ (λ iᵉ → hom-arrow-cartesian-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))

  is-cartesian-Π-cartesian-hom-arrowᵉ :
    is-cartesian-hom-arrowᵉ (map-Πᵉ fᵉ) (map-Πᵉ gᵉ) hom-arrow-Π-cartesian-hom-arrowᵉ
  is-cartesian-Π-cartesian-hom-arrowᵉ =
    is-pullback-Πᵉ
      ( λ iᵉ → map-codomain-cartesian-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))
      ( gᵉ)
      ( λ iᵉ → cone-cartesian-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))
      ( λ iᵉ → is-cartesian-cartesian-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))

  Π-cartesian-hom-arrowᵉ :
    cartesian-hom-arrowᵉ (map-Πᵉ fᵉ) (map-Πᵉ gᵉ)
  pr1ᵉ Π-cartesian-hom-arrowᵉ = hom-arrow-Π-cartesian-hom-arrowᵉ
  pr2ᵉ Π-cartesian-hom-arrowᵉ = is-cartesian-Π-cartesian-hom-arrowᵉ
```

### Dependent sums of cartesian morphisms of arrows

Givenᵉ aᵉ familyᵉ ofᵉ cartesianᵉ morphismsᵉ ofᵉ arrowsᵉ `αᵢᵉ : fᵢᵉ → gᵢ`,ᵉ thenᵉ thereᵉ isᵉ aᵉ
cartesianᵉ morphismᵉ ofᵉ arrowsᵉ `totᵉ fᵉ → totᵉ g`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Iᵉ : UUᵉ l5ᵉ} {Aᵉ : Iᵉ → UUᵉ l1ᵉ} {Bᵉ : Iᵉ → UUᵉ l2ᵉ} {Xᵉ : Iᵉ → UUᵉ l3ᵉ} {Yᵉ : Iᵉ → UUᵉ l4ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ) (gᵉ : (iᵉ : Iᵉ) → Xᵉ iᵉ → Yᵉ iᵉ)
  (αᵉ : (iᵉ : Iᵉ) → cartesian-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ))
  where

  hom-arrow-tot-cartesian-hom-arrowᵉ :
    hom-arrowᵉ (totᵉ fᵉ) (totᵉ gᵉ)
  hom-arrow-tot-cartesian-hom-arrowᵉ =
    tot-hom-arrowᵉ fᵉ gᵉ (λ iᵉ → hom-arrow-cartesian-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))

  is-cartesian-tot-cartesian-hom-arrowᵉ :
    is-cartesian-hom-arrowᵉ (totᵉ fᵉ) (totᵉ gᵉ) hom-arrow-tot-cartesian-hom-arrowᵉ
  is-cartesian-tot-cartesian-hom-arrowᵉ =
    is-pullback-tot-is-pullback-family-id-coneᵉ
      ( λ iᵉ → map-codomain-cartesian-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))
      ( gᵉ)
      ( λ iᵉ → cone-cartesian-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))
      ( λ iᵉ → is-cartesian-cartesian-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))

  tot-cartesian-hom-arrowᵉ :
    cartesian-hom-arrowᵉ (totᵉ fᵉ) (totᵉ gᵉ)
  pr1ᵉ tot-cartesian-hom-arrowᵉ = hom-arrow-tot-cartesian-hom-arrowᵉ
  pr2ᵉ tot-cartesian-hom-arrowᵉ = is-cartesian-tot-cartesian-hom-arrowᵉ
```

### Cartesian morphisms of arrows are preserved under products

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  {Cᵉ : UUᵉ l5ᵉ} {Dᵉ : UUᵉ l6ᵉ} {Zᵉ : UUᵉ l7ᵉ} {Wᵉ : UUᵉ l8ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Cᵉ → Dᵉ) (iᵉ : Zᵉ → Wᵉ)
  (αᵉ : cartesian-hom-arrowᵉ fᵉ gᵉ) (βᵉ : cartesian-hom-arrowᵉ hᵉ iᵉ)
  where

  is-cartesian-product-cartesian-hom-arrowᵉ :
    is-cartesian-hom-arrowᵉ
      ( map-productᵉ fᵉ hᵉ)
      ( map-productᵉ gᵉ iᵉ)
      ( product-hom-arrowᵉ fᵉ gᵉ hᵉ iᵉ
        ( hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( hom-arrow-cartesian-hom-arrowᵉ hᵉ iᵉ βᵉ))
  is-cartesian-product-cartesian-hom-arrowᵉ =
    is-pullback-product-is-pullbackᵉ
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ (hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ))
      ( gᵉ)
      ( map-codomain-hom-arrowᵉ hᵉ iᵉ (hom-arrow-cartesian-hom-arrowᵉ hᵉ iᵉ βᵉ))
      ( iᵉ)
      ( cone-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( cone-cartesian-hom-arrowᵉ hᵉ iᵉ βᵉ)
      ( is-cartesian-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( is-cartesian-cartesian-hom-arrowᵉ hᵉ iᵉ βᵉ)

  product-cartesian-hom-arrowᵉ :
    cartesian-hom-arrowᵉ (map-productᵉ fᵉ hᵉ) (map-productᵉ gᵉ iᵉ)
  product-cartesian-hom-arrowᵉ =
    ( ( product-hom-arrowᵉ fᵉ gᵉ hᵉ iᵉ
        ( hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( hom-arrow-cartesian-hom-arrowᵉ hᵉ iᵉ βᵉ)) ,ᵉ
      ( is-cartesian-product-cartesian-hom-arrowᵉ))
```

### Cartesian morphisms of arrows are preserved under coproducts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  {Cᵉ : UUᵉ l5ᵉ} {Dᵉ : UUᵉ l6ᵉ} {Zᵉ : UUᵉ l7ᵉ} {Wᵉ : UUᵉ l8ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Cᵉ → Dᵉ) (iᵉ : Zᵉ → Wᵉ)
  (αᵉ : cartesian-hom-arrowᵉ fᵉ gᵉ) (βᵉ : cartesian-hom-arrowᵉ hᵉ iᵉ)
  where

  is-cartesian-coproduct-cartesian-hom-arrowᵉ :
    is-cartesian-hom-arrowᵉ
      ( map-coproductᵉ fᵉ hᵉ)
      ( map-coproductᵉ gᵉ iᵉ)
      ( coproduct-hom-arrowᵉ fᵉ gᵉ hᵉ iᵉ
        ( hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( hom-arrow-cartesian-hom-arrowᵉ hᵉ iᵉ βᵉ))
  is-cartesian-coproduct-cartesian-hom-arrowᵉ =
    is-pullback-coproduct-is-pullbackᵉ
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ (hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ))
      ( gᵉ)
      ( map-codomain-hom-arrowᵉ hᵉ iᵉ (hom-arrow-cartesian-hom-arrowᵉ hᵉ iᵉ βᵉ))
      ( iᵉ)
      ( cone-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( cone-cartesian-hom-arrowᵉ hᵉ iᵉ βᵉ)
      ( is-cartesian-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( is-cartesian-cartesian-hom-arrowᵉ hᵉ iᵉ βᵉ)

  coproduct-cartesian-hom-arrowᵉ :
    cartesian-hom-arrowᵉ (map-coproductᵉ fᵉ hᵉ) (map-coproductᵉ gᵉ iᵉ)
  coproduct-cartesian-hom-arrowᵉ =
    ( ( coproduct-hom-arrowᵉ fᵉ gᵉ hᵉ iᵉ
        ( hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( hom-arrow-cartesian-hom-arrowᵉ hᵉ iᵉ βᵉ)) ,ᵉ
      ( is-cartesian-coproduct-cartesian-hom-arrowᵉ))
```

### Cartesian morphisms of arrows are preserved under exponentiation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : cartesian-hom-arrowᵉ fᵉ gᵉ) (Sᵉ : UUᵉ l5ᵉ)
  where

  hom-arrow-postcomp-cartesian-hom-arrowᵉ :
    hom-arrowᵉ (postcompᵉ Sᵉ fᵉ) (postcompᵉ Sᵉ gᵉ)
  hom-arrow-postcomp-cartesian-hom-arrowᵉ =
    postcomp-hom-arrowᵉ fᵉ gᵉ (hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ) Sᵉ

  is-cartesian-postcomp-cartesian-hom-arrowᵉ :
    is-cartesian-hom-arrowᵉ
      ( postcompᵉ Sᵉ fᵉ)
      ( postcompᵉ Sᵉ gᵉ)
      ( hom-arrow-postcomp-cartesian-hom-arrowᵉ)
  is-cartesian-postcomp-cartesian-hom-arrowᵉ =
    is-pullback-postcomp-is-pullbackᵉ
      ( map-codomain-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( gᵉ)
      ( cone-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( is-cartesian-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( Sᵉ)

  postcomp-cartesian-hom-arrowᵉ :
    cartesian-hom-arrowᵉ (postcompᵉ Sᵉ fᵉ) (postcompᵉ Sᵉ gᵉ)
  pr1ᵉ postcomp-cartesian-hom-arrowᵉ =
    hom-arrow-postcomp-cartesian-hom-arrowᵉ
  pr2ᵉ postcomp-cartesian-hom-arrowᵉ = is-cartesian-postcomp-cartesian-hom-arrowᵉ
```

### A folding operation on cartesian morphisms of arrows

Aᵉ morphismᵉ ofᵉ arrowsᵉ

```text
         iᵉ
    Aᵉ ------>ᵉ Xᵉ
    |         |
  fᵉ |         | gᵉ
    ∨ᵉ         ∨ᵉ
    Bᵉ ------>ᵉ Yᵉ
         jᵉ
```

isᵉ cartesianᵉ ifᵉ andᵉ onlyᵉ ifᵉ eitherᵉ ofᵉ theᵉ foldedᵉ morphismsᵉ

```text
          (fᵉ ,ᵉ iᵉ)                       (fᵉ ,ᵉ iᵉ)
        Aᵉ ------>ᵉ Bᵉ ×ᵉ Xᵉ               Aᵉ ------>ᵉ Bᵉ ×ᵉ Xᵉ
        |           |                 |           |
  gᵉ ∘ᵉ iᵉ |           | jᵉ ×ᵉ gᵉ     jᵉ ∘ᵉ fᵉ |           | jᵉ ×ᵉ gᵉ
        ∨ᵉ           ∨ᵉ                 ∨ᵉ           ∨ᵉ
        Yᵉ ------>ᵉ Yᵉ ×ᵉ Yᵉ               Yᵉ ------>ᵉ Yᵉ ×ᵉ Yᵉ
             Δᵉ                             Δᵉ
```

is.ᵉ

Itᵉ remainsᵉ to formalizeᵉ theᵉ right-handᵉ version.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  transpose-fold-hom-arrowᵉ :
    hom-arrowᵉ
      ( λ xᵉ → (fᵉ xᵉ ,ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ xᵉ))
      ( diagonal-productᵉ Yᵉ)
  transpose-fold-hom-arrowᵉ =
    hom-arrow-coneᵉ
      ( map-productᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ) gᵉ)
      ( diagonal-productᵉ Yᵉ)
      ( fold-coneᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ) gᵉ (cone-hom-arrowᵉ fᵉ gᵉ αᵉ))

  fold-hom-arrowᵉ :
    hom-arrowᵉ
      ( gᵉ ∘ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( map-productᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ) gᵉ)
  fold-hom-arrowᵉ =
    transpose-hom-arrowᵉ
      ( λ aᵉ → fᵉ aᵉ ,ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)
      ( diagonal-productᵉ Yᵉ)
      ( transpose-fold-hom-arrowᵉ)

  is-cartesian-transpose-fold-hom-arrowᵉ :
    is-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ →
    is-cartesian-hom-arrowᵉ
      ( λ xᵉ → (fᵉ xᵉ ,ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ xᵉ))
      ( diagonal-productᵉ Yᵉ)
      ( transpose-fold-hom-arrowᵉ)
  is-cartesian-transpose-fold-hom-arrowᵉ =
    is-pullback-fold-cone-is-pullbackᵉ
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( gᵉ)
      ( cone-hom-arrowᵉ fᵉ gᵉ αᵉ)

  is-cartesian-is-cartesian-transpose-fold-hom-arrowᵉ :
    is-cartesian-hom-arrowᵉ
      ( λ xᵉ → (fᵉ xᵉ ,ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ xᵉ))
      ( diagonal-productᵉ Yᵉ)
      ( transpose-fold-hom-arrowᵉ) →
    is-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ
  is-cartesian-is-cartesian-transpose-fold-hom-arrowᵉ =
    is-pullback-is-pullback-fold-coneᵉ
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( gᵉ)
      ( cone-hom-arrowᵉ fᵉ gᵉ αᵉ)

  is-cartesian-fold-hom-arrowᵉ :
    is-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ →
    is-cartesian-hom-arrowᵉ
      ( gᵉ ∘ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( map-productᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ) gᵉ)
      ( fold-hom-arrowᵉ)
  is-cartesian-fold-hom-arrowᵉ Hᵉ =
    is-cartesian-transpose-cartesian-hom-arrowᵉ
      ( λ xᵉ → (fᵉ xᵉ ,ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ xᵉ))
      ( diagonal-productᵉ Yᵉ)
      ( transpose-fold-hom-arrowᵉ ,ᵉ is-cartesian-transpose-fold-hom-arrowᵉ Hᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  (αᵉ : cartesian-hom-arrowᵉ fᵉ gᵉ)
  where

  transpose-fold-cartesian-hom-arrowᵉ :
    cartesian-hom-arrowᵉ
      ( λ xᵉ → (fᵉ xᵉ ,ᵉ map-domain-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ xᵉ))
      ( diagonal-productᵉ Yᵉ)
  pr1ᵉ transpose-fold-cartesian-hom-arrowᵉ =
    transpose-fold-hom-arrowᵉ fᵉ gᵉ (hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
  pr2ᵉ transpose-fold-cartesian-hom-arrowᵉ =
    is-cartesian-transpose-fold-hom-arrowᵉ fᵉ gᵉ
      ( hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( is-cartesian-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)

  fold-cartesian-hom-arrowᵉ :
    cartesian-hom-arrowᵉ
      ( gᵉ ∘ᵉ map-domain-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( map-productᵉ (map-codomain-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ) gᵉ)
  pr1ᵉ fold-cartesian-hom-arrowᵉ =
    fold-hom-arrowᵉ fᵉ gᵉ (hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
  pr2ᵉ fold-cartesian-hom-arrowᵉ =
    is-cartesian-fold-hom-arrowᵉ fᵉ gᵉ
      ( hom-arrow-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( is-cartesian-cartesian-hom-arrowᵉ fᵉ gᵉ αᵉ)
```

### Lifting cartesian morphisms along lifts of the codomain

Supposeᵉ givenᵉ aᵉ cospanᵉ ofᵉ morphismsᵉ ofᵉ arrowsᵉ

```text
    Aᵉ ------>ᵉ Cᵉ <------ᵉ Bᵉ
    |         |       ⌞ᵉ |
  fᵉ |    αᵉ    hᵉ    βᵉ    | gᵉ
    ∨ᵉ         ∨ᵉ         ∨ᵉ
    A'ᵉ ----->ᵉ C'ᵉ <-----ᵉ B'ᵉ
```

where `β`ᵉ isᵉ cartesian.ᵉ Moreover,ᵉ supposeᵉ weᵉ haveᵉ aᵉ mapᵉ `iᵉ : A'ᵉ → B'`ᵉ fromᵉ theᵉ
codomainᵉ ofᵉ theᵉ sourceᵉ ofᵉ `α`ᵉ to theᵉ codomainᵉ ofᵉ theᵉ sourceᵉ ofᵉ `β`ᵉ suchᵉ thatᵉ theᵉ
triangleᵉ

```text
         iᵉ
     A'ᵉ --->ᵉ B'ᵉ
      \ᵉ     /ᵉ
       \ᵉ   /ᵉ
        ∨ᵉ ∨ᵉ
         C'ᵉ
```

commutes.ᵉ Thenᵉ thereᵉ isᵉ aᵉ uniqueᵉ morphismᵉ ofᵉ arrowsᵉ `γᵉ : fᵉ → g`ᵉ with aᵉ homotopyᵉ
`βᵉ ~ᵉ αᵉ ∘ᵉ γ`ᵉ extendingᵉ theᵉ triangle,ᵉ andᵉ thisᵉ morphismᵉ isᵉ cartesianᵉ ifᵉ andᵉ onlyᵉ
ifᵉ `α`ᵉ is.ᵉ

**Proof.**ᵉ Theᵉ uniqueᵉ existenceᵉ ofᵉ `γ`ᵉ andᵉ theᵉ homotopyᵉ followsᵉ fromᵉ theᵉ
pullbackᵉ propertyᵉ ofᵉ `β`.ᵉ Theᵉ restᵉ isᵉ aᵉ reiterationᵉ ofᵉ theᵉ 3-for-2ᵉ propertyᵉ ofᵉ
cartesianᵉ morphisms.ᵉ

Weᵉ beginᵉ byᵉ constructingᵉ theᵉ commutingᵉ triangleᵉ ofᵉ morphismsᵉ ofᵉ arrowsᵉ:

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {A'ᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {B'ᵉ : UUᵉ l4ᵉ} {Cᵉ : UUᵉ l5ᵉ} {C'ᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → A'ᵉ) (gᵉ : Bᵉ → B'ᵉ) (hᵉ : Cᵉ → C'ᵉ)
  (βᵉ : cartesian-hom-arrowᵉ gᵉ hᵉ)
  (αᵉ : hom-arrowᵉ fᵉ hᵉ)
  (iᵉ : A'ᵉ → B'ᵉ)
  (Hᵉ :
    coherence-triangle-maps'ᵉ
      ( map-codomain-hom-arrowᵉ fᵉ hᵉ αᵉ)
      ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
      ( iᵉ))
  where

  cone-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ :
    coneᵉ (map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ) hᵉ Aᵉ
  cone-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ =
    ( iᵉ ∘ᵉ fᵉ ,ᵉ map-domain-hom-arrowᵉ fᵉ hᵉ αᵉ ,ᵉ Hᵉ ·rᵉ fᵉ ∙hᵉ coh-hom-arrowᵉ fᵉ hᵉ αᵉ)

  map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ : Aᵉ → Bᵉ
  map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ =
    gap-is-pullbackᵉ
      ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
      ( hᵉ)
      ( cone-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
      ( is-cartesian-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
      ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ)

  hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ : hom-arrowᵉ fᵉ gᵉ
  pr1ᵉ hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ =
    map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ
  pr1ᵉ (pr2ᵉ hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ) = iᵉ
  pr2ᵉ (pr2ᵉ hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ) =
    inv-htpyᵉ
      ( htpy-vertical-map-gap-is-pullbackᵉ
        ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
        ( hᵉ)
        ( cone-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
        ( is-cartesian-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
        ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ))

  abstract
    inv-coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ :
      coherence-triangle-hom-arrow'ᵉ fᵉ gᵉ hᵉ
        ( αᵉ)
        ( hom-arrow-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
        ( hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ)
    inv-coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ =
      ( htpy-horizontal-map-gap-is-pullbackᵉ
          ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
          ( hᵉ)
          ( cone-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
          ( is-cartesian-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
          ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ)) ,ᵉ
      ( Hᵉ) ,ᵉ
      ( ( ap-concat-htpy'ᵉ
          ( ( hᵉ) ·lᵉ
            ( htpy-horizontal-map-gap-is-pullbackᵉ
              ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
              ( hᵉ)
              ( cone-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
              ( pr2ᵉ βᵉ)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ)))
          ( ap-concat-htpy'ᵉ
            ( coh-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ ·rᵉ
              map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ)
            ( left-whisker-inv-htpyᵉ
              ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
              ( htpy-vertical-map-gap-is-pullbackᵉ
                ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
                ( hᵉ)
                ( cone-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
                ( pr2ᵉ βᵉ)
                ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ))))) ∙hᵉ
        ( assoc-htpyᵉ
          ( inv-htpyᵉ
            ( ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ) ·lᵉ
              ( htpy-vertical-map-gap-is-pullbackᵉ
                ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
                ( hᵉ)
                ( cone-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
                ( pr2ᵉ βᵉ)
                ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ))))
          ( coh-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ ·rᵉ
            map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ)
          ( ( hᵉ) ·lᵉ
            ( htpy-horizontal-map-gap-is-pullbackᵉ
              ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
              ( hᵉ)
              ( cone-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
              ( pr2ᵉ βᵉ)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ)))) ∙hᵉ
        ( inv-htpy-left-transpose-htpy-concatᵉ
          ( ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ) ·lᵉ
            ( htpy-vertical-map-gap-is-pullbackᵉ
              ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
              ( hᵉ)
              ( cone-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
              ( pr2ᵉ βᵉ)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ)))
          ( Hᵉ ·rᵉ fᵉ ∙hᵉ coh-hom-arrowᵉ fᵉ hᵉ αᵉ)
          ( ( coh-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ ·rᵉ
              map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ) ∙hᵉ
            ( hᵉ) ·lᵉ
            ( htpy-horizontal-map-gap-is-pullbackᵉ
              ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
              ( hᵉ)
              ( cone-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
              ( is-cartesian-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ)))
          ( inv-htpyᵉ
            ( coh-htpy-cone-gap-is-pullbackᵉ
              ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
              ( hᵉ)
              ( cone-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
              ( is-cartesian-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ)))))

  coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ :
    coherence-triangle-hom-arrowᵉ fᵉ gᵉ hᵉ
      ( αᵉ)
      ( hom-arrow-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
      ( hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ)
  coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ =
    inv-htpy-hom-arrowᵉ fᵉ hᵉ
      ( comp-hom-arrowᵉ fᵉ gᵉ hᵉ
        ( hom-arrow-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
        ( hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ))
      ( αᵉ)
      ( inv-coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ)
```

Now,ᵉ ifᵉ `α`ᵉ wasᵉ cartesianᵉ to beginᵉ with,ᵉ theᵉ liftᵉ isᵉ also.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {A'ᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {B'ᵉ : UUᵉ l4ᵉ} {Cᵉ : UUᵉ l5ᵉ} {C'ᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → A'ᵉ) (gᵉ : Bᵉ → B'ᵉ) (hᵉ : Cᵉ → C'ᵉ)
  (βᵉ : cartesian-hom-arrowᵉ gᵉ hᵉ)
  (αᵉ : cartesian-hom-arrowᵉ fᵉ hᵉ)
  (iᵉ : A'ᵉ → B'ᵉ)
  (Hᵉ :
    coherence-triangle-maps'ᵉ
      ( map-codomain-cartesian-hom-arrowᵉ fᵉ hᵉ αᵉ)
      ( map-codomain-cartesian-hom-arrowᵉ gᵉ hᵉ βᵉ)
      ( iᵉ))
  where

  abstract
    is-cartesian-cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ :
      is-cartesian-hom-arrowᵉ fᵉ gᵉ
        ( hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ fᵉ gᵉ hᵉ
          ( βᵉ)
          ( hom-arrow-cartesian-hom-arrowᵉ fᵉ hᵉ αᵉ)
          ( iᵉ)
          ( Hᵉ))
    is-cartesian-cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ =
      is-cartesian-top-cartesian-hom-arrow-triangle'ᵉ fᵉ gᵉ hᵉ
        ( hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ
          ( fᵉ) gᵉ hᵉ βᵉ (hom-arrow-cartesian-hom-arrowᵉ fᵉ hᵉ αᵉ) iᵉ Hᵉ)
        ( αᵉ)
        ( βᵉ)
        ( inv-coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ
          ( fᵉ) gᵉ hᵉ βᵉ (hom-arrow-cartesian-hom-arrowᵉ fᵉ hᵉ αᵉ) iᵉ Hᵉ)

  cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ :
    cartesian-hom-arrowᵉ fᵉ gᵉ
  cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ =
    ( hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ
      ( fᵉ) gᵉ hᵉ βᵉ (hom-arrow-cartesian-hom-arrowᵉ fᵉ hᵉ αᵉ) iᵉ Hᵉ) ,ᵉ
    ( is-cartesian-cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrowᵉ)
```

## See also

-ᵉ [Cocartesianᵉ morphismsᵉ ofᵉ arrows](synthetic-homotopy-theory.cocartesian-morphisms-arrows.mdᵉ)
  forᵉ theᵉ dual.ᵉ
-ᵉ [Diagonalsᵉ ofᵉ morphismsᵉ ofᵉ arrows](foundation.diagonals-of-morphisms-arrows.mdᵉ)
  isᵉ anotherᵉ operationᵉ thatᵉ preservesᵉ cartesianness.ᵉ