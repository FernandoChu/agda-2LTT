# The universal properties of cartesian product types

```agda
module foundation.universal-property-cartesian-product-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.pullbacksᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.universal-property-pullbacksᵉ
```

</details>

## Idea

[Cartesianᵉ products](foundation-core.cartesian-product-types.mdᵉ) haveᵉ universalᵉ
propertiesᵉ bothᵉ asᵉ limitsᵉ andᵉ asᵉ colimitsᵉ ofᵉ types.ᵉ Theᵉ
{{#conceptᵉ "universalᵉ propertyᵉ ofᵉ cartesianᵉ productsᵉ asᵉ limits"ᵉ}} statesᵉ that,ᵉ
givenᵉ typesᵉ `A`,ᵉ `B`ᵉ andᵉ `X`,ᵉ mapsᵉ _intoᵉ_ theᵉ cartesianᵉ productᵉ `Xᵉ → Aᵉ ×ᵉ B`ᵉ areᵉ
in [correspondence](foundation-core.equivalences.mdᵉ) with pairsᵉ ofᵉ mapsᵉ `Xᵉ → A`ᵉ
andᵉ `Xᵉ → B`.ᵉ Theᵉ
{{#conceptᵉ "universalᵉ propertyᵉ ofᵉ cartesianᵉ productsᵉ asᵉ colimits"ᵉ}} statesᵉ thatᵉ
mapsᵉ _outᵉ ofᵉ_ theᵉ cartesianᵉ productᵉ `Aᵉ ×ᵉ Bᵉ → X`ᵉ areᵉ in correspondenceᵉ with
"curried"ᵉ mapsᵉ `Aᵉ → Bᵉ → X`.ᵉ

Observeᵉ thatᵉ theᵉ universalᵉ propertyᵉ ofᵉ cartesianᵉ productsᵉ asᵉ limitsᵉ canᵉ beᵉ
understoodᵉ asᵉ aᵉ categorifiedᵉ versionᵉ ofᵉ theᵉ familiarᵉ distributivityᵉ ofᵉ exponentsᵉ
overᵉ productsᵉ

$$ᵉ
(Aᵉ ×ᵉ B)^Xᵉ ≃ᵉ A^Xᵉ ×ᵉ B^X,ᵉ
$$ᵉ

whileᵉ theᵉ universalᵉ propertyᵉ ofᵉ cartesianᵉ productsᵉ asᵉ colimitsᵉ areᵉ aᵉ
categorifiedᵉ versionᵉ ofᵉ theᵉ identityᵉ

$$ᵉ
X^{(Aᵉ ×ᵉ Bᵉ)} ≃ᵉ {(X^B)}^A.ᵉ
$$ᵉ

## Theorems

### The universal property of cartesian products as limits

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : Xᵉ → UUᵉ l2ᵉ} {Bᵉ : Xᵉ → UUᵉ l3ᵉ}
  where

  map-up-productᵉ :
    ((xᵉ : Xᵉ) → Aᵉ xᵉ ×ᵉ Bᵉ xᵉ) → ((xᵉ : Xᵉ) → Aᵉ xᵉ) ×ᵉ ((xᵉ : Xᵉ) → Bᵉ xᵉ)
  pr1ᵉ (map-up-productᵉ fᵉ) xᵉ = pr1ᵉ (fᵉ xᵉ)
  pr2ᵉ (map-up-productᵉ fᵉ) xᵉ = pr2ᵉ (fᵉ xᵉ)

  map-inv-up-productᵉ :
    (((xᵉ : Xᵉ) → Aᵉ xᵉ) ×ᵉ ((xᵉ : Xᵉ) → Bᵉ xᵉ)) → (xᵉ : Xᵉ) → Aᵉ xᵉ ×ᵉ Bᵉ xᵉ
  pr1ᵉ (map-inv-up-productᵉ (fᵉ ,ᵉ gᵉ) xᵉ) = fᵉ xᵉ
  pr2ᵉ (map-inv-up-productᵉ (fᵉ ,ᵉ gᵉ) xᵉ) = gᵉ xᵉ

  iff-up-productᵉ :
    ((xᵉ : Xᵉ) → Aᵉ xᵉ ×ᵉ Bᵉ xᵉ) ↔ᵉ ((xᵉ : Xᵉ) → Aᵉ xᵉ) ×ᵉ ((xᵉ : Xᵉ) → Bᵉ xᵉ)
  iff-up-productᵉ = (map-up-productᵉ ,ᵉ map-inv-up-productᵉ)

  up-productᵉ : is-equivᵉ map-up-productᵉ
  up-productᵉ =
    is-equiv-is-invertibleᵉ (map-inv-up-productᵉ) (refl-htpyᵉ) (refl-htpyᵉ)

  is-equiv-map-inv-up-productᵉ : is-equivᵉ map-inv-up-productᵉ
  is-equiv-map-inv-up-productᵉ = is-equiv-map-inv-is-equivᵉ up-productᵉ

  equiv-up-productᵉ :
    ((xᵉ : Xᵉ) → Aᵉ xᵉ ×ᵉ Bᵉ xᵉ) ≃ᵉ (((xᵉ : Xᵉ) → Aᵉ xᵉ) ×ᵉ ((xᵉ : Xᵉ) → Bᵉ xᵉ))
  pr1ᵉ equiv-up-productᵉ = map-up-productᵉ
  pr2ᵉ equiv-up-productᵉ = up-productᵉ

  inv-equiv-up-productᵉ :
    (((xᵉ : Xᵉ) → Aᵉ xᵉ) ×ᵉ ((xᵉ : Xᵉ) → Bᵉ xᵉ)) ≃ᵉ ((xᵉ : Xᵉ) → Aᵉ xᵉ ×ᵉ Bᵉ xᵉ)
  inv-equiv-up-productᵉ = inv-equivᵉ equiv-up-productᵉ
```

#### The universal property of cartesian products as pullbacks

Aᵉ differentᵉ wayᵉ to stateᵉ theᵉ universalᵉ propertyᵉ ofᵉ cartesianᵉ productsᵉ asᵉ limitsᵉ
isᵉ to sayᵉ thatᵉ theᵉ canonicalᵉ [cone](foundation.cones-over-cospan-diagrams.mdᵉ)
overᵉ theᵉ [terminalᵉ typeᵉ `unit`](foundation.unit-type.mdᵉ)

```text
           pr2ᵉ
   Aᵉ ×ᵉ Bᵉ ------>ᵉ Bᵉ
     |           |
 pr1ᵉ |           |
     ∨ᵉ           ∨ᵉ
     Aᵉ ------->ᵉ unitᵉ
```

isᵉ aᵉ [pullback](foundation-core.pullbacks.md).ᵉ Theᵉ
[universalᵉ propertyᵉ ofᵉ pullbacks](foundation-core.universal-property-pullbacks.mdᵉ)
statesᵉ in thisᵉ caseᵉ thatᵉ mapsᵉ intoᵉ `Aᵉ ×ᵉ B`ᵉ areᵉ in correspondenceᵉ with pairsᵉ ofᵉ
mapsᵉ intoᵉ `A`ᵉ andᵉ `B`ᵉ suchᵉ thatᵉ theᵉ squareᵉ

```text
     Xᵉ -------->ᵉ Bᵉ
     |           |
     |           |
     ∨ᵉ           ∨ᵉ
     Aᵉ ------->ᵉ unitᵉ
```

[commutes](foundation-core.commuting-squares-of-maps.md).ᵉ However,ᵉ allᵉ parallelᵉ
mapsᵉ intoᵉ theᵉ terminalᵉ typeᵉ areᵉ [equal](foundation-core.identity-types.md),ᵉ
henceᵉ theᵉ coherenceᵉ requirementᵉ isᵉ redundant.ᵉ

Weᵉ startᵉ byᵉ constructingᵉ theᵉ coneᵉ forᵉ twoᵉ mapsᵉ intoᵉ theᵉ unitᵉ type.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  cone-cartesian-productᵉ : coneᵉ (terminal-mapᵉ Aᵉ) (terminal-mapᵉ Bᵉ) (Aᵉ ×ᵉ Bᵉ)
  pr1ᵉ cone-cartesian-productᵉ = pr1ᵉ
  pr1ᵉ (pr2ᵉ cone-cartesian-productᵉ) = pr2ᵉ
  pr2ᵉ (pr2ᵉ cone-cartesian-productᵉ) = refl-htpyᵉ
```

Next,ᵉ weᵉ showᵉ thatᵉ cartesianᵉ productsᵉ areᵉ aᵉ specialᵉ caseᵉ ofᵉ pullbacks.ᵉ

```agda
  gap-cartesian-productᵉ :
    Aᵉ ×ᵉ Bᵉ → standard-pullbackᵉ (terminal-mapᵉ Aᵉ) (terminal-mapᵉ Bᵉ)
  gap-cartesian-productᵉ =
    gapᵉ (terminal-mapᵉ Aᵉ) (terminal-mapᵉ Bᵉ) cone-cartesian-productᵉ

  inv-gap-cartesian-productᵉ :
    standard-pullbackᵉ (terminal-mapᵉ Aᵉ) (terminal-mapᵉ Bᵉ) → Aᵉ ×ᵉ Bᵉ
  pr1ᵉ (inv-gap-cartesian-productᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ)) = aᵉ
  pr2ᵉ (inv-gap-cartesian-productᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ)) = bᵉ

  abstract
    is-section-inv-gap-cartesian-productᵉ :
      is-sectionᵉ gap-cartesian-productᵉ inv-gap-cartesian-productᵉ
    is-section-inv-gap-cartesian-productᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ) =
      map-extensionality-standard-pullbackᵉ
        ( terminal-mapᵉ Aᵉ)
        ( terminal-mapᵉ Bᵉ)
        ( reflᵉ)
        ( reflᵉ)
        ( eq-is-contrᵉ (is-prop-unitᵉ starᵉ starᵉ))

  is-retraction-inv-gap-cartesian-productᵉ :
    is-retractionᵉ gap-cartesian-productᵉ inv-gap-cartesian-productᵉ
  is-retraction-inv-gap-cartesian-productᵉ (aᵉ ,ᵉ bᵉ) = reflᵉ

  abstract
    is-pullback-cartesian-productᵉ :
      is-pullbackᵉ (terminal-mapᵉ Aᵉ) (terminal-mapᵉ Bᵉ) cone-cartesian-productᵉ
    is-pullback-cartesian-productᵉ =
      is-equiv-is-invertibleᵉ
        inv-gap-cartesian-productᵉ
        is-section-inv-gap-cartesian-productᵉ
        is-retraction-inv-gap-cartesian-productᵉ
```

Weᵉ concludeᵉ thatᵉ cartesianᵉ productsᵉ satisfyᵉ theᵉ universalᵉ propertyᵉ ofᵉ pullbacks.ᵉ

```agda
  abstract
    universal-property-pullback-cartesian-productᵉ :
      universal-property-pullbackᵉ
        ( terminal-mapᵉ Aᵉ)
        ( terminal-mapᵉ Bᵉ)
        ( cone-cartesian-productᵉ)
    universal-property-pullback-cartesian-productᵉ =
      universal-property-pullback-is-pullbackᵉ
        ( terminal-mapᵉ Aᵉ)
        ( terminal-mapᵉ Bᵉ)
        ( cone-cartesian-productᵉ)
        ( is-pullback-cartesian-productᵉ)
```

### The universal property of cartesian products as colimits

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ ×ᵉ Bᵉ → UUᵉ l3ᵉ}
  where

  equiv-ind-productᵉ : ((xᵉ : Aᵉ) (yᵉ : Bᵉ) → Cᵉ (xᵉ ,ᵉ yᵉ)) ≃ᵉ ((tᵉ : Aᵉ ×ᵉ Bᵉ) → Cᵉ tᵉ)
  equiv-ind-productᵉ = equiv-ind-Σᵉ
```