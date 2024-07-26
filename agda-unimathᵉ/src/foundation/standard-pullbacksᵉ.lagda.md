# Standard pullbacks

```agda
module foundation.standard-pullbacksᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.diagonal-maps-cartesian-products-of-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
open import foundation-core.universal-property-pullbacksᵉ
open import foundation-core.whiskering-identifications-concatenationᵉ
```

</details>

## Idea

Givenᵉ aᵉ [cospanᵉ ofᵉ types](foundation.cospans.mdᵉ)

```text
  fᵉ : Aᵉ → Xᵉ ←ᵉ Bᵉ : g,ᵉ
```

weᵉ canᵉ formᵉ theᵉ
{{#conceptᵉ "standardᵉ pullback"ᵉ Disambiguation="types"ᵉ Agda=standard-pullbackᵉ}}
`Aᵉ ×_Xᵉ B`ᵉ satisfyingᵉ
[theᵉ universalᵉ propertyᵉ ofᵉ theᵉ pullback](foundation-core.universal-property-pullbacks.mdᵉ)
ofᵉ theᵉ cospan,ᵉ completingᵉ theᵉ diagramᵉ

```text
  Aᵉ ×_Xᵉ Bᵉ ------>ᵉ Bᵉ
     | ⌟ᵉ          |
     |            | gᵉ
     |            |
     ∨ᵉ            ∨ᵉ
     Aᵉ --------->ᵉ X.ᵉ
           fᵉ
```

Theᵉ standardᵉ pullbackᵉ consistsᵉ ofᵉ [pairs](foundation.dependent-pair-types.mdᵉ)
`aᵉ : A`ᵉ andᵉ `bᵉ : B`ᵉ suchᵉ thatᵉ `fᵉ a`ᵉ andᵉ `gᵉ b`ᵉ agreeᵉ:

```text
  Aᵉ ×_Xᵉ Bᵉ :=ᵉ Σᵉ (aᵉ : Aᵉ) (bᵉ : B),ᵉ (fᵉ aᵉ ＝ᵉ gᵉ b),ᵉ
```

thusᵉ theᵉ standardᵉ [cone](foundation.cones-over-cospan-diagrams.mdᵉ) consistsᵉ ofᵉ
theᵉ canonicalᵉ projections.ᵉ

## Definitions

### The standard pullback of a cospan

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  standard-pullbackᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  standard-pullbackᵉ = Σᵉ Aᵉ (λ xᵉ → Σᵉ Bᵉ (λ yᵉ → fᵉ xᵉ ＝ᵉ gᵉ yᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {fᵉ : Aᵉ → Xᵉ} {gᵉ : Bᵉ → Xᵉ}
  where

  vertical-map-standard-pullbackᵉ : standard-pullbackᵉ fᵉ gᵉ → Aᵉ
  vertical-map-standard-pullbackᵉ = pr1ᵉ

  horizontal-map-standard-pullbackᵉ : standard-pullbackᵉ fᵉ gᵉ → Bᵉ
  horizontal-map-standard-pullbackᵉ tᵉ = pr1ᵉ (pr2ᵉ tᵉ)

  coherence-square-standard-pullbackᵉ :
    coherence-square-mapsᵉ
      ( horizontal-map-standard-pullbackᵉ)
      ( vertical-map-standard-pullbackᵉ)
      ( gᵉ)
      ( fᵉ)
  coherence-square-standard-pullbackᵉ tᵉ = pr2ᵉ (pr2ᵉ tᵉ)
```

### The cone at the standard pullback

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  cone-standard-pullbackᵉ : coneᵉ fᵉ gᵉ (standard-pullbackᵉ fᵉ gᵉ)
  pr1ᵉ cone-standard-pullbackᵉ = vertical-map-standard-pullbackᵉ
  pr1ᵉ (pr2ᵉ cone-standard-pullbackᵉ) = horizontal-map-standard-pullbackᵉ
  pr2ᵉ (pr2ᵉ cone-standard-pullbackᵉ) = coherence-square-standard-pullbackᵉ
```

### The gap map into the standard pullback

Theᵉ {{#conceptᵉ "standardᵉ gapᵉ map"ᵉ Disambiguation="coneᵉ overᵉ aᵉ cospan"ᵉ Agda=gapᵉ}}
ofᵉ aᵉ [commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ) isᵉ theᵉ mapᵉ
fromᵉ theᵉ domainᵉ ofᵉ theᵉ coneᵉ intoᵉ theᵉ standardᵉ pullback.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  gapᵉ : coneᵉ fᵉ gᵉ Cᵉ → Cᵉ → standard-pullbackᵉ fᵉ gᵉ
  pr1ᵉ (gapᵉ cᵉ zᵉ) = vertical-map-coneᵉ fᵉ gᵉ cᵉ zᵉ
  pr1ᵉ (pr2ᵉ (gapᵉ cᵉ zᵉ)) = horizontal-map-coneᵉ fᵉ gᵉ cᵉ zᵉ
  pr2ᵉ (pr2ᵉ (gapᵉ cᵉ zᵉ)) = coherence-square-coneᵉ fᵉ gᵉ cᵉ zᵉ
```

#### The standard ternary pullback

Givenᵉ twoᵉ cospansᵉ with aᵉ sharedᵉ vertexᵉ `B`ᵉ:

```text
      fᵉ       gᵉ       hᵉ       iᵉ
  Aᵉ ---->ᵉ Xᵉ <----ᵉ Bᵉ ---->ᵉ Yᵉ <----ᵉ C,ᵉ
```

weᵉ callᵉ theᵉ standardᵉ limitᵉ ofᵉ theᵉ diagramᵉ theᵉ
{{#conceptᵉ "standardᵉ ternaryᵉ pullback"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=standard-ternary-pullback}}.ᵉ
Itᵉ isᵉ definedᵉ asᵉ theᵉ sumᵉ

```text
  standard-ternary-pullbackᵉ fᵉ gᵉ hᵉ iᵉ :=ᵉ
    Σᵉ (aᵉ : Aᵉ) (bᵉ : Bᵉ) (cᵉ : C),ᵉ ((fᵉ aᵉ ＝ᵉ gᵉ bᵉ) ×ᵉ (hᵉ bᵉ ＝ᵉ iᵉ c)).ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} {Bᵉ : UUᵉ l4ᵉ} {Cᵉ : UUᵉ l5ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Bᵉ → Yᵉ) (iᵉ : Cᵉ → Yᵉ)
  where

  standard-ternary-pullbackᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  standard-ternary-pullbackᵉ =
    Σᵉ Aᵉ (λ aᵉ → Σᵉ Bᵉ (λ bᵉ → Σᵉ Cᵉ (λ cᵉ → (fᵉ aᵉ ＝ᵉ gᵉ bᵉ) ×ᵉ (hᵉ bᵉ ＝ᵉ iᵉ cᵉ))))
```

## Properties

### Characterization of the identity type of the standard pullback

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  Eq-standard-pullbackᵉ : (tᵉ t'ᵉ : standard-pullbackᵉ fᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  Eq-standard-pullbackᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ) (a'ᵉ ,ᵉ b'ᵉ ,ᵉ p'ᵉ) =
    Σᵉ (aᵉ ＝ᵉ a'ᵉ) (λ αᵉ → Σᵉ (bᵉ ＝ᵉ b'ᵉ) (λ βᵉ → apᵉ fᵉ αᵉ ∙ᵉ p'ᵉ ＝ᵉ pᵉ ∙ᵉ apᵉ gᵉ βᵉ))

  refl-Eq-standard-pullbackᵉ :
    (tᵉ : standard-pullbackᵉ fᵉ gᵉ) → Eq-standard-pullbackᵉ tᵉ tᵉ
  pr1ᵉ (refl-Eq-standard-pullbackᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ)) = reflᵉ
  pr1ᵉ (pr2ᵉ (refl-Eq-standard-pullbackᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ))) = reflᵉ
  pr2ᵉ (pr2ᵉ (refl-Eq-standard-pullbackᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ))) = invᵉ right-unitᵉ

  Eq-eq-standard-pullbackᵉ :
    (sᵉ tᵉ : standard-pullbackᵉ fᵉ gᵉ) → sᵉ ＝ᵉ tᵉ → Eq-standard-pullbackᵉ sᵉ tᵉ
  Eq-eq-standard-pullbackᵉ sᵉ .sᵉ reflᵉ = refl-Eq-standard-pullbackᵉ sᵉ

  extensionality-standard-pullbackᵉ :
    (tᵉ t'ᵉ : standard-pullbackᵉ fᵉ gᵉ) → (tᵉ ＝ᵉ t'ᵉ) ≃ᵉ Eq-standard-pullbackᵉ tᵉ t'ᵉ
  extensionality-standard-pullbackᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ) =
    extensionality-Σᵉ
      ( λ bp'ᵉ αᵉ → Σᵉ (bᵉ ＝ᵉ pr1ᵉ bp'ᵉ) (λ βᵉ → apᵉ fᵉ αᵉ ∙ᵉ pr2ᵉ bp'ᵉ ＝ᵉ pᵉ ∙ᵉ apᵉ gᵉ βᵉ))
      ( reflᵉ)
      ( reflᵉ ,ᵉ invᵉ right-unitᵉ)
      ( λ xᵉ → id-equivᵉ)
      ( extensionality-Σᵉ
        ( λ p'ᵉ βᵉ → p'ᵉ ＝ᵉ pᵉ ∙ᵉ apᵉ gᵉ βᵉ)
        ( reflᵉ)
        ( invᵉ right-unitᵉ)
        ( λ yᵉ → id-equivᵉ)
        ( λ p'ᵉ → equiv-concat'ᵉ p'ᵉ (invᵉ right-unitᵉ) ∘eᵉ equiv-invᵉ pᵉ p'ᵉ))

  map-extensionality-standard-pullbackᵉ :
    { sᵉ tᵉ : standard-pullbackᵉ fᵉ gᵉ}
    ( αᵉ : vertical-map-standard-pullbackᵉ sᵉ ＝ᵉ vertical-map-standard-pullbackᵉ tᵉ)
    ( βᵉ :
      horizontal-map-standard-pullbackᵉ sᵉ ＝ᵉ
      horizontal-map-standard-pullbackᵉ tᵉ) →
    ( ( apᵉ fᵉ αᵉ ∙ᵉ coherence-square-standard-pullbackᵉ tᵉ) ＝ᵉ
      ( coherence-square-standard-pullbackᵉ sᵉ ∙ᵉ apᵉ gᵉ βᵉ)) →
    sᵉ ＝ᵉ tᵉ
  map-extensionality-standard-pullbackᵉ {sᵉ} {tᵉ} αᵉ βᵉ γᵉ =
    map-inv-equivᵉ (extensionality-standard-pullbackᵉ sᵉ tᵉ) (αᵉ ,ᵉ βᵉ ,ᵉ γᵉ)
```

### The standard pullback satisfies the universal property of pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  abstract
    universal-property-standard-pullbackᵉ :
      universal-property-pullbackᵉ fᵉ gᵉ (cone-standard-pullbackᵉ fᵉ gᵉ)
    universal-property-standard-pullbackᵉ Cᵉ =
      is-equiv-compᵉ
        ( totᵉ (λ _ → map-distributive-Π-Σᵉ))
        ( mapping-into-Σᵉ)
        ( is-equiv-mapping-into-Σᵉ)
        ( is-equiv-tot-is-fiberwise-equivᵉ (λ _ → is-equiv-map-distributive-Π-Σᵉ))
```

### A cone is equal to the value of `cone-map` at its own gap map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  htpy-cone-up-pullback-standard-pullbackᵉ :
    (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
    htpy-coneᵉ fᵉ gᵉ (cone-mapᵉ fᵉ gᵉ (cone-standard-pullbackᵉ fᵉ gᵉ) (gapᵉ fᵉ gᵉ cᵉ)) cᵉ
  pr1ᵉ (htpy-cone-up-pullback-standard-pullbackᵉ cᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ (htpy-cone-up-pullback-standard-pullbackᵉ cᵉ)) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (htpy-cone-up-pullback-standard-pullbackᵉ cᵉ)) = right-unit-htpyᵉ
```

### Standard pullbacks are symmetric

Theᵉ standardᵉ pullbackᵉ ofᵉ `fᵉ : Aᵉ ->ᵉ Xᵉ <-ᵉ Bᵉ : g`ᵉ isᵉ equivalentᵉ to theᵉ standardᵉ
pullbackᵉ ofᵉ `gᵉ : Bᵉ ->ᵉ Xᵉ <-ᵉ Aᵉ : f`.ᵉ

```agda
map-commutative-standard-pullbackᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) → standard-pullbackᵉ fᵉ gᵉ → standard-pullbackᵉ gᵉ fᵉ
pr1ᵉ (map-commutative-standard-pullbackᵉ fᵉ gᵉ xᵉ) =
  horizontal-map-standard-pullbackᵉ xᵉ
pr1ᵉ (pr2ᵉ (map-commutative-standard-pullbackᵉ fᵉ gᵉ xᵉ)) =
  vertical-map-standard-pullbackᵉ xᵉ
pr2ᵉ (pr2ᵉ (map-commutative-standard-pullbackᵉ fᵉ gᵉ xᵉ)) =
  invᵉ (coherence-square-standard-pullbackᵉ xᵉ)

inv-inv-map-commutative-standard-pullbackᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) →
  ( map-commutative-standard-pullbackᵉ fᵉ gᵉ ∘ᵉ
    map-commutative-standard-pullbackᵉ gᵉ fᵉ) ~ᵉ idᵉ
inv-inv-map-commutative-standard-pullbackᵉ fᵉ gᵉ xᵉ =
  eq-pair-eq-fiberᵉ
    ( eq-pair-eq-fiberᵉ
      ( inv-invᵉ (coherence-square-standard-pullbackᵉ xᵉ)))

abstract
  is-equiv-map-commutative-standard-pullbackᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) → is-equivᵉ (map-commutative-standard-pullbackᵉ fᵉ gᵉ)
  is-equiv-map-commutative-standard-pullbackᵉ fᵉ gᵉ =
    is-equiv-is-invertibleᵉ
      ( map-commutative-standard-pullbackᵉ gᵉ fᵉ)
      ( inv-inv-map-commutative-standard-pullbackᵉ fᵉ gᵉ)
      ( inv-inv-map-commutative-standard-pullbackᵉ gᵉ fᵉ)

commutative-standard-pullbackᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) →
  standard-pullbackᵉ fᵉ gᵉ ≃ᵉ standard-pullbackᵉ gᵉ fᵉ
pr1ᵉ (commutative-standard-pullbackᵉ fᵉ gᵉ) =
  map-commutative-standard-pullbackᵉ fᵉ gᵉ
pr2ᵉ (commutative-standard-pullbackᵉ fᵉ gᵉ) =
  is-equiv-map-commutative-standard-pullbackᵉ fᵉ gᵉ
```

#### The gap map of the swapped cone computes as the underlying gap map followed by a swap

```agda
triangle-map-commutative-standard-pullbackᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
  gapᵉ gᵉ fᵉ (swap-coneᵉ fᵉ gᵉ cᵉ) ~ᵉ
  map-commutative-standard-pullbackᵉ fᵉ gᵉ ∘ᵉ gapᵉ fᵉ gᵉ cᵉ
triangle-map-commutative-standard-pullbackᵉ fᵉ gᵉ cᵉ = refl-htpyᵉ
```

### Standard pullbacks are associative

Considerᵉ twoᵉ cospansᵉ with aᵉ sharedᵉ vertexᵉ `B`ᵉ:

```text
      fᵉ       gᵉ       hᵉ       iᵉ
  Aᵉ ---->ᵉ Xᵉ <----ᵉ Bᵉ ---->ᵉ Yᵉ <----ᵉ C,ᵉ
```

thenᵉ weᵉ canᵉ constructᵉ theirᵉ limitᵉ using standardᵉ pullbacksᵉ in twoᵉ equivalentᵉ
ways.ᵉ Weᵉ canᵉ constructᵉ itᵉ byᵉ firstᵉ formingᵉ theᵉ standardᵉ pullbackᵉ ofᵉ `f`ᵉ andᵉ `g`,ᵉ
andᵉ thenᵉ formingᵉ theᵉ standardᵉ pullbackᵉ ofᵉ theᵉ resultingᵉ `hᵉ ∘ᵉ f'`ᵉ andᵉ `i`ᵉ

```text
  (Aᵉ ×_Xᵉ Bᵉ) ×_Yᵉ Cᵉ --------------------->ᵉ Cᵉ
         | ⌟ᵉ                             |
         |                               | iᵉ
         ∨ᵉ                               ∨ᵉ
      Aᵉ ×_Xᵉ Bᵉ --------->ᵉ Bᵉ ------------>ᵉ Yᵉ
         | ⌟ᵉ     f'ᵉ      |       hᵉ
         |               | gᵉ
         ∨ᵉ               ∨ᵉ
         Aᵉ ------------>ᵉ X,ᵉ
                 fᵉ
```

orᵉ weᵉ canᵉ firstᵉ formᵉ theᵉ pullbackᵉ ofᵉ `h`ᵉ andᵉ `i`,ᵉ andᵉ thenᵉ formᵉ theᵉ pullbackᵉ ofᵉ
`f`ᵉ andᵉ theᵉ resultingᵉ `gᵉ ∘ᵉ i'`ᵉ:

```text
  Aᵉ ×_Xᵉ (Bᵉ ×_Yᵉ Cᵉ) -->ᵉ Bᵉ ×_Yᵉ Cᵉ --------->ᵉ Cᵉ
         | ⌟ᵉ             | ⌟ᵉ             |
         |               | i'ᵉ            | iᵉ
         |               ∨ᵉ               ∨ᵉ
         |               Bᵉ ------------>ᵉ Yᵉ
         |               |       hᵉ
         |               | gᵉ
         ∨ᵉ               ∨ᵉ
         Aᵉ ------------>ᵉ X.ᵉ
                 fᵉ
```

Weᵉ showᵉ thatᵉ bothᵉ ofᵉ theseᵉ constructionsᵉ areᵉ equivalentᵉ byᵉ showingᵉ theyᵉ areᵉ
equivalentᵉ to theᵉ standardᵉ ternaryᵉ pullback.ᵉ

**Note:**ᵉ Associativityᵉ with respectᵉ to ternaryᵉ cospansᵉ

```text
              Bᵉ
              |
              | gᵉ
              ∨ᵉ
    Aᵉ ------>ᵉ Xᵉ <------ᵉ Cᵉ
         fᵉ         hᵉ
```

isᵉ aᵉ specialᵉ caseᵉ ofᵉ whatᵉ weᵉ considerᵉ hereᵉ thatᵉ isᵉ recoveredᵉ byᵉ using

```text
      fᵉ       gᵉ       gᵉ       hᵉ
  Aᵉ ---->ᵉ Xᵉ <----ᵉ Bᵉ ---->ᵉ Xᵉ <----ᵉ C.ᵉ
```

-ᵉ Seeᵉ alsoᵉ theᵉ followingᵉ relevantᵉ stackᵉ exchangeᵉ questionᵉ:
  [Associativityᵉ ofᵉ pullbacks](https://math.stackexchange.com/questions/2046276/associativity-of-pullbacks).ᵉ

#### Computing the left associated iterated standard pullback

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} {Bᵉ : UUᵉ l4ᵉ} {Cᵉ : UUᵉ l5ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Bᵉ → Yᵉ) (iᵉ : Cᵉ → Yᵉ)
  where

  map-left-associative-standard-pullbackᵉ :
    standard-pullbackᵉ (hᵉ ∘ᵉ horizontal-map-standard-pullbackᵉ {fᵉ = fᵉ} {gᵉ = gᵉ}) iᵉ →
    standard-ternary-pullbackᵉ fᵉ gᵉ hᵉ iᵉ
  map-left-associative-standard-pullbackᵉ ((aᵉ ,ᵉ bᵉ ,ᵉ pᵉ) ,ᵉ cᵉ ,ᵉ qᵉ) =
    ( aᵉ ,ᵉ bᵉ ,ᵉ cᵉ ,ᵉ pᵉ ,ᵉ qᵉ)

  map-inv-left-associative-standard-pullbackᵉ :
    standard-ternary-pullbackᵉ fᵉ gᵉ hᵉ iᵉ →
    standard-pullbackᵉ (hᵉ ∘ᵉ horizontal-map-standard-pullbackᵉ {fᵉ = fᵉ} {gᵉ = gᵉ}) iᵉ
  map-inv-left-associative-standard-pullbackᵉ (aᵉ ,ᵉ bᵉ ,ᵉ cᵉ ,ᵉ pᵉ ,ᵉ qᵉ) =
    ( ( aᵉ ,ᵉ bᵉ ,ᵉ pᵉ) ,ᵉ cᵉ ,ᵉ qᵉ)

  is-equiv-map-left-associative-standard-pullbackᵉ :
    is-equivᵉ map-left-associative-standard-pullbackᵉ
  is-equiv-map-left-associative-standard-pullbackᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-left-associative-standard-pullbackᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)

  compute-left-associative-standard-pullbackᵉ :
    standard-pullbackᵉ (hᵉ ∘ᵉ horizontal-map-standard-pullbackᵉ {fᵉ = fᵉ} {gᵉ = gᵉ}) iᵉ ≃ᵉ
    standard-ternary-pullbackᵉ fᵉ gᵉ hᵉ iᵉ
  compute-left-associative-standard-pullbackᵉ =
    ( map-left-associative-standard-pullbackᵉ ,ᵉ
      is-equiv-map-left-associative-standard-pullbackᵉ)
```

#### Computing the right associated iterated dependent pullback

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} {Bᵉ : UUᵉ l4ᵉ} {Cᵉ : UUᵉ l5ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Bᵉ → Yᵉ) (iᵉ : Cᵉ → Yᵉ)
  where

  map-right-associative-standard-pullbackᵉ :
    standard-pullbackᵉ fᵉ (gᵉ ∘ᵉ vertical-map-standard-pullbackᵉ {fᵉ = hᵉ} {gᵉ = iᵉ}) →
    standard-ternary-pullbackᵉ fᵉ gᵉ hᵉ iᵉ
  map-right-associative-standard-pullbackᵉ (aᵉ ,ᵉ (bᵉ ,ᵉ cᵉ ,ᵉ pᵉ) ,ᵉ qᵉ) =
    ( aᵉ ,ᵉ bᵉ ,ᵉ cᵉ ,ᵉ qᵉ ,ᵉ pᵉ)

  map-inv-right-associative-standard-pullbackᵉ :
    standard-ternary-pullbackᵉ fᵉ gᵉ hᵉ iᵉ →
    standard-pullbackᵉ fᵉ (gᵉ ∘ᵉ vertical-map-standard-pullbackᵉ {fᵉ = hᵉ} {gᵉ = iᵉ})
  map-inv-right-associative-standard-pullbackᵉ (aᵉ ,ᵉ bᵉ ,ᵉ cᵉ ,ᵉ pᵉ ,ᵉ qᵉ) =
    ( aᵉ ,ᵉ (bᵉ ,ᵉ cᵉ ,ᵉ qᵉ) ,ᵉ pᵉ)

  is-equiv-map-right-associative-standard-pullbackᵉ :
    is-equivᵉ map-right-associative-standard-pullbackᵉ
  is-equiv-map-right-associative-standard-pullbackᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-right-associative-standard-pullbackᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)

  compute-right-associative-standard-pullbackᵉ :
    standard-pullbackᵉ fᵉ (gᵉ ∘ᵉ vertical-map-standard-pullbackᵉ {fᵉ = hᵉ} {gᵉ = iᵉ}) ≃ᵉ
    standard-ternary-pullbackᵉ fᵉ gᵉ hᵉ iᵉ
  compute-right-associative-standard-pullbackᵉ =
    ( map-right-associative-standard-pullbackᵉ ,ᵉ
      is-equiv-map-right-associative-standard-pullbackᵉ)
```

#### Standard pullbacks are associative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} {Bᵉ : UUᵉ l4ᵉ} {Cᵉ : UUᵉ l5ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Bᵉ → Yᵉ) (iᵉ : Cᵉ → Yᵉ)
  where

  associative-standard-pullbackᵉ :
    standard-pullbackᵉ (hᵉ ∘ᵉ horizontal-map-standard-pullbackᵉ {fᵉ = fᵉ} {gᵉ = gᵉ}) iᵉ ≃ᵉ
    standard-pullbackᵉ fᵉ (gᵉ ∘ᵉ vertical-map-standard-pullbackᵉ {fᵉ = hᵉ} {gᵉ = iᵉ})
  associative-standard-pullbackᵉ =
    ( inv-equivᵉ (compute-right-associative-standard-pullbackᵉ fᵉ gᵉ hᵉ iᵉ)) ∘eᵉ
    ( compute-left-associative-standard-pullbackᵉ fᵉ gᵉ hᵉ iᵉ)

  map-associative-standard-pullbackᵉ :
    standard-pullbackᵉ (hᵉ ∘ᵉ horizontal-map-standard-pullbackᵉ {fᵉ = fᵉ} {gᵉ = gᵉ}) iᵉ →
    standard-pullbackᵉ fᵉ (gᵉ ∘ᵉ vertical-map-standard-pullbackᵉ {fᵉ = hᵉ} {gᵉ = iᵉ})
  map-associative-standard-pullbackᵉ = map-equivᵉ associative-standard-pullbackᵉ

  map-inv-associative-standard-pullbackᵉ :
    standard-pullbackᵉ fᵉ (gᵉ ∘ᵉ vertical-map-standard-pullbackᵉ {fᵉ = hᵉ} {gᵉ = iᵉ}) →
    standard-pullbackᵉ (hᵉ ∘ᵉ horizontal-map-standard-pullbackᵉ {fᵉ = fᵉ} {gᵉ = gᵉ}) iᵉ
  map-inv-associative-standard-pullbackᵉ =
    map-inv-equivᵉ associative-standard-pullbackᵉ
```

### Pullbacks can be "folded"

Givenᵉ aᵉ standardᵉ pullbackᵉ squareᵉ

```text
         f'ᵉ
    Cᵉ ------->ᵉ Bᵉ
    | ⌟ᵉ        |
  g'|ᵉ          | gᵉ
    ∨ᵉ          ∨ᵉ
    Aᵉ ------->ᵉ Xᵉ
         fᵉ
```

weᵉ canᵉ "fold"ᵉ theᵉ verticalᵉ edgeᵉ ontoᵉ theᵉ horizontalᵉ oneᵉ andᵉ getᵉ aᵉ newᵉ pullbackᵉ
squareᵉ

```text
            Cᵉ --------->ᵉ Xᵉ
            | ⌟ᵉ          |
  (f'ᵉ ,ᵉ g'ᵉ) |            |
            ∨ᵉ            ∨ᵉ
          Aᵉ ×ᵉ Bᵉ ----->ᵉ Xᵉ ×ᵉ X,ᵉ
                fᵉ ×ᵉ gᵉ
```

moreover,ᵉ thisᵉ foldedᵉ squareᵉ isᵉ aᵉ pullbackᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ originalᵉ oneᵉ is.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  fold-coneᵉ :
    {l4ᵉ : Level} {Cᵉ : UUᵉ l4ᵉ} →
    coneᵉ fᵉ gᵉ Cᵉ → coneᵉ (map-productᵉ fᵉ gᵉ) (diagonal-productᵉ Xᵉ) Cᵉ
  pr1ᵉ (pr1ᵉ (fold-coneᵉ cᵉ) zᵉ) = vertical-map-coneᵉ fᵉ gᵉ cᵉ zᵉ
  pr2ᵉ (pr1ᵉ (fold-coneᵉ cᵉ) zᵉ) = horizontal-map-coneᵉ fᵉ gᵉ cᵉ zᵉ
  pr1ᵉ (pr2ᵉ (fold-coneᵉ cᵉ)) = gᵉ ∘ᵉ horizontal-map-coneᵉ fᵉ gᵉ cᵉ
  pr2ᵉ (pr2ᵉ (fold-coneᵉ cᵉ)) zᵉ = eq-pairᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ zᵉ) reflᵉ

  map-fold-cone-standard-pullbackᵉ :
    standard-pullbackᵉ fᵉ gᵉ →
    standard-pullbackᵉ (map-productᵉ fᵉ gᵉ) (diagonal-productᵉ Xᵉ)
  pr1ᵉ (pr1ᵉ (map-fold-cone-standard-pullbackᵉ xᵉ)) =
    vertical-map-standard-pullbackᵉ xᵉ
  pr2ᵉ (pr1ᵉ (map-fold-cone-standard-pullbackᵉ xᵉ)) =
    horizontal-map-standard-pullbackᵉ xᵉ
  pr1ᵉ (pr2ᵉ (map-fold-cone-standard-pullbackᵉ xᵉ)) =
    gᵉ (horizontal-map-standard-pullbackᵉ xᵉ)
  pr2ᵉ (pr2ᵉ (map-fold-cone-standard-pullbackᵉ xᵉ)) =
    eq-pairᵉ (coherence-square-standard-pullbackᵉ xᵉ) reflᵉ

  map-inv-fold-cone-standard-pullbackᵉ :
    standard-pullbackᵉ (map-productᵉ fᵉ gᵉ) (diagonal-productᵉ Xᵉ) →
    standard-pullbackᵉ fᵉ gᵉ
  pr1ᵉ (map-inv-fold-cone-standard-pullbackᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ xᵉ ,ᵉ αᵉ)) = aᵉ
  pr1ᵉ (pr2ᵉ (map-inv-fold-cone-standard-pullbackᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ xᵉ ,ᵉ αᵉ))) = bᵉ
  pr2ᵉ (pr2ᵉ (map-inv-fold-cone-standard-pullbackᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ xᵉ ,ᵉ αᵉ))) =
    apᵉ pr1ᵉ αᵉ ∙ᵉ invᵉ (apᵉ pr2ᵉ αᵉ)

  abstract
    is-section-map-inv-fold-cone-standard-pullbackᵉ :
      is-sectionᵉ
        ( map-fold-cone-standard-pullbackᵉ)
        ( map-inv-fold-cone-standard-pullbackᵉ)
    is-section-map-inv-fold-cone-standard-pullbackᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ (xᵉ ,ᵉ αᵉ)) =
      map-extensionality-standard-pullbackᵉ
        ( map-productᵉ fᵉ gᵉ)
        ( diagonal-productᵉ Xᵉ)
        ( reflᵉ)
        ( apᵉ pr2ᵉ αᵉ)
        ( ( invᵉ (is-section-pair-eqᵉ αᵉ)) ∙ᵉ
          ( apᵉ
            ( λ tᵉ → eq-pairᵉ tᵉ (apᵉ pr2ᵉ αᵉ))
            ( ( invᵉ right-unitᵉ) ∙ᵉ
              ( invᵉ
                ( left-whisker-concatᵉ
                  ( apᵉ pr1ᵉ αᵉ)
                  ( left-invᵉ (apᵉ pr2ᵉ αᵉ)))) ∙ᵉ
              ( invᵉ (assocᵉ (apᵉ pr1ᵉ αᵉ) (invᵉ (apᵉ pr2ᵉ αᵉ)) (apᵉ pr2ᵉ αᵉ))))) ∙ᵉ
          ( eq-pair-concatᵉ
            ( apᵉ pr1ᵉ αᵉ ∙ᵉ invᵉ (apᵉ pr2ᵉ αᵉ))
            ( apᵉ pr2ᵉ αᵉ)
            ( reflᵉ)
            ( apᵉ pr2ᵉ αᵉ)) ∙ᵉ
          ( apᵉ
            ( concatᵉ (eq-pairᵉ (apᵉ pr1ᵉ αᵉ ∙ᵉ invᵉ (apᵉ pr2ᵉ αᵉ)) reflᵉ) (xᵉ ,ᵉ xᵉ))
            ( invᵉ (compute-ap-diagonal-productᵉ (apᵉ pr2ᵉ αᵉ)))))

  abstract
    is-retraction-map-inv-fold-cone-standard-pullbackᵉ :
      is-retractionᵉ
        ( map-fold-cone-standard-pullbackᵉ)
        ( map-inv-fold-cone-standard-pullbackᵉ)
    is-retraction-map-inv-fold-cone-standard-pullbackᵉ (aᵉ ,ᵉ bᵉ ,ᵉ pᵉ) =
      map-extensionality-standard-pullbackᵉ fᵉ gᵉ
        ( reflᵉ)
        ( reflᵉ)
        ( invᵉ
          ( ( right-whisker-concatᵉ
              ( ( right-whisker-concatᵉ
                  ( ap-pr1-eq-pairᵉ pᵉ reflᵉ)
                  ( invᵉ (apᵉ pr2ᵉ (eq-pairᵉ pᵉ reflᵉ)))) ∙ᵉ
                ( apᵉ (λ tᵉ → pᵉ ∙ᵉ invᵉ tᵉ) (ap-pr2-eq-pairᵉ pᵉ reflᵉ)) ∙ᵉ
                ( right-unitᵉ))
              ( reflᵉ)) ∙ᵉ
            ( right-unitᵉ)))

  abstract
    is-equiv-map-fold-cone-standard-pullbackᵉ :
      is-equivᵉ map-fold-cone-standard-pullbackᵉ
    is-equiv-map-fold-cone-standard-pullbackᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-fold-cone-standard-pullbackᵉ)
        ( is-section-map-inv-fold-cone-standard-pullbackᵉ)
        ( is-retraction-map-inv-fold-cone-standard-pullbackᵉ)

  compute-fold-standard-pullbackᵉ :
    standard-pullbackᵉ fᵉ gᵉ ≃ᵉ
    standard-pullbackᵉ (map-productᵉ fᵉ gᵉ) (diagonal-productᵉ Xᵉ)
  compute-fold-standard-pullbackᵉ =
    map-fold-cone-standard-pullbackᵉ ,ᵉ is-equiv-map-fold-cone-standard-pullbackᵉ

  triangle-map-fold-cone-standard-pullbackᵉ :
    {l4ᵉ : Level} {Cᵉ : UUᵉ l4ᵉ} (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
    gapᵉ (map-productᵉ fᵉ gᵉ) (diagonal-productᵉ Xᵉ) (fold-coneᵉ cᵉ) ~ᵉ
    map-fold-cone-standard-pullbackᵉ ∘ᵉ gapᵉ fᵉ gᵉ cᵉ
  triangle-map-fold-cone-standard-pullbackᵉ cᵉ = refl-htpyᵉ
```

### The equivalence on standard pullbacks induced by parallel cospans

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  {fᵉ f'ᵉ : Aᵉ → Xᵉ} (Hfᵉ : fᵉ ~ᵉ f'ᵉ) {gᵉ g'ᵉ : Bᵉ → Xᵉ} (Hgᵉ : gᵉ ~ᵉ g'ᵉ)
  where

  map-equiv-standard-pullback-htpyᵉ :
    standard-pullbackᵉ f'ᵉ g'ᵉ → standard-pullbackᵉ fᵉ gᵉ
  map-equiv-standard-pullback-htpyᵉ =
    totᵉ (λ aᵉ → totᵉ (λ bᵉ → concat'ᵉ (fᵉ aᵉ) (invᵉ (Hgᵉ bᵉ)) ∘ᵉ concatᵉ (Hfᵉ aᵉ) (g'ᵉ bᵉ)))

  abstract
    is-equiv-map-equiv-standard-pullback-htpyᵉ :
      is-equivᵉ map-equiv-standard-pullback-htpyᵉ
    is-equiv-map-equiv-standard-pullback-htpyᵉ =
      is-equiv-tot-is-fiberwise-equivᵉ
        ( λ aᵉ →
          is-equiv-tot-is-fiberwise-equivᵉ
            ( λ bᵉ →
              is-equiv-compᵉ
                ( concat'ᵉ (fᵉ aᵉ) (invᵉ (Hgᵉ bᵉ)))
                ( concatᵉ (Hfᵉ aᵉ) (g'ᵉ bᵉ))
                ( is-equiv-concatᵉ (Hfᵉ aᵉ) (g'ᵉ bᵉ))
                ( is-equiv-concat'ᵉ (fᵉ aᵉ) (invᵉ (Hgᵉ bᵉ)))))

  equiv-standard-pullback-htpyᵉ :
    standard-pullbackᵉ f'ᵉ g'ᵉ ≃ᵉ standard-pullbackᵉ fᵉ gᵉ
  pr1ᵉ equiv-standard-pullback-htpyᵉ = map-equiv-standard-pullback-htpyᵉ
  pr2ᵉ equiv-standard-pullback-htpyᵉ = is-equiv-map-equiv-standard-pullback-htpyᵉ
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}