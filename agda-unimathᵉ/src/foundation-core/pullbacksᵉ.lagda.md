# Pullbacks

```agda
module foundation-core.pullbacksᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-fibers-of-mapsᵉ
open import foundation.identity-typesᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.diagonal-maps-cartesian-products-of-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.families-of-equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.universal-property-pullbacksᵉ
```

</details>

## Idea

Considerᵉ aᵉ [cone](foundation.cones-over-cospan-diagrams.mdᵉ) overᵉ aᵉ
[cospanᵉ diagramᵉ ofᵉ types](foundation.cospan-diagrams.mdᵉ) `fᵉ : Aᵉ ->ᵉ Xᵉ <-ᵉ Bᵉ : g,`ᵉ

```text
  Cᵉ ------>ᵉ Bᵉ
  |         |
  |         | gᵉ
  ∨ᵉ         ∨ᵉ
  Aᵉ ------>ᵉ X.ᵉ
       fᵉ
```

weᵉ wantᵉ to poseᵉ theᵉ questionᵉ ofᵉ whetherᵉ thisᵉ coneᵉ isᵉ aᵉ
{{#conceptᵉ "pullbackᵉ cone"ᵉ Disambiguation="types"ᵉ Agda=is-pullback}}.ᵉ Althoughᵉ
thisᵉ conceptᵉ isᵉ capturedᵉ byᵉ
[theᵉ universalᵉ propertyᵉ ofᵉ theᵉ pullback](foundation-core.universal-property-pullbacks.md),ᵉ
thatᵉ isᵉ aᵉ largeᵉ proposition,ᵉ whichᵉ isᵉ notᵉ suitableᵉ forᵉ allᵉ purposes.ᵉ Therefore,ᵉ
asᵉ ourᵉ mainᵉ definitionᵉ ofᵉ aᵉ pullbackᵉ coneᵉ weᵉ considerᵉ theᵉ
{{#conceptᵉ "smallᵉ predicateᵉ ofᵉ beingᵉ aᵉ pullback"ᵉ Agda=is-pullbackᵉ}}: givenᵉ theᵉ
existenceᵉ ofᵉ theᵉ [standardᵉ pullbackᵉ type](foundation.standard-pullbacks.mdᵉ)
`Aᵉ ×_Xᵉ B`,ᵉ aᵉ coneᵉ isᵉ aᵉ _pullbackᵉ_ ifᵉ theᵉ gapᵉ mapᵉ intoᵉ theᵉ standardᵉ pullbackᵉ isᵉ
anᵉ [equivalence](foundation-core.equivalences.md).ᵉ

## Definitions

### The small property of being a pullback

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  is-pullbackᵉ : coneᵉ fᵉ gᵉ Cᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-pullbackᵉ cᵉ = is-equivᵉ (gapᵉ fᵉ gᵉ cᵉ)
```

### A cone is a pullback if and only if it satisfies the universal property

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  abstract
    is-pullback-universal-property-pullbackᵉ :
      (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) → universal-property-pullbackᵉ fᵉ gᵉ cᵉ → is-pullbackᵉ fᵉ gᵉ cᵉ
    is-pullback-universal-property-pullbackᵉ cᵉ =
      is-equiv-up-pullback-up-pullbackᵉ
        ( cone-standard-pullbackᵉ fᵉ gᵉ)
        ( cᵉ)
        ( gapᵉ fᵉ gᵉ cᵉ)
        ( htpy-cone-up-pullback-standard-pullbackᵉ fᵉ gᵉ cᵉ)
        ( universal-property-standard-pullbackᵉ fᵉ gᵉ)

  abstract
    universal-property-pullback-is-pullbackᵉ :
      (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) → is-pullbackᵉ fᵉ gᵉ cᵉ →
      universal-property-pullbackᵉ fᵉ gᵉ cᵉ
    universal-property-pullback-is-pullbackᵉ cᵉ is-pullback-cᵉ =
      up-pullback-up-pullback-is-equivᵉ
        ( cone-standard-pullbackᵉ fᵉ gᵉ)
        ( cᵉ)
        ( gapᵉ fᵉ gᵉ cᵉ)
        ( htpy-cone-up-pullback-standard-pullbackᵉ fᵉ gᵉ cᵉ)
        ( is-pullback-cᵉ)
        ( universal-property-standard-pullbackᵉ fᵉ gᵉ)
```

### The gap map into a pullback

Theᵉ
{{#conceptᵉ "gapᵉ map"ᵉ Disambiguation="coneᵉ overᵉ aᵉ cospan"ᵉ Agda=gap-is-pullbackᵉ}}
ofᵉ aᵉ [commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ) isᵉ theᵉ mapᵉ
fromᵉ theᵉ domainᵉ ofᵉ theᵉ coneᵉ intoᵉ theᵉ pullback.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (Hᵉ : is-pullbackᵉ fᵉ gᵉ cᵉ)
  where

  gap-is-pullbackᵉ : {l5ᵉ : Level} {C'ᵉ : UUᵉ l5ᵉ} → coneᵉ fᵉ gᵉ C'ᵉ → C'ᵉ → Cᵉ
  gap-is-pullbackᵉ =
    map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ
      ( universal-property-pullback-is-pullbackᵉ fᵉ gᵉ cᵉ Hᵉ)

  compute-gap-is-pullbackᵉ :
    {l5ᵉ : Level} {C'ᵉ : UUᵉ l5ᵉ} (c'ᵉ : coneᵉ fᵉ gᵉ C'ᵉ) →
    cone-mapᵉ fᵉ gᵉ cᵉ (gap-is-pullbackᵉ c'ᵉ) ＝ᵉ c'ᵉ
  compute-gap-is-pullbackᵉ =
    compute-map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ
      ( universal-property-pullback-is-pullbackᵉ fᵉ gᵉ cᵉ Hᵉ)
```

### The homotopy of cones obtained from the universal property of pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) {Cᵉ : UUᵉ l4ᵉ}
  (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (upᵉ : is-pullbackᵉ fᵉ gᵉ cᵉ)
  {l5ᵉ : Level} {C'ᵉ : UUᵉ l5ᵉ} (c'ᵉ : coneᵉ fᵉ gᵉ C'ᵉ)
  where

  htpy-cone-gap-is-pullbackᵉ :
    htpy-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (gap-is-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
  htpy-cone-gap-is-pullbackᵉ =
    htpy-eq-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (gap-is-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
      ( compute-gap-is-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ)

  htpy-vertical-map-gap-is-pullbackᵉ :
    vertical-map-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (gap-is-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ)) ~ᵉ
      vertical-map-coneᵉ fᵉ gᵉ c'ᵉ
  htpy-vertical-map-gap-is-pullbackᵉ =
    htpy-vertical-map-htpy-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (gap-is-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
      ( htpy-cone-gap-is-pullbackᵉ)

  htpy-horizontal-map-gap-is-pullbackᵉ :
    horizontal-map-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (gap-is-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ)) ~ᵉ
      horizontal-map-coneᵉ fᵉ gᵉ c'ᵉ
  htpy-horizontal-map-gap-is-pullbackᵉ =
    htpy-horizontal-map-htpy-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (gap-is-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
      ( htpy-cone-gap-is-pullbackᵉ)

  coh-htpy-cone-gap-is-pullbackᵉ :
    coherence-htpy-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (gap-is-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
      ( htpy-vertical-map-gap-is-pullbackᵉ)
      ( htpy-horizontal-map-gap-is-pullbackᵉ)
  coh-htpy-cone-gap-is-pullbackᵉ =
    coh-htpy-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (gap-is-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
      ( htpy-cone-gap-is-pullbackᵉ)
```

## Properties

### The standard pullbacks are pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  is-pullback-standard-pullbackᵉ : is-pullbackᵉ fᵉ gᵉ (cone-standard-pullbackᵉ fᵉ gᵉ)
  is-pullback-standard-pullbackᵉ = is-equiv-idᵉ
```

### Pullbacks are preserved under homotopies of parallel cones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  {fᵉ f'ᵉ : Aᵉ → Xᵉ} (Hfᵉ : fᵉ ~ᵉ f'ᵉ) {gᵉ g'ᵉ : Bᵉ → Xᵉ} (Hgᵉ : gᵉ ~ᵉ g'ᵉ)
  where

  triangle-is-pullback-htpyᵉ :
    {cᵉ : coneᵉ fᵉ gᵉ Cᵉ} {c'ᵉ : coneᵉ f'ᵉ g'ᵉ Cᵉ} (Hcᵉ : htpy-parallel-coneᵉ Hfᵉ Hgᵉ cᵉ c'ᵉ) →
    gapᵉ fᵉ gᵉ cᵉ ~ᵉ map-equiv-standard-pullback-htpyᵉ Hfᵉ Hgᵉ ∘ᵉ gapᵉ f'ᵉ g'ᵉ c'ᵉ
  triangle-is-pullback-htpyᵉ {pᵉ ,ᵉ qᵉ ,ᵉ Hᵉ} {p'ᵉ ,ᵉ q'ᵉ ,ᵉ H'ᵉ} (Hpᵉ ,ᵉ Hqᵉ ,ᵉ HHᵉ) zᵉ =
    map-extensionality-standard-pullbackᵉ fᵉ gᵉ
      ( Hpᵉ zᵉ)
      ( Hqᵉ zᵉ)
      ( ( invᵉ (assocᵉ (apᵉ fᵉ (Hpᵉ zᵉ)) (Hfᵉ (p'ᵉ zᵉ) ∙ᵉ H'ᵉ zᵉ) (invᵉ (Hgᵉ (q'ᵉ zᵉ))))) ∙ᵉ
        ( invᵉ
          ( right-transpose-eq-concatᵉ
            ( Hᵉ zᵉ ∙ᵉ apᵉ gᵉ (Hqᵉ zᵉ))
            ( Hgᵉ (q'ᵉ zᵉ))
            ( apᵉ fᵉ (Hpᵉ zᵉ) ∙ᵉ (Hfᵉ (p'ᵉ zᵉ) ∙ᵉ H'ᵉ zᵉ))
            ( ( assocᵉ (Hᵉ zᵉ) (apᵉ gᵉ (Hqᵉ zᵉ)) (Hgᵉ (q'ᵉ zᵉ))) ∙ᵉ
              ( HHᵉ zᵉ) ∙ᵉ
              ( assocᵉ (apᵉ fᵉ (Hpᵉ zᵉ)) (Hfᵉ (p'ᵉ zᵉ)) (H'ᵉ zᵉ))))))

  abstract
    is-pullback-htpyᵉ :
      {cᵉ : coneᵉ fᵉ gᵉ Cᵉ} (c'ᵉ : coneᵉ f'ᵉ g'ᵉ Cᵉ)
      (Hcᵉ : htpy-parallel-coneᵉ Hfᵉ Hgᵉ cᵉ c'ᵉ) →
      is-pullbackᵉ f'ᵉ g'ᵉ c'ᵉ → is-pullbackᵉ fᵉ gᵉ cᵉ
    is-pullback-htpyᵉ {cᵉ} c'ᵉ Hᵉ pb-c'ᵉ =
      is-equiv-left-map-triangleᵉ
        ( gapᵉ fᵉ gᵉ cᵉ)
        ( map-equiv-standard-pullback-htpyᵉ Hfᵉ Hgᵉ)
        ( gapᵉ f'ᵉ g'ᵉ c'ᵉ)
        ( triangle-is-pullback-htpyᵉ Hᵉ)
        ( pb-c'ᵉ)
        ( is-equiv-map-equiv-standard-pullback-htpyᵉ Hfᵉ Hgᵉ)

  abstract
    is-pullback-htpy'ᵉ :
      (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) {c'ᵉ : coneᵉ f'ᵉ g'ᵉ Cᵉ}
      (Hcᵉ : htpy-parallel-coneᵉ Hfᵉ Hgᵉ cᵉ c'ᵉ) →
      is-pullbackᵉ fᵉ gᵉ cᵉ → is-pullbackᵉ f'ᵉ g'ᵉ c'ᵉ
    is-pullback-htpy'ᵉ cᵉ {c'ᵉ} Hᵉ =
      is-equiv-top-map-triangleᵉ
        ( gapᵉ fᵉ gᵉ cᵉ)
        ( map-equiv-standard-pullback-htpyᵉ Hfᵉ Hgᵉ)
        ( gapᵉ f'ᵉ g'ᵉ c'ᵉ)
        ( triangle-is-pullback-htpyᵉ Hᵉ)
        ( is-equiv-map-equiv-standard-pullback-htpyᵉ Hfᵉ Hgᵉ)
```

### Pullbacks are symmetric

Theᵉ pullbackᵉ ofᵉ `fᵉ : Aᵉ → Xᵉ ←ᵉ Bᵉ : g`ᵉ isᵉ alsoᵉ theᵉ pullbackᵉ ofᵉ `gᵉ : Bᵉ → Xᵉ ←ᵉ Aᵉ : f`.ᵉ

```agda
abstract
  is-pullback-swap-coneᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
    is-pullbackᵉ fᵉ gᵉ cᵉ → is-pullbackᵉ gᵉ fᵉ (swap-coneᵉ fᵉ gᵉ cᵉ)
  is-pullback-swap-coneᵉ fᵉ gᵉ cᵉ pb-cᵉ =
    is-equiv-left-map-triangleᵉ
      ( gapᵉ gᵉ fᵉ (swap-coneᵉ fᵉ gᵉ cᵉ))
      ( map-commutative-standard-pullbackᵉ fᵉ gᵉ)
      ( gapᵉ fᵉ gᵉ cᵉ)
      ( triangle-map-commutative-standard-pullbackᵉ fᵉ gᵉ cᵉ)
      ( pb-cᵉ)
      ( is-equiv-map-commutative-standard-pullbackᵉ fᵉ gᵉ)

abstract
  is-pullback-swap-cone'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
    is-pullbackᵉ gᵉ fᵉ (swap-coneᵉ fᵉ gᵉ cᵉ) → is-pullbackᵉ fᵉ gᵉ cᵉ
  is-pullback-swap-cone'ᵉ fᵉ gᵉ cᵉ =
    is-equiv-top-map-triangleᵉ
      ( gapᵉ gᵉ fᵉ (swap-coneᵉ fᵉ gᵉ cᵉ))
      ( map-commutative-standard-pullbackᵉ fᵉ gᵉ)
      ( gapᵉ fᵉ gᵉ cᵉ)
      ( triangle-map-commutative-standard-pullbackᵉ fᵉ gᵉ cᵉ)
      ( is-equiv-map-commutative-standard-pullbackᵉ fᵉ gᵉ)
```

### A cone is a pullback if and only if it induces a family of equivalences between the fibers of the vertical maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  square-tot-map-fiber-vertical-map-coneᵉ :
    gapᵉ fᵉ gᵉ cᵉ ∘ᵉ map-equiv-total-fiberᵉ (pr1ᵉ cᵉ) ~ᵉ
    totᵉ (λ _ → totᵉ (λ _ → invᵉ)) ∘ᵉ totᵉ (map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ)
  square-tot-map-fiber-vertical-map-coneᵉ
    (.(vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ) ,ᵉ xᵉ ,ᵉ reflᵉ) =
    eq-pair-eq-fiberᵉ
      ( eq-pair-eq-fiberᵉ
        ( invᵉ (apᵉ invᵉ right-unitᵉ ∙ᵉ inv-invᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ xᵉ))))

  abstract
    is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ :
      is-pullbackᵉ fᵉ gᵉ cᵉ → is-fiberwise-equivᵉ (map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ)
    is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ pbᵉ =
      is-fiberwise-equiv-is-equiv-totᵉ
        ( is-equiv-top-is-equiv-bottom-squareᵉ
          ( map-equiv-total-fiberᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ))
          ( totᵉ (λ _ → totᵉ (λ _ → invᵉ)))
          ( totᵉ (map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ))
          ( gapᵉ fᵉ gᵉ cᵉ)
          ( square-tot-map-fiber-vertical-map-coneᵉ)
          ( is-equiv-map-equiv-total-fiberᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ))
          ( is-equiv-tot-is-fiberwise-equivᵉ
            ( λ xᵉ →
              is-equiv-tot-is-fiberwise-equivᵉ (λ yᵉ → is-equiv-invᵉ (gᵉ yᵉ) (fᵉ xᵉ))))
          ( pbᵉ))

  abstract
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ :
      is-fiberwise-equivᵉ (map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ) → is-pullbackᵉ fᵉ gᵉ cᵉ
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ is-equiv-fsqᵉ =
      is-equiv-bottom-is-equiv-top-squareᵉ
        ( map-equiv-total-fiberᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ))
        ( totᵉ (λ _ → totᵉ (λ _ → invᵉ)))
        ( totᵉ (map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ))
        ( gapᵉ fᵉ gᵉ cᵉ)
        ( square-tot-map-fiber-vertical-map-coneᵉ)
        ( is-equiv-map-equiv-total-fiberᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ))
        ( is-equiv-tot-is-fiberwise-equivᵉ
          ( λ xᵉ →
            is-equiv-tot-is-fiberwise-equivᵉ (λ yᵉ → is-equiv-invᵉ (gᵉ yᵉ) (fᵉ xᵉ))))
        ( is-equiv-tot-is-fiberwise-equivᵉ is-equiv-fsqᵉ)
```

### The horizontal pullback pasting property

Givenᵉ aᵉ diagramᵉ asᵉ followsᵉ where theᵉ right-handᵉ squareᵉ isᵉ aᵉ pullbackᵉ

```text
  ∙ᵉ ------->ᵉ ∙ᵉ ------->ᵉ ∙ᵉ
  |          | ⌟ᵉ        |
  |          |          |
  ∨ᵉ          ∨ᵉ          ∨ᵉ
  ∙ᵉ ------->ᵉ ∙ᵉ ------->ᵉ ∙,ᵉ
```

thenᵉ theᵉ left-handᵉ squareᵉ isᵉ aᵉ pullbackᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ compositeᵉ squareᵉ is.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  (iᵉ : Xᵉ → Yᵉ) (jᵉ : Yᵉ → Zᵉ) (hᵉ : Cᵉ → Zᵉ)
  (cᵉ : coneᵉ jᵉ hᵉ Bᵉ) (dᵉ : coneᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) Aᵉ)
  where

  abstract
    is-pullback-rectangle-is-pullback-left-squareᵉ :
      is-pullbackᵉ jᵉ hᵉ cᵉ → is-pullbackᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) dᵉ →
      is-pullbackᵉ (jᵉ ∘ᵉ iᵉ) hᵉ (pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ)
    is-pullback-rectangle-is-pullback-left-squareᵉ pb-cᵉ pb-dᵉ =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ (jᵉ ∘ᵉ iᵉ) hᵉ
        ( pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ)
        ( λ xᵉ →
          is-equiv-left-map-triangleᵉ
            ( map-fiber-vertical-map-coneᵉ
              ( jᵉ ∘ᵉ iᵉ) hᵉ (pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ) xᵉ)
            ( map-fiber-vertical-map-coneᵉ jᵉ hᵉ cᵉ (iᵉ xᵉ))
            ( map-fiber-vertical-map-coneᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) dᵉ xᵉ)
            ( preserves-pasting-horizontal-map-fiber-vertical-map-coneᵉ
              ( iᵉ)
              ( jᵉ)
              ( hᵉ)
              ( cᵉ)
              ( dᵉ)
              ( xᵉ))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ
              ( iᵉ)
              ( vertical-map-coneᵉ jᵉ hᵉ cᵉ)
              ( dᵉ)
              ( pb-dᵉ)
              ( xᵉ))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ
              ( jᵉ)
              ( hᵉ)
              ( cᵉ)
              ( pb-cᵉ)
              ( iᵉ xᵉ)))

  abstract
    is-pullback-left-square-is-pullback-rectangleᵉ :
      is-pullbackᵉ jᵉ hᵉ cᵉ →
      is-pullbackᵉ (jᵉ ∘ᵉ iᵉ) hᵉ (pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ) →
      is-pullbackᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) dᵉ
    is-pullback-left-square-is-pullback-rectangleᵉ pb-cᵉ pb-rectᵉ =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ iᵉ
        ( vertical-map-coneᵉ jᵉ hᵉ cᵉ)
        ( dᵉ)
        ( λ xᵉ →
          is-equiv-top-map-triangleᵉ
            ( map-fiber-vertical-map-coneᵉ
              ( jᵉ ∘ᵉ iᵉ) hᵉ (pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ) xᵉ)
            ( map-fiber-vertical-map-coneᵉ jᵉ hᵉ cᵉ (iᵉ xᵉ))
            ( map-fiber-vertical-map-coneᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) dᵉ xᵉ)
            ( preserves-pasting-horizontal-map-fiber-vertical-map-coneᵉ
              ( iᵉ)
              ( jᵉ)
              ( hᵉ)
              ( cᵉ)
              ( dᵉ)
              ( xᵉ))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ
              ( jᵉ)
              ( hᵉ)
              ( cᵉ)
              ( pb-cᵉ)
              ( iᵉ xᵉ))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ
              ( jᵉ ∘ᵉ iᵉ)
              ( hᵉ)
              ( pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ)
              ( pb-rectᵉ)
              ( xᵉ)))
```

### The vertical pullback pasting property

Givenᵉ aᵉ diagramᵉ asᵉ followsᵉ where theᵉ lowerᵉ squareᵉ isᵉ aᵉ pullbackᵉ

```text
  ∙ᵉ ------->ᵉ ∙ᵉ
  |          |
  |          |
  ∨ᵉ          ∨ᵉ
  ∙ᵉ ------->ᵉ ∙ᵉ
  | ⌟ᵉ        |
  |          |
  ∨ᵉ          ∨ᵉ
  ∙ᵉ ------->ᵉ ∙,ᵉ
```

thenᵉ theᵉ upperᵉ squareᵉ isᵉ aᵉ pullbackᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ compositeᵉ squareᵉ is.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  (fᵉ : Cᵉ → Zᵉ) (gᵉ : Yᵉ → Zᵉ) (hᵉ : Xᵉ → Yᵉ)
  (cᵉ : coneᵉ fᵉ gᵉ Bᵉ) (dᵉ : coneᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ Aᵉ)
  where

  abstract
    is-pullback-top-square-is-pullback-rectangleᵉ :
      is-pullbackᵉ fᵉ gᵉ cᵉ →
      is-pullbackᵉ fᵉ (gᵉ ∘ᵉ hᵉ) (pasting-vertical-coneᵉ fᵉ gᵉ hᵉ cᵉ dᵉ) →
      is-pullbackᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ dᵉ
    is-pullback-top-square-is-pullback-rectangleᵉ pb-cᵉ pb-dcᵉ =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ
        ( horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
        ( hᵉ)
        ( dᵉ)
        ( λ xᵉ →
          is-fiberwise-equiv-is-equiv-map-Σᵉ
            ( λ tᵉ → fiberᵉ hᵉ (pr1ᵉ tᵉ))
            ( map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
            ( λ tᵉ →
              map-fiber-vertical-map-coneᵉ
                ( horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
                ( hᵉ)
                ( dᵉ)
                ( pr1ᵉ tᵉ))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ
              ( fᵉ)
              ( gᵉ)
              ( cᵉ)
              ( pb-cᵉ)
              ( vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
            ( is-equiv-top-is-equiv-bottom-squareᵉ
              ( map-inv-compute-fiber-compᵉ
                ( vertical-map-coneᵉ fᵉ gᵉ cᵉ)
                ( vertical-map-coneᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ dᵉ)
                ( vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
              ( map-inv-compute-fiber-compᵉ gᵉ hᵉ (fᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ)))
              ( map-Σᵉ
                ( λ tᵉ → fiberᵉ hᵉ (pr1ᵉ tᵉ))
                ( map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
                ( λ tᵉ →
                  map-fiber-vertical-map-coneᵉ
                    ( horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ dᵉ (pr1ᵉ tᵉ)))
              ( map-fiber-vertical-map-coneᵉ fᵉ
                ( gᵉ ∘ᵉ hᵉ)
                ( pasting-vertical-coneᵉ fᵉ gᵉ hᵉ cᵉ dᵉ)
                ( vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
              ( preserves-pasting-vertical-map-fiber-vertical-map-coneᵉ fᵉ gᵉ hᵉ cᵉ dᵉ
                ( vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
              ( is-equiv-map-inv-compute-fiber-compᵉ
                ( vertical-map-coneᵉ fᵉ gᵉ cᵉ)
                ( vertical-map-coneᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ dᵉ)
                ( vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
              ( is-equiv-map-inv-compute-fiber-compᵉ gᵉ hᵉ
                ( fᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ)))
              ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ fᵉ
                ( gᵉ ∘ᵉ hᵉ)
                ( pasting-vertical-coneᵉ fᵉ gᵉ hᵉ cᵉ dᵉ)
                ( pb-dcᵉ)
                ( vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ)))
            ( xᵉ ,ᵉ reflᵉ))

  abstract
    is-pullback-rectangle-is-pullback-top-squareᵉ :
      is-pullbackᵉ fᵉ gᵉ cᵉ →
      is-pullbackᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ dᵉ →
      is-pullbackᵉ fᵉ (gᵉ ∘ᵉ hᵉ) (pasting-vertical-coneᵉ fᵉ gᵉ hᵉ cᵉ dᵉ)
    is-pullback-rectangle-is-pullback-top-squareᵉ pb-cᵉ pb-dᵉ =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ
        ( fᵉ)
        ( gᵉ ∘ᵉ hᵉ)
        ( pasting-vertical-coneᵉ fᵉ gᵉ hᵉ cᵉ dᵉ)
        ( λ xᵉ →
          is-equiv-bottom-is-equiv-top-squareᵉ
            ( map-inv-compute-fiber-compᵉ
              ( vertical-map-coneᵉ fᵉ gᵉ cᵉ)
              ( vertical-map-coneᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ dᵉ)
              ( xᵉ))
            ( map-inv-compute-fiber-compᵉ gᵉ hᵉ (fᵉ xᵉ))
            ( map-Σᵉ
              ( λ tᵉ → fiberᵉ hᵉ (pr1ᵉ tᵉ))
              ( map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ)
              ( λ tᵉ →
                map-fiber-vertical-map-coneᵉ
                  ( horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
                  ( hᵉ)
                  ( dᵉ)
                  ( pr1ᵉ tᵉ)))
            ( map-fiber-vertical-map-coneᵉ
              ( fᵉ)
              ( gᵉ ∘ᵉ hᵉ)
              ( pasting-vertical-coneᵉ fᵉ gᵉ hᵉ cᵉ dᵉ)
              ( xᵉ))
            ( preserves-pasting-vertical-map-fiber-vertical-map-coneᵉ
              ( fᵉ)
              ( gᵉ)
              ( hᵉ)
              ( cᵉ)
              ( dᵉ)
              ( xᵉ))
            ( is-equiv-map-inv-compute-fiber-compᵉ
              ( vertical-map-coneᵉ fᵉ gᵉ cᵉ)
              ( vertical-map-coneᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ dᵉ)
              ( xᵉ))
            ( is-equiv-map-inv-compute-fiber-compᵉ gᵉ hᵉ (fᵉ xᵉ))
            ( is-equiv-map-Σᵉ
              ( λ tᵉ → fiberᵉ hᵉ (pr1ᵉ tᵉ))
              ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ
                ( fᵉ)
                ( gᵉ)
                ( cᵉ)
                ( pb-cᵉ)
                ( xᵉ))
              ( λ tᵉ →
                is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ
                  ( horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
                  ( hᵉ)
                  ( dᵉ)
                  ( pb-dᵉ)
                  ( pr1ᵉ tᵉ))))
```

### Pullbacks are associative

Considerᵉ twoᵉ cospansᵉ with aᵉ sharedᵉ vertexᵉ `B`ᵉ:

```text
      fᵉ       gᵉ       hᵉ       iᵉ
  Aᵉ ---->ᵉ Xᵉ <----ᵉ Bᵉ ---->ᵉ Yᵉ <----ᵉ C,ᵉ
```

andᵉ with pullbackᵉ conesᵉ `α`ᵉ andᵉ `β`ᵉ respectively.ᵉ Moreover,ᵉ considerᵉ aᵉ coneᵉ `γ`ᵉ
overᵉ theᵉ pullbacksᵉ asᵉ in theᵉ followingᵉ diagramᵉ

```text
  ∙ᵉ ------------>ᵉ ∙ᵉ ------------>ᵉ Cᵉ
  |               | ⌟ᵉ             |
  |       γᵉ       |       βᵉ       | iᵉ
  ∨ᵉ               ∨ᵉ               ∨ᵉ
  ∙ᵉ ------------>ᵉ Bᵉ ------------>ᵉ Yᵉ
  | ⌟ᵉ             |       hᵉ
  |       αᵉ       | gᵉ
  ∨ᵉ               ∨ᵉ
  Aᵉ ------------>ᵉ X.ᵉ
          fᵉ
```

Thenᵉ theᵉ pastingᵉ `γᵉ □ᵉ α`ᵉ isᵉ aᵉ pullbackᵉ ifᵉ andᵉ onlyᵉ ifᵉ `γ`ᵉ isᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ
pastingᵉ `γᵉ □ᵉ β`ᵉ is.ᵉ And,ᵉ in particular,ᵉ weᵉ haveᵉ theᵉ equivalenceᵉ

$$ᵉ
(Aᵉ ×_Xᵉ Bᵉ) ×_Yᵉ Cᵉ ≃ᵉ Aᵉ ×_Xᵉ (Bᵉ ×_Yᵉ C).ᵉ
$$ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
  {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} {Bᵉ : UUᵉ l4ᵉ} {Cᵉ : UUᵉ l5ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Bᵉ → Yᵉ) (iᵉ : Cᵉ → Yᵉ)
  {Sᵉ : UUᵉ l6ᵉ} {Tᵉ : UUᵉ l7ᵉ} {Uᵉ : UUᵉ l8ᵉ}
  (αᵉ : coneᵉ fᵉ gᵉ Sᵉ) (βᵉ : coneᵉ hᵉ iᵉ Tᵉ)
  (γᵉ : coneᵉ (horizontal-map-coneᵉ fᵉ gᵉ αᵉ) (vertical-map-coneᵉ hᵉ iᵉ βᵉ) Uᵉ)
  (is-pullback-αᵉ : is-pullbackᵉ fᵉ gᵉ αᵉ)
  (is-pullback-βᵉ : is-pullbackᵉ hᵉ iᵉ βᵉ)
  where

  is-pullback-associativeᵉ :
    is-pullbackᵉ
      ( fᵉ)
      ( gᵉ ∘ᵉ vertical-map-coneᵉ hᵉ iᵉ βᵉ)
      ( pasting-vertical-coneᵉ fᵉ gᵉ (vertical-map-coneᵉ hᵉ iᵉ βᵉ) αᵉ γᵉ) →
    is-pullbackᵉ
      ( hᵉ ∘ᵉ horizontal-map-coneᵉ fᵉ gᵉ αᵉ)
      ( iᵉ)
      ( pasting-horizontal-coneᵉ (horizontal-map-coneᵉ fᵉ gᵉ αᵉ) hᵉ iᵉ βᵉ γᵉ)
  is-pullback-associativeᵉ Hᵉ =
    is-pullback-rectangle-is-pullback-left-squareᵉ
      ( horizontal-map-coneᵉ fᵉ gᵉ αᵉ)
      ( hᵉ)
      ( iᵉ)
      ( βᵉ)
      ( γᵉ)
      ( is-pullback-βᵉ)
      ( is-pullback-top-square-is-pullback-rectangleᵉ
        ( fᵉ)
        ( gᵉ)
        ( vertical-map-coneᵉ hᵉ iᵉ βᵉ)
        ( αᵉ)
        ( γᵉ)
        ( is-pullback-αᵉ)
        ( Hᵉ))

  is-pullback-inv-associativeᵉ :
    is-pullbackᵉ
      ( hᵉ ∘ᵉ horizontal-map-coneᵉ fᵉ gᵉ αᵉ)
      ( iᵉ)
      ( pasting-horizontal-coneᵉ (horizontal-map-coneᵉ fᵉ gᵉ αᵉ) hᵉ iᵉ βᵉ γᵉ) →
    is-pullbackᵉ
      ( fᵉ)
      ( gᵉ ∘ᵉ vertical-map-coneᵉ hᵉ iᵉ βᵉ)
      ( pasting-vertical-coneᵉ fᵉ gᵉ (vertical-map-coneᵉ hᵉ iᵉ βᵉ) αᵉ γᵉ)
  is-pullback-inv-associativeᵉ Hᵉ =
    is-pullback-rectangle-is-pullback-top-squareᵉ
        ( fᵉ)
        ( gᵉ)
        ( vertical-map-coneᵉ hᵉ iᵉ βᵉ)
        ( αᵉ)
        ( γᵉ)
        ( is-pullback-αᵉ)
        ( is-pullback-left-square-is-pullback-rectangleᵉ
          ( horizontal-map-coneᵉ fᵉ gᵉ αᵉ)
          ( hᵉ)
          ( iᵉ)
          ( βᵉ)
          ( γᵉ)
          ( is-pullback-βᵉ)
          ( Hᵉ))
```

### Pullbacks can be "folded"

Givenᵉ aᵉ pullbackᵉ squareᵉ

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

  abstract
    is-pullback-fold-cone-is-pullbackᵉ :
      {l4ᵉ : Level} {Cᵉ : UUᵉ l4ᵉ} (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
      is-pullbackᵉ fᵉ gᵉ cᵉ →
      is-pullbackᵉ (map-productᵉ fᵉ gᵉ) (diagonal-productᵉ Xᵉ) (fold-coneᵉ fᵉ gᵉ cᵉ)
    is-pullback-fold-cone-is-pullbackᵉ cᵉ pb-cᵉ =
      is-equiv-left-map-triangleᵉ
        ( gapᵉ (map-productᵉ fᵉ gᵉ) (diagonal-productᵉ Xᵉ) (fold-coneᵉ fᵉ gᵉ cᵉ))
        ( map-fold-cone-standard-pullbackᵉ fᵉ gᵉ)
        ( gapᵉ fᵉ gᵉ cᵉ)
        ( triangle-map-fold-cone-standard-pullbackᵉ fᵉ gᵉ cᵉ)
        ( pb-cᵉ)
        ( is-equiv-map-fold-cone-standard-pullbackᵉ fᵉ gᵉ)

  abstract
    is-pullback-is-pullback-fold-coneᵉ :
      {l4ᵉ : Level} {Cᵉ : UUᵉ l4ᵉ} (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
      is-pullbackᵉ (map-productᵉ fᵉ gᵉ) (diagonal-productᵉ Xᵉ) (fold-coneᵉ fᵉ gᵉ cᵉ) →
      is-pullbackᵉ fᵉ gᵉ cᵉ
    is-pullback-is-pullback-fold-coneᵉ cᵉ =
      is-equiv-top-map-triangleᵉ
        ( gapᵉ (map-productᵉ fᵉ gᵉ) (diagonal-productᵉ Xᵉ) (fold-coneᵉ fᵉ gᵉ cᵉ))
        ( map-fold-cone-standard-pullbackᵉ fᵉ gᵉ)
        ( gapᵉ fᵉ gᵉ cᵉ)
        ( triangle-map-fold-cone-standard-pullbackᵉ fᵉ gᵉ cᵉ)
        ( is-equiv-map-fold-cone-standard-pullbackᵉ fᵉ gᵉ)
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}