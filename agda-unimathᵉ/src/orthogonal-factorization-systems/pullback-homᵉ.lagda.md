# The pullback-hom

```agda
module orthogonal-factorization-systems.pullback-homᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-arrowsᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-fibers-of-mapsᵉ
open import foundation.higher-homotopies-morphisms-arrowsᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopies-morphisms-arrowsᵉ
open import foundation.identity-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.pullbacksᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.universal-property-pullbacksᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "pullback-hom"ᵉ Agda=pullback-homᵉ}} orᵉ
{{#conceptᵉ "pullback-power"ᵉ Agda=pullback-homᵉ}} ofᵉ twoᵉ mapsᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ
`gᵉ : Xᵉ → Y`,ᵉ isᵉ theᵉ [gapᵉ map](foundation.pullbacks.mdᵉ) ofᵉ theᵉ
[commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ):

```text
             -ᵉ ∘ᵉ fᵉ
      Bᵉ → Xᵉ ------->ᵉ Aᵉ → Xᵉ
        |              |
  gᵉ ∘ᵉ -ᵉ |              | gᵉ ∘ᵉ -ᵉ
        ∨ᵉ              ∨ᵉ
      Bᵉ → Yᵉ ------->ᵉ Aᵉ → Y.ᵉ
             -ᵉ ∘ᵉ fᵉ
```

Moreᵉ explicitly,ᵉ theᵉ pullbackᵉ ofᵉ `-ᵉ ∘ᵉ f`ᵉ andᵉ `gᵉ ∘ᵉ -`ᵉ isᵉ theᵉ typeᵉ ofᵉ
[morphismsᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) fromᵉ `f`ᵉ to `g`,ᵉ whileᵉ theᵉ
domainᵉ ofᵉ theᵉ pullback-homᵉ isᵉ theᵉ typeᵉ `Bᵉ → X`ᵉ ofᵉ diagonalᵉ fillersᵉ forᵉ morphismsᵉ
ofᵉ arrowsᵉ fromᵉ `f`ᵉ to `g`.ᵉ Theᵉ pullback-homᵉ canᵉ thereforeᵉ beᵉ describedᵉ asᵉ aᵉ mapᵉ

```text
  pullback-homᵉ fᵉ gᵉ : (Bᵉ → Xᵉ) → hom-arrowᵉ fᵉ gᵉ
```

Thisᵉ mapᵉ takesᵉ aᵉ mapᵉ `jᵉ : Bᵉ → X`ᵉ asᵉ in theᵉ diagramᵉ

```text
    Aᵉ       Xᵉ
    |     ∧ᵉ |
  fᵉ |  j/ᵉ   | gᵉ
    ∨ᵉ /ᵉ     ∨ᵉ
    Bᵉ       Yᵉ
```

to theᵉ [morphismᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) fromᵉ `f`ᵉ to `g`ᵉ asᵉ
in theᵉ diagramᵉ

```text
         jᵉ ∘ᵉ fᵉ
    Aᵉ ---------->ᵉ Xᵉ
    |             |
  fᵉ |  refl-htpyᵉ  | gᵉ
    ∨ᵉ             ∨ᵉ
    Bᵉ ---------->ᵉ Y.ᵉ
         gᵉ ∘ᵉ jᵉ
```

Theᵉ [fibers](foundation-core.fibers-of-maps.mdᵉ) ofᵉ theᵉ pullback-homᵉ areᵉ
[liftingᵉ squares](orthogonal-factorization-systems.lifting-structures-on-squares.md).ᵉ
Theᵉ pullback-homᵉ isᵉ thereforeᵉ aᵉ fundamentalᵉ operationᵉ in theᵉ studyᵉ ofᵉ
[liftingᵉ conditions](orthogonal-factorization-systems.mere-lifting-properties.mdᵉ)
andᵉ
[orthogonalityᵉ conditions](orthogonal-factorization-systems.orthogonal-maps.mdᵉ):
Theᵉ pullback-homᵉ ofᵉ `f`ᵉ andᵉ `g`ᵉ isᵉ anᵉ
[equivalence](foundation-core.equivalences.mdᵉ) ifᵉ andᵉ onlyᵉ ifᵉ `f`ᵉ isᵉ leftᵉ
orthogonalᵉ to `g`,ᵉ whileᵉ theᵉ pullback-homᵉ ofᵉ `f`ᵉ andᵉ `g`ᵉ isᵉ
[surjective](foundation.surjective-maps.mdᵉ) ifᵉ andᵉ onlyᵉ ifᵉ `f`ᵉ satisfiesᵉ theᵉ
leftᵉ liftingᵉ propertyᵉ to `g`.ᵉ

Thereᵉ areᵉ twoᵉ commonᵉ waysᵉ to denoteᵉ theᵉ pullback-homᵉ: Someᵉ authorsᵉ useᵉ `fᵉ ⋔ᵉ g`,ᵉ
whileᵉ otherᵉ authorsᵉ useᵉ `⟨fᵉ ,ᵉ g⟩`.ᵉ Bothᵉ notationsᵉ canᵉ beᵉ used,ᵉ dependingᵉ onᵉ whatᵉ
perspectiveᵉ ofᵉ theᵉ pullback-homᵉ isᵉ emphasized.ᵉ Theᵉ pitchfork-notationᵉ `fᵉ ⋔ᵉ g`ᵉ isᵉ
usedᵉ moreᵉ oftenᵉ in settingsᵉ where aᵉ liftingᵉ propertyᵉ ofᵉ `f`ᵉ andᵉ `g`ᵉ isᵉ
emphasized,ᵉ whileᵉ theᵉ hom-notationᵉ `⟨fᵉ ,ᵉ g⟩`ᵉ isᵉ usedᵉ whenᵉ theᵉ pullback-homᵉ isᵉ
thoughtᵉ ofᵉ in termsᵉ ofᵉ hom-sets.ᵉ Theᵉ latterᵉ notationᵉ isᵉ usefulᵉ forᵉ instance,ᵉ ifᵉ
oneᵉ wantsᵉ to emphasizeᵉ anᵉ adjointᵉ relationᵉ betweenᵉ theᵉ pullback-homᵉ andᵉ theᵉ
pushout-productᵉ:

```text
  ⟨fᵉ □ᵉ gᵉ ,ᵉ h⟩ᵉ ＝ᵉ ⟨fᵉ ,ᵉ ⟨gᵉ ,ᵉ h⟩⟩.ᵉ
```

## Definitions

### The pullback-hom

Theᵉ pullback-homᵉ `fᵉ ⋔ᵉ g`ᵉ isᵉ theᵉ mapᵉ `(Bᵉ → Xᵉ) → hom-arrowᵉ fᵉ g`,ᵉ thatᵉ takesᵉ aᵉ
diagonalᵉ mapᵉ `j`ᵉ fromᵉ theᵉ codomainᵉ ofᵉ `f`ᵉ to theᵉ domainᵉ ofᵉ `g`ᵉ to theᵉ morphismᵉ
ofᵉ arrowsᵉ

```text
         jᵉ ∘ᵉ fᵉ
    Aᵉ ---------->ᵉ Xᵉ
    |             |
  fᵉ |  refl-htpyᵉ  | gᵉ
    ∨ᵉ             ∨ᵉ
    Bᵉ ---------->ᵉ Y.ᵉ
         gᵉ ∘ᵉ jᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  map-domain-pullback-homᵉ : (Bᵉ → Xᵉ) → Aᵉ → Xᵉ
  map-domain-pullback-homᵉ jᵉ = jᵉ ∘ᵉ fᵉ

  map-codomain-pullback-homᵉ : (Bᵉ → Xᵉ) → Bᵉ → Yᵉ
  map-codomain-pullback-homᵉ jᵉ = gᵉ ∘ᵉ jᵉ

  coh-pullback-homᵉ :
    (jᵉ : Bᵉ → Xᵉ) →
    coherence-hom-arrowᵉ fᵉ gᵉ
      ( map-domain-pullback-homᵉ jᵉ)
      ( map-codomain-pullback-homᵉ jᵉ)
  coh-pullback-homᵉ jᵉ = refl-htpyᵉ

  pullback-homᵉ : (Bᵉ → Xᵉ) → hom-arrowᵉ fᵉ gᵉ
  pr1ᵉ (pullback-homᵉ jᵉ) = map-domain-pullback-homᵉ jᵉ
  pr1ᵉ (pr2ᵉ (pullback-homᵉ jᵉ)) = map-codomain-pullback-homᵉ jᵉ
  pr2ᵉ (pr2ᵉ (pullback-homᵉ jᵉ)) = coh-pullback-homᵉ jᵉ

  infix 30 _⋔ᵉ_
  _⋔ᵉ_ = pullback-homᵉ
```

Theᵉ symbolᵉ `⋔`ᵉ isᵉ theᵉ [pitchfork](https://codepoints.net/U+22D4ᵉ) (agda-inputᵉ:
`\pitchfork`).ᵉ

### The cone structure on the codomain of the pullback-hom

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  left-projection-hom-arrow-pullback-homᵉ : hom-arrowᵉ fᵉ gᵉ → Bᵉ → Yᵉ
  left-projection-hom-arrow-pullback-homᵉ = map-codomain-hom-arrowᵉ fᵉ gᵉ

  right-projection-hom-arrow-pullback-homᵉ : hom-arrowᵉ fᵉ gᵉ → Aᵉ → Xᵉ
  right-projection-hom-arrow-pullback-homᵉ = map-domain-hom-arrowᵉ fᵉ gᵉ

  coherence-square-cone-hom-arrow-pullback-homᵉ :
    coherence-square-mapsᵉ
      ( right-projection-hom-arrow-pullback-homᵉ)
      ( left-projection-hom-arrow-pullback-homᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( precompᵉ fᵉ Yᵉ)
  coherence-square-cone-hom-arrow-pullback-homᵉ hᵉ = eq-htpyᵉ (coh-hom-arrowᵉ fᵉ gᵉ hᵉ)

  cone-hom-arrow-pullback-homᵉ :
    coneᵉ (precompᵉ fᵉ Yᵉ) (postcompᵉ Aᵉ gᵉ) (hom-arrowᵉ fᵉ gᵉ)
  pr1ᵉ cone-hom-arrow-pullback-homᵉ = left-projection-hom-arrow-pullback-homᵉ
  pr1ᵉ (pr2ᵉ cone-hom-arrow-pullback-homᵉ) =
    right-projection-hom-arrow-pullback-homᵉ
  pr2ᵉ (pr2ᵉ cone-hom-arrow-pullback-homᵉ) =
    coherence-square-cone-hom-arrow-pullback-homᵉ
```

### The standard pullback of the defining cospan of the pullback-hom

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  type-standard-pullback-homᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  type-standard-pullback-homᵉ =
    standard-pullbackᵉ (precompᵉ fᵉ Yᵉ) (postcompᵉ Aᵉ gᵉ)

  module _
    (hᵉ : type-standard-pullback-homᵉ)
    where

    map-domain-standard-pullback-homᵉ : Aᵉ → Xᵉ
    map-domain-standard-pullback-homᵉ = pr1ᵉ (pr2ᵉ hᵉ)

    map-codomain-standard-pullback-homᵉ : Bᵉ → Yᵉ
    map-codomain-standard-pullback-homᵉ = pr1ᵉ hᵉ

    eq-coh-standard-pullback-homᵉ :
      precompᵉ fᵉ Yᵉ map-codomain-standard-pullback-homᵉ ＝ᵉ
      postcompᵉ Aᵉ gᵉ map-domain-standard-pullback-homᵉ
    eq-coh-standard-pullback-homᵉ = pr2ᵉ (pr2ᵉ hᵉ)

    coh-standard-pullback-homᵉ :
      precompᵉ fᵉ Yᵉ map-codomain-standard-pullback-homᵉ ~ᵉ
      postcompᵉ Aᵉ gᵉ map-domain-standard-pullback-homᵉ
    coh-standard-pullback-homᵉ = htpy-eqᵉ eq-coh-standard-pullback-homᵉ
```

### The cone of the diagram defining the pullback-hom

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  cone-pullback-homᵉ : coneᵉ (precompᵉ fᵉ Yᵉ) (postcompᵉ Aᵉ gᵉ) (Bᵉ → Xᵉ)
  pr1ᵉ cone-pullback-homᵉ = postcompᵉ Bᵉ gᵉ
  pr1ᵉ (pr2ᵉ cone-pullback-homᵉ) = precompᵉ fᵉ Xᵉ
  pr2ᵉ (pr2ᵉ cone-pullback-homᵉ) = refl-htpyᵉ

  gap-pullback-homᵉ : (Bᵉ → Xᵉ) → type-standard-pullback-homᵉ fᵉ gᵉ
  gap-pullback-homᵉ = gapᵉ (precompᵉ fᵉ Yᵉ) (postcompᵉ Aᵉ gᵉ) cone-pullback-homᵉ
```

### The equivalence of the codomain of the pullback-hom with the standard pullback

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  map-compute-pullback-homᵉ :
    hom-arrowᵉ fᵉ gᵉ → type-standard-pullback-homᵉ fᵉ gᵉ
  pr1ᵉ (map-compute-pullback-homᵉ hᵉ) =
    map-codomain-hom-arrowᵉ fᵉ gᵉ hᵉ
  pr1ᵉ (pr2ᵉ (map-compute-pullback-homᵉ hᵉ)) =
    map-domain-hom-arrowᵉ fᵉ gᵉ hᵉ
  pr2ᵉ (pr2ᵉ (map-compute-pullback-homᵉ hᵉ)) =
    eq-htpyᵉ (coh-hom-arrowᵉ fᵉ gᵉ hᵉ)

  map-inv-compute-pullback-homᵉ :
    type-standard-pullback-homᵉ fᵉ gᵉ → hom-arrowᵉ fᵉ gᵉ
  pr1ᵉ (map-inv-compute-pullback-homᵉ hᵉ) =
    map-domain-standard-pullback-homᵉ fᵉ gᵉ hᵉ
  pr1ᵉ (pr2ᵉ (map-inv-compute-pullback-homᵉ hᵉ)) =
    map-codomain-standard-pullback-homᵉ fᵉ gᵉ hᵉ
  pr2ᵉ (pr2ᵉ (map-inv-compute-pullback-homᵉ hᵉ)) =
    coh-standard-pullback-homᵉ fᵉ gᵉ hᵉ

  is-section-map-inv-compute-pullback-homᵉ :
    is-sectionᵉ map-compute-pullback-homᵉ map-inv-compute-pullback-homᵉ
  is-section-map-inv-compute-pullback-homᵉ hᵉ =
    eq-pair-eq-fiberᵉ
      ( eq-pair-eq-fiberᵉ
        ( is-retraction-eq-htpyᵉ (eq-coh-standard-pullback-homᵉ fᵉ gᵉ hᵉ)))

  is-retraction-map-inv-compute-pullback-homᵉ :
    is-retractionᵉ map-compute-pullback-homᵉ map-inv-compute-pullback-homᵉ
  is-retraction-map-inv-compute-pullback-homᵉ hᵉ =
    eq-pair-eq-fiberᵉ
      ( eq-pair-eq-fiberᵉ (is-section-eq-htpyᵉ (coh-hom-arrowᵉ fᵉ gᵉ hᵉ)))

  abstract
    is-equiv-map-compute-pullback-homᵉ :
      is-equivᵉ map-compute-pullback-homᵉ
    is-equiv-map-compute-pullback-homᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-compute-pullback-homᵉ)
        ( is-section-map-inv-compute-pullback-homᵉ)
        ( is-retraction-map-inv-compute-pullback-homᵉ)

  abstract
    is-equiv-map-inv-compute-pullback-homᵉ :
      is-equivᵉ map-inv-compute-pullback-homᵉ
    is-equiv-map-inv-compute-pullback-homᵉ =
      is-equiv-is-invertibleᵉ
        ( map-compute-pullback-homᵉ)
        ( is-retraction-map-inv-compute-pullback-homᵉ)
        ( is-section-map-inv-compute-pullback-homᵉ)

  compute-pullback-homᵉ : hom-arrowᵉ fᵉ gᵉ ≃ᵉ type-standard-pullback-homᵉ fᵉ gᵉ
  pr1ᵉ compute-pullback-homᵉ = map-compute-pullback-homᵉ
  pr2ᵉ compute-pullback-homᵉ = is-equiv-map-compute-pullback-homᵉ

  inv-compute-pullback-homᵉ : type-standard-pullback-homᵉ fᵉ gᵉ ≃ᵉ hom-arrowᵉ fᵉ gᵉ
  pr1ᵉ inv-compute-pullback-homᵉ = map-inv-compute-pullback-homᵉ
  pr2ᵉ inv-compute-pullback-homᵉ = is-equiv-map-inv-compute-pullback-homᵉ
```

### The commuting triangle of the pullback-hom and the gap map

Weᵉ constructᵉ theᵉ homotopyᵉ witnessingᵉ thatᵉ theᵉ triangleᵉ ofᵉ mapsᵉ

```text
                  (Bᵉ → Xᵉ)
                 /ᵉ       \ᵉ
  pullback-homᵉ  /ᵉ         \ᵉ gapᵉ
               ∨ᵉ           ∨ᵉ
     hom-arrowᵉ fᵉ gᵉ ----->ᵉ type-standard-pullback-homᵉ fᵉ gᵉ
```

commutes.ᵉ Theᵉ bottomᵉ mapᵉ in thisᵉ triangleᵉ isᵉ theᵉ underlyingᵉ mapᵉ ofᵉ theᵉ
equivalenceᵉ `hom-arrowᵉ fᵉ gᵉ ≃ᵉ type-stanard-pullback-homᵉ fᵉ g`ᵉ constructedᵉ above.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  triangle-pullback-homᵉ :
    coherence-triangle-maps'ᵉ
      ( gap-pullback-homᵉ fᵉ gᵉ)
      ( map-compute-pullback-homᵉ fᵉ gᵉ)
      ( pullback-homᵉ fᵉ gᵉ)
  triangle-pullback-homᵉ jᵉ =
    eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ (is-retraction-eq-htpyᵉ reflᵉ))
```

### The action on homotopies of the `pullback-hom`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) {jᵉ kᵉ : Bᵉ → Xᵉ} (Hᵉ : jᵉ ~ᵉ kᵉ)
  where

  htpy-domain-htpy-hom-arrow-htpyᵉ :
    map-domain-pullback-homᵉ fᵉ gᵉ jᵉ ~ᵉ map-domain-pullback-homᵉ fᵉ gᵉ kᵉ
  htpy-domain-htpy-hom-arrow-htpyᵉ = Hᵉ ·rᵉ fᵉ

  htpy-codomain-htpy-hom-arrow-htpyᵉ :
    map-codomain-pullback-homᵉ fᵉ gᵉ jᵉ ~ᵉ map-codomain-pullback-homᵉ fᵉ gᵉ kᵉ
  htpy-codomain-htpy-hom-arrow-htpyᵉ = gᵉ ·lᵉ Hᵉ

  coh-htpy-hom-arrow-htpyᵉ :
    coherence-htpy-hom-arrowᵉ fᵉ gᵉ
      ( pullback-homᵉ fᵉ gᵉ jᵉ)
      ( pullback-homᵉ fᵉ gᵉ kᵉ)
      ( htpy-domain-htpy-hom-arrow-htpyᵉ)
      ( htpy-codomain-htpy-hom-arrow-htpyᵉ)
  coh-htpy-hom-arrow-htpyᵉ = inv-htpyᵉ right-unit-htpyᵉ

  htpy-hom-arrow-htpyᵉ :
    htpy-hom-arrowᵉ fᵉ gᵉ (pullback-homᵉ fᵉ gᵉ jᵉ) (pullback-homᵉ fᵉ gᵉ kᵉ)
  pr1ᵉ htpy-hom-arrow-htpyᵉ = htpy-domain-htpy-hom-arrow-htpyᵉ
  pr1ᵉ (pr2ᵉ htpy-hom-arrow-htpyᵉ) = htpy-codomain-htpy-hom-arrow-htpyᵉ
  pr2ᵉ (pr2ᵉ htpy-hom-arrow-htpyᵉ) = coh-htpy-hom-arrow-htpyᵉ
```

## Properties

### The cone of the pullback-hom is a pullback

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-pullback-cone-hom-arrow-pullback-homᵉ :
    is-pullbackᵉ (precompᵉ fᵉ Yᵉ) (postcompᵉ Aᵉ gᵉ) (cone-hom-arrow-pullback-homᵉ fᵉ gᵉ)
  is-pullback-cone-hom-arrow-pullback-homᵉ =
    is-equiv-map-compute-pullback-homᵉ fᵉ gᵉ

  universal-property-pullback-cone-hom-arrow-pullback-homᵉ :
    universal-property-pullbackᵉ
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-hom-arrow-pullback-homᵉ fᵉ gᵉ)
  universal-property-pullback-cone-hom-arrow-pullback-homᵉ =
    universal-property-pullback-is-pullbackᵉ
      ( precompᵉ fᵉ Yᵉ)
      ( postcompᵉ Aᵉ gᵉ)
      ( cone-hom-arrow-pullback-homᵉ fᵉ gᵉ)
      ( is-pullback-cone-hom-arrow-pullback-homᵉ)
```

### The action on homotopies at `refl-htpy` is the reflexivity homotopy of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) {jᵉ : Bᵉ → Xᵉ}
  where

  htpy-domain-compute-refl-htpy-hom-arrow-htpyᵉ :
    htpy-domain-htpy-hom-arrow-htpyᵉ fᵉ gᵉ (refl-htpy'ᵉ jᵉ) ~ᵉ
    htpy-domain-refl-htpy-hom-arrowᵉ fᵉ gᵉ (pullback-homᵉ fᵉ gᵉ jᵉ)
  htpy-domain-compute-refl-htpy-hom-arrow-htpyᵉ = refl-htpyᵉ

  htpy-codomain-compute-refl-htpy-hom-arrow-htpyᵉ :
    htpy-codomain-htpy-hom-arrow-htpyᵉ fᵉ gᵉ (refl-htpy'ᵉ jᵉ) ~ᵉ
    htpy-codomain-refl-htpy-hom-arrowᵉ fᵉ gᵉ (pullback-homᵉ fᵉ gᵉ jᵉ)
  htpy-codomain-compute-refl-htpy-hom-arrow-htpyᵉ = refl-htpyᵉ

  coh-compute-refl-htpy-hom-arrow-htpyᵉ :
    coherence-htpy-htpy-hom-arrowᵉ fᵉ gᵉ
      ( pullback-homᵉ fᵉ gᵉ jᵉ)
      ( pullback-homᵉ fᵉ gᵉ jᵉ)
      ( htpy-hom-arrow-htpyᵉ fᵉ gᵉ refl-htpyᵉ)
      ( refl-htpy-hom-arrowᵉ fᵉ gᵉ (pullback-homᵉ fᵉ gᵉ jᵉ))
      ( htpy-domain-compute-refl-htpy-hom-arrow-htpyᵉ)
      ( htpy-codomain-compute-refl-htpy-hom-arrow-htpyᵉ)
  coh-compute-refl-htpy-hom-arrow-htpyᵉ = refl-htpyᵉ

  compute-refl-htpy-hom-arrow-htpyᵉ :
    htpy-htpy-hom-arrowᵉ fᵉ gᵉ
      ( pullback-homᵉ fᵉ gᵉ jᵉ)
      ( pullback-homᵉ fᵉ gᵉ jᵉ)
      ( htpy-hom-arrow-htpyᵉ fᵉ gᵉ refl-htpyᵉ)
      ( refl-htpy-hom-arrowᵉ fᵉ gᵉ (pullback-homᵉ fᵉ gᵉ jᵉ))
  pr1ᵉ compute-refl-htpy-hom-arrow-htpyᵉ =
    htpy-domain-compute-refl-htpy-hom-arrow-htpyᵉ
  pr1ᵉ (pr2ᵉ compute-refl-htpy-hom-arrow-htpyᵉ) =
    htpy-codomain-compute-refl-htpy-hom-arrow-htpyᵉ
  pr2ᵉ (pr2ᵉ compute-refl-htpy-hom-arrow-htpyᵉ) =
    coh-compute-refl-htpy-hom-arrow-htpyᵉ
```

### Computing the pullback-hom of a composite

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Sᵉ : UUᵉ l5ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Yᵉ → Sᵉ)
  where

  map-domain-left-whisker-hom-arrowᵉ : hom-arrowᵉ fᵉ gᵉ → Aᵉ → Xᵉ
  map-domain-left-whisker-hom-arrowᵉ αᵉ = map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ

  map-codomain-left-whisker-hom-arrowᵉ : hom-arrowᵉ fᵉ gᵉ → Bᵉ → Sᵉ
  map-codomain-left-whisker-hom-arrowᵉ αᵉ = hᵉ ∘ᵉ map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ

  coh-left-whisker-hom-arrowᵉ :
    (αᵉ : hom-arrowᵉ fᵉ gᵉ) →
    coherence-square-mapsᵉ
      ( map-domain-left-whisker-hom-arrowᵉ αᵉ)
      ( fᵉ)
      ( hᵉ ∘ᵉ gᵉ)
      ( map-codomain-left-whisker-hom-arrowᵉ αᵉ)
  coh-left-whisker-hom-arrowᵉ αᵉ = hᵉ ·lᵉ (coh-hom-arrowᵉ fᵉ gᵉ αᵉ)

  left-whisker-hom-arrowᵉ :
    hom-arrowᵉ fᵉ gᵉ → hom-arrowᵉ fᵉ (hᵉ ∘ᵉ gᵉ)
  pr1ᵉ (left-whisker-hom-arrowᵉ αᵉ) = map-domain-left-whisker-hom-arrowᵉ αᵉ
  pr1ᵉ (pr2ᵉ (left-whisker-hom-arrowᵉ αᵉ)) = map-codomain-left-whisker-hom-arrowᵉ αᵉ
  pr2ᵉ (pr2ᵉ (left-whisker-hom-arrowᵉ αᵉ)) = coh-left-whisker-hom-arrowᵉ αᵉ

  compute-pullback-hom-comp-rightᵉ :
    coherence-triangle-mapsᵉ
      ( pullback-homᵉ fᵉ (hᵉ ∘ᵉ gᵉ))
      ( left-whisker-hom-arrowᵉ)
      ( pullback-homᵉ fᵉ gᵉ)
  compute-pullback-hom-comp-rightᵉ = refl-htpyᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Sᵉ : UUᵉ l5ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Sᵉ → Aᵉ)
  where

  map-domain-right-whisker-hom-arrowᵉ : hom-arrowᵉ fᵉ gᵉ → Sᵉ → Xᵉ
  map-domain-right-whisker-hom-arrowᵉ αᵉ = map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ ∘ᵉ hᵉ

  map-codomain-right-whisker-hom-arrowᵉ : hom-arrowᵉ fᵉ gᵉ → Bᵉ → Yᵉ
  map-codomain-right-whisker-hom-arrowᵉ αᵉ = map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ

  coh-right-whisker-hom-arrowᵉ :
    (αᵉ : hom-arrowᵉ fᵉ gᵉ) →
    coherence-hom-arrowᵉ (fᵉ ∘ᵉ hᵉ) gᵉ
      ( map-domain-right-whisker-hom-arrowᵉ αᵉ)
      ( map-codomain-right-whisker-hom-arrowᵉ αᵉ)
  coh-right-whisker-hom-arrowᵉ αᵉ =
    coh-hom-arrowᵉ fᵉ gᵉ αᵉ ·rᵉ hᵉ

  right-whisker-hom-arrowᵉ :
    hom-arrowᵉ fᵉ gᵉ → hom-arrowᵉ (fᵉ ∘ᵉ hᵉ) gᵉ
  pr1ᵉ (right-whisker-hom-arrowᵉ αᵉ) = map-domain-right-whisker-hom-arrowᵉ αᵉ
  pr1ᵉ (pr2ᵉ (right-whisker-hom-arrowᵉ αᵉ)) = map-codomain-right-whisker-hom-arrowᵉ αᵉ
  pr2ᵉ (pr2ᵉ (right-whisker-hom-arrowᵉ αᵉ)) = coh-right-whisker-hom-arrowᵉ αᵉ

  compute-pullback-hom-comp-leftᵉ :
    coherence-triangle-mapsᵉ
      ( pullback-homᵉ (fᵉ ∘ᵉ hᵉ) gᵉ)
      ( right-whisker-hom-arrowᵉ)
      ( pullback-homᵉ fᵉ gᵉ)
  compute-pullback-hom-comp-leftᵉ = refl-htpyᵉ
```

### Computing the fiber map between the vertical maps in the pullback-hom square

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  compute-map-fiber-vertical-pullback-homᵉ :
    (hᵉ : Bᵉ → Yᵉ) →
    equiv-arrowᵉ
      ( precomp-Πᵉ fᵉ (fiberᵉ gᵉ ∘ᵉ hᵉ))
      ( map-fiber-vertical-map-coneᵉ
        ( precompᵉ fᵉ Yᵉ)
        ( postcompᵉ Aᵉ gᵉ)
        ( cone-pullback-homᵉ fᵉ gᵉ)
        ( hᵉ))
  pr1ᵉ (compute-map-fiber-vertical-pullback-homᵉ hᵉ) =
    compute-Π-fiber-postcompᵉ Bᵉ gᵉ hᵉ
  pr1ᵉ (pr2ᵉ (compute-map-fiber-vertical-pullback-homᵉ hᵉ)) =
    compute-Π-fiber-postcompᵉ Aᵉ gᵉ (hᵉ ∘ᵉ fᵉ)
  pr2ᵉ (pr2ᵉ (compute-map-fiber-vertical-pullback-homᵉ hᵉ)) Hᵉ =
    eq-Eq-fiberᵉ
      ( postcompᵉ Aᵉ gᵉ)
      ( precompᵉ fᵉ Yᵉ hᵉ)
      ( reflᵉ)
      ( compute-eq-htpy-ap-precompᵉ fᵉ (pr2ᵉ (map-distributive-Π-Σᵉ Hᵉ)))
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}

## External links

-ᵉ [Pullback-power](https://ncatlab.org/nlab/show/pullback+powerᵉ) atᵉ theᵉ $n$Labᵉ

Aᵉ wikidataᵉ identifierᵉ forᵉ thisᵉ conceptᵉ isᵉ unavailable.ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ Rie22ᵉ}}