# Coherently invertible maps

```agda
module foundation-core.coherently-invertible-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-higher-homotopies-compositionᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-homotopiesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.invertible-mapsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.whiskering-homotopies-concatenationᵉ
```

</details>

## Idea

Aᵉ [(two-sidedᵉ) inverse](foundation-core.invertible-maps.mdᵉ) forᵉ aᵉ mapᵉ
`fᵉ : Aᵉ → B`ᵉ isᵉ aᵉ mapᵉ `gᵉ : Bᵉ → A`ᵉ equippedᵉ with
[homotopies](foundation-core.homotopies.mdᵉ) `Sᵉ : fᵉ ∘ᵉ gᵉ ~ᵉ id`ᵉ andᵉ
`Rᵉ : gᵉ ∘ᵉ fᵉ ~ᵉ id`.ᵉ Suchᵉ data,ᵉ howeverᵉ isᵉ [structure](foundation.structure.mdᵉ) onᵉ
theᵉ mapᵉ `f`,ᵉ andᵉ notᵉ generallyᵉ aᵉ [property](foundation-core.propositions.md).ᵉ
Oneᵉ wayᵉ to makeᵉ theᵉ typeᵉ ofᵉ inversesᵉ intoᵉ aᵉ propertyᵉ isᵉ byᵉ addingᵉ aᵉ singleᵉ
coherenceᵉ conditionᵉ betweenᵉ theᵉ homotopiesᵉ ofᵉ theᵉ inverse,ᵉ askingᵉ thatᵉ theᵉ
followingᵉ diagramᵉ commmutesᵉ

```text
              Sᵉ ·rᵉ fᵉ
            --------->ᵉ
  fᵉ ∘ᵉ gᵉ ∘ᵉ fᵉ            f.ᵉ
            --------->ᵉ
              fᵉ ·lᵉ Rᵉ
```

Weᵉ callᵉ suchᵉ data aᵉ
{{#conceptᵉ "coherentlyᵉ invertibleᵉ map"ᵉ Agda=coherently-invertible-map}}.ᵉ I.e.,ᵉ aᵉ
coherentlyᵉ invertibleᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ aᵉ mapᵉ equippedᵉ with aᵉ two-sidedᵉ inverseᵉ
andᵉ thisᵉ additionalᵉ coherence.ᵉ

Thereᵉ isᵉ alsoᵉ theᵉ alternativeᵉ coherenceᵉ conditionᵉ weᵉ couldᵉ addᵉ

```text
              Rᵉ ·rᵉ gᵉ
            --------->ᵉ
  gᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ            g.ᵉ
            --------->ᵉ
              gᵉ ·lᵉ Sᵉ
```

Weᵉ willᵉ colloquiallyᵉ referᵉ to invertibleᵉ mapsᵉ equippedᵉ with thisᵉ coherenceᵉ asᵉ
_transposeᵉ coherentlyᵉ invertibleᵉ maps_.ᵉ

**Note.**ᵉ Coherentlyᵉ invertibleᵉ mapsᵉ areᵉ referredᵉ to asᵉ
{{#conceptᵉ "halfᵉ adjointᵉ equivalences"ᵉ}} in {{#citeᵉ UF13}}.ᵉ

Onᵉ thisᵉ pageᵉ weᵉ willᵉ proveᵉ thatᵉ everyᵉ two-sidedᵉ inverseᵉ `g`ᵉ ofᵉ `f`ᵉ canᵉ beᵉ
promotedᵉ to aᵉ coherentᵉ two-sidedᵉ inverse.ᵉ Thus,ᵉ forᵉ mostᵉ propertiesᵉ ofᵉ
coherentlyᵉ invertibleᵉ maps,ᵉ itᵉ sufficesᵉ to considerᵉ theᵉ data ofᵉ aᵉ two-sidedᵉ
inverse.ᵉ However,ᵉ thisᵉ coherenceᵉ constructionᵉ requiresᵉ usᵉ to replaceᵉ theᵉ sectionᵉ
homotopyᵉ (orᵉ retractionᵉ homotopy).ᵉ Forᵉ thisᵉ reasonᵉ weᵉ alsoᵉ giveᵉ directᵉ
constructionsᵉ showingᵉ

1.ᵉ Theᵉ identityᵉ mapᵉ isᵉ coherentlyᵉ invertible.ᵉ
2.ᵉ Theᵉ compositeᵉ ofᵉ twoᵉ coherentlyᵉ invertibleᵉ mapsᵉ isᵉ coherentlyᵉ invertible.ᵉ
3.ᵉ Theᵉ inverseᵉ ofᵉ aᵉ coherentlyᵉ invertibleᵉ mapᵉ isᵉ coherentlyᵉ invertible.ᵉ
4.ᵉ Everyᵉ mapᵉ homotopicᵉ to aᵉ coherentlyᵉ invertibleᵉ mapᵉ isᵉ coherentlyᵉ invertible.ᵉ
5.ᵉ Theᵉ 3-for-2ᵉ propertyᵉ ofᵉ coherentlyᵉ invertibleᵉ maps.ᵉ

Eachᵉ ofᵉ theseᵉ constructionsᵉ appropriatelyᵉ preserveᵉ theᵉ data ofᵉ theᵉ underlyingᵉ
two-sidedᵉ inverse.ᵉ

## Definition

### The predicate of being a coherently invertible map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  coherence-is-coherently-invertibleᵉ :
    (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Aᵉ) (Gᵉ : fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ) (Hᵉ : gᵉ ∘ᵉ fᵉ ~ᵉ idᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-is-coherently-invertibleᵉ fᵉ gᵉ Gᵉ Hᵉ = Gᵉ ·rᵉ fᵉ ~ᵉ fᵉ ·lᵉ Hᵉ

  is-coherently-invertibleᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-coherently-invertibleᵉ fᵉ =
    Σᵉ ( Bᵉ → Aᵉ)
      ( λ gᵉ →
        Σᵉ ( fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ)
          ( λ Gᵉ →
            Σᵉ ( gᵉ ∘ᵉ fᵉ ~ᵉ idᵉ)
              ( λ Hᵉ → coherence-is-coherently-invertibleᵉ fᵉ gᵉ Gᵉ Hᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  (Hᵉ : is-coherently-invertibleᵉ fᵉ)
  where

  map-inv-is-coherently-invertibleᵉ : Bᵉ → Aᵉ
  map-inv-is-coherently-invertibleᵉ = pr1ᵉ Hᵉ

  is-section-map-inv-is-coherently-invertibleᵉ :
    is-sectionᵉ fᵉ map-inv-is-coherently-invertibleᵉ
  is-section-map-inv-is-coherently-invertibleᵉ = pr1ᵉ (pr2ᵉ Hᵉ)

  is-retraction-map-inv-is-coherently-invertibleᵉ :
    is-retractionᵉ fᵉ map-inv-is-coherently-invertibleᵉ
  is-retraction-map-inv-is-coherently-invertibleᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Hᵉ))

  coh-is-coherently-invertibleᵉ :
    coherence-is-coherently-invertibleᵉ fᵉ
      ( map-inv-is-coherently-invertibleᵉ)
      ( is-section-map-inv-is-coherently-invertibleᵉ)
      ( is-retraction-map-inv-is-coherently-invertibleᵉ)
  coh-is-coherently-invertibleᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ Hᵉ))

  is-invertible-is-coherently-invertibleᵉ : is-invertibleᵉ fᵉ
  pr1ᵉ is-invertible-is-coherently-invertibleᵉ =
    map-inv-is-coherently-invertibleᵉ
  pr1ᵉ (pr2ᵉ is-invertible-is-coherently-invertibleᵉ) =
    is-section-map-inv-is-coherently-invertibleᵉ
  pr2ᵉ (pr2ᵉ is-invertible-is-coherently-invertibleᵉ) =
    is-retraction-map-inv-is-coherently-invertibleᵉ

  section-is-coherently-invertibleᵉ : sectionᵉ fᵉ
  pr1ᵉ section-is-coherently-invertibleᵉ =
    map-inv-is-coherently-invertibleᵉ
  pr2ᵉ section-is-coherently-invertibleᵉ =
    is-section-map-inv-is-coherently-invertibleᵉ

  retraction-is-coherently-invertibleᵉ : retractionᵉ fᵉ
  pr1ᵉ retraction-is-coherently-invertibleᵉ =
    map-inv-is-coherently-invertibleᵉ
  pr2ᵉ retraction-is-coherently-invertibleᵉ =
    is-retraction-map-inv-is-coherently-invertibleᵉ
```

Weᵉ willᵉ showᵉ thatᵉ `is-coherently-invertible`ᵉ isᵉ aᵉ propositionᵉ in
[`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).ᵉ

### The type of coherently invertible maps

```agda
coherently-invertible-mapᵉ : {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
coherently-invertible-mapᵉ Aᵉ Bᵉ = Σᵉ (Aᵉ → Bᵉ) (is-coherently-invertibleᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : coherently-invertible-mapᵉ Aᵉ Bᵉ)
  where

  map-coherently-invertible-mapᵉ : Aᵉ → Bᵉ
  map-coherently-invertible-mapᵉ = pr1ᵉ eᵉ

  is-coherently-invertible-map-coherently-invertible-mapᵉ :
    is-coherently-invertibleᵉ map-coherently-invertible-mapᵉ
  is-coherently-invertible-map-coherently-invertible-mapᵉ = pr2ᵉ eᵉ

  map-inv-coherently-invertible-mapᵉ : Bᵉ → Aᵉ
  map-inv-coherently-invertible-mapᵉ =
    map-inv-is-coherently-invertibleᵉ
      ( is-coherently-invertible-map-coherently-invertible-mapᵉ)

  is-section-map-inv-coherently-invertible-mapᵉ :
    map-coherently-invertible-mapᵉ ∘ᵉ map-inv-coherently-invertible-mapᵉ ~ᵉ idᵉ
  is-section-map-inv-coherently-invertible-mapᵉ =
    is-section-map-inv-is-coherently-invertibleᵉ
      ( is-coherently-invertible-map-coherently-invertible-mapᵉ)

  is-retraction-map-inv-coherently-invertible-mapᵉ :
    map-inv-coherently-invertible-mapᵉ ∘ᵉ map-coherently-invertible-mapᵉ ~ᵉ idᵉ
  is-retraction-map-inv-coherently-invertible-mapᵉ =
    is-retraction-map-inv-is-coherently-invertibleᵉ
      ( is-coherently-invertible-map-coherently-invertible-mapᵉ)

  coh-coherently-invertible-mapᵉ :
    coherence-is-coherently-invertibleᵉ
      ( map-coherently-invertible-mapᵉ)
      ( map-inv-coherently-invertible-mapᵉ)
      ( is-section-map-inv-coherently-invertible-mapᵉ)
      ( is-retraction-map-inv-coherently-invertible-mapᵉ)
  coh-coherently-invertible-mapᵉ =
    coh-is-coherently-invertibleᵉ
      ( is-coherently-invertible-map-coherently-invertible-mapᵉ)

  section-coherently-invertible-mapᵉ :
    sectionᵉ map-coherently-invertible-mapᵉ
  section-coherently-invertible-mapᵉ =
    section-is-coherently-invertibleᵉ
      ( is-coherently-invertible-map-coherently-invertible-mapᵉ)

  retraction-coherently-invertible-mapᵉ :
    retractionᵉ map-coherently-invertible-mapᵉ
  retraction-coherently-invertible-mapᵉ =
    retraction-is-coherently-invertibleᵉ
      ( is-coherently-invertible-map-coherently-invertible-mapᵉ)

  is-invertible-coherently-invertible-mapᵉ :
    is-invertibleᵉ map-coherently-invertible-mapᵉ
  is-invertible-coherently-invertible-mapᵉ =
    is-invertible-is-coherently-invertibleᵉ
      ( is-coherently-invertible-map-coherently-invertible-mapᵉ)

  invertible-map-coherently-invertible-mapᵉ : invertible-mapᵉ Aᵉ Bᵉ
  pr1ᵉ invertible-map-coherently-invertible-mapᵉ =
    map-coherently-invertible-mapᵉ
  pr2ᵉ invertible-map-coherently-invertible-mapᵉ =
    is-invertible-coherently-invertible-mapᵉ
```

### The predicate of being a transpose coherently invertible map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  coherence-is-transpose-coherently-invertibleᵉ :
    (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Aᵉ) (Gᵉ : fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ) (Hᵉ : gᵉ ∘ᵉ fᵉ ~ᵉ idᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-is-transpose-coherently-invertibleᵉ fᵉ gᵉ Gᵉ Hᵉ = Hᵉ ·rᵉ gᵉ ~ᵉ gᵉ ·lᵉ Gᵉ

  is-transpose-coherently-invertibleᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-transpose-coherently-invertibleᵉ fᵉ =
    Σᵉ ( Bᵉ → Aᵉ)
      ( λ gᵉ →
        Σᵉ ( fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ)
          ( λ Gᵉ →
            Σᵉ ( gᵉ ∘ᵉ fᵉ ~ᵉ idᵉ)
              ( λ Hᵉ → coherence-is-transpose-coherently-invertibleᵉ fᵉ gᵉ Gᵉ Hᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  (Hᵉ : is-transpose-coherently-invertibleᵉ fᵉ)
  where

  map-inv-is-transpose-coherently-invertibleᵉ : Bᵉ → Aᵉ
  map-inv-is-transpose-coherently-invertibleᵉ = pr1ᵉ Hᵉ

  is-section-map-inv-is-transpose-coherently-invertibleᵉ :
    fᵉ ∘ᵉ map-inv-is-transpose-coherently-invertibleᵉ ~ᵉ idᵉ
  is-section-map-inv-is-transpose-coherently-invertibleᵉ = pr1ᵉ (pr2ᵉ Hᵉ)

  is-retraction-map-inv-is-transpose-coherently-invertibleᵉ :
    map-inv-is-transpose-coherently-invertibleᵉ ∘ᵉ fᵉ ~ᵉ idᵉ
  is-retraction-map-inv-is-transpose-coherently-invertibleᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Hᵉ))

  coh-is-transpose-coherently-invertibleᵉ :
    coherence-is-transpose-coherently-invertibleᵉ fᵉ
      ( map-inv-is-transpose-coherently-invertibleᵉ)
      ( is-section-map-inv-is-transpose-coherently-invertibleᵉ)
      ( is-retraction-map-inv-is-transpose-coherently-invertibleᵉ)
  coh-is-transpose-coherently-invertibleᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ Hᵉ))

  is-invertible-is-transpose-coherently-invertibleᵉ : is-invertibleᵉ fᵉ
  pr1ᵉ is-invertible-is-transpose-coherently-invertibleᵉ =
    map-inv-is-transpose-coherently-invertibleᵉ
  pr1ᵉ (pr2ᵉ is-invertible-is-transpose-coherently-invertibleᵉ) =
    is-section-map-inv-is-transpose-coherently-invertibleᵉ
  pr2ᵉ (pr2ᵉ is-invertible-is-transpose-coherently-invertibleᵉ) =
    is-retraction-map-inv-is-transpose-coherently-invertibleᵉ

  section-is-transpose-coherently-invertibleᵉ : sectionᵉ fᵉ
  pr1ᵉ section-is-transpose-coherently-invertibleᵉ =
    map-inv-is-transpose-coherently-invertibleᵉ
  pr2ᵉ section-is-transpose-coherently-invertibleᵉ =
    is-section-map-inv-is-transpose-coherently-invertibleᵉ

  retraction-is-transpose-coherently-invertibleᵉ : retractionᵉ fᵉ
  pr1ᵉ retraction-is-transpose-coherently-invertibleᵉ =
    map-inv-is-transpose-coherently-invertibleᵉ
  pr2ᵉ retraction-is-transpose-coherently-invertibleᵉ =
    is-retraction-map-inv-is-transpose-coherently-invertibleᵉ
```

Weᵉ willᵉ showᵉ thatᵉ `is-transpose-coherently-invertible`ᵉ isᵉ aᵉ propositionᵉ in
[`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).ᵉ

### The type of transpose coherently invertible maps

```agda
transpose-coherently-invertible-mapᵉ :
  {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
transpose-coherently-invertible-mapᵉ Aᵉ Bᵉ =
  Σᵉ (Aᵉ → Bᵉ) (is-transpose-coherently-invertibleᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (eᵉ : transpose-coherently-invertible-mapᵉ Aᵉ Bᵉ)
  where

  map-transpose-coherently-invertible-mapᵉ : Aᵉ → Bᵉ
  map-transpose-coherently-invertible-mapᵉ = pr1ᵉ eᵉ

  is-transpose-coherently-invertible-map-transpose-coherently-invertible-mapᵉ :
    is-transpose-coherently-invertibleᵉ map-transpose-coherently-invertible-mapᵉ
  is-transpose-coherently-invertible-map-transpose-coherently-invertible-mapᵉ =
    pr2ᵉ eᵉ

  map-inv-transpose-coherently-invertible-mapᵉ : Bᵉ → Aᵉ
  map-inv-transpose-coherently-invertible-mapᵉ =
    map-inv-is-transpose-coherently-invertibleᵉ
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-mapᵉ)

  is-section-map-inv-transpose-coherently-invertible-mapᵉ :
    ( map-transpose-coherently-invertible-mapᵉ ∘ᵉ
      map-inv-transpose-coherently-invertible-mapᵉ) ~ᵉ
    ( idᵉ)
  is-section-map-inv-transpose-coherently-invertible-mapᵉ =
    is-section-map-inv-is-transpose-coherently-invertibleᵉ
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-mapᵉ)

  is-retraction-map-inv-transpose-coherently-invertible-mapᵉ :
    ( map-inv-transpose-coherently-invertible-mapᵉ ∘ᵉ
      map-transpose-coherently-invertible-mapᵉ) ~ᵉ
    ( idᵉ)
  is-retraction-map-inv-transpose-coherently-invertible-mapᵉ =
    is-retraction-map-inv-is-transpose-coherently-invertibleᵉ
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-mapᵉ)

  coh-transpose-coherently-invertible-mapᵉ :
    coherence-is-transpose-coherently-invertibleᵉ
      ( map-transpose-coherently-invertible-mapᵉ)
      ( map-inv-transpose-coherently-invertible-mapᵉ)
      ( is-section-map-inv-transpose-coherently-invertible-mapᵉ)
      ( is-retraction-map-inv-transpose-coherently-invertible-mapᵉ)
  coh-transpose-coherently-invertible-mapᵉ =
    coh-is-transpose-coherently-invertibleᵉ
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-mapᵉ)

  section-transpose-coherently-invertible-mapᵉ :
    sectionᵉ map-transpose-coherently-invertible-mapᵉ
  section-transpose-coherently-invertible-mapᵉ =
    section-is-transpose-coherently-invertibleᵉ
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-mapᵉ)

  retraction-transpose-coherently-invertible-mapᵉ :
    retractionᵉ map-transpose-coherently-invertible-mapᵉ
  retraction-transpose-coherently-invertible-mapᵉ =
    retraction-is-transpose-coherently-invertibleᵉ
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-mapᵉ)

  is-invertible-transpose-coherently-invertible-mapᵉ :
    is-invertibleᵉ map-transpose-coherently-invertible-mapᵉ
  is-invertible-transpose-coherently-invertible-mapᵉ =
    is-invertible-is-transpose-coherently-invertibleᵉ
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-mapᵉ)

  invertible-map-transpose-coherently-invertible-mapᵉ : invertible-mapᵉ Aᵉ Bᵉ
  pr1ᵉ invertible-map-transpose-coherently-invertible-mapᵉ =
    map-transpose-coherently-invertible-mapᵉ
  pr2ᵉ invertible-map-transpose-coherently-invertible-mapᵉ =
    is-invertible-transpose-coherently-invertible-mapᵉ
```

### Invertible maps that are coherent are coherently invertible maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  (Hᵉ : is-invertibleᵉ fᵉ)
  where

  coherence-is-invertibleᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-is-invertibleᵉ =
    coherence-is-coherently-invertibleᵉ
      ( fᵉ)
      ( map-inv-is-invertibleᵉ Hᵉ)
      ( is-section-map-inv-is-invertibleᵉ Hᵉ)
      ( is-retraction-map-inv-is-invertibleᵉ Hᵉ)

  transpose-coherence-is-invertibleᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  transpose-coherence-is-invertibleᵉ =
    coherence-is-transpose-coherently-invertibleᵉ
      ( fᵉ)
      ( map-inv-is-invertibleᵉ Hᵉ)
      ( is-section-map-inv-is-invertibleᵉ Hᵉ)
      ( is-retraction-map-inv-is-invertibleᵉ Hᵉ)

  is-coherently-invertible-coherence-is-invertibleᵉ :
    coherence-is-invertibleᵉ → is-coherently-invertibleᵉ fᵉ
  is-coherently-invertible-coherence-is-invertibleᵉ cohᵉ =
    ( map-inv-is-invertibleᵉ Hᵉ ,ᵉ
      is-section-map-inv-is-invertibleᵉ Hᵉ ,ᵉ
      is-retraction-map-inv-is-invertibleᵉ Hᵉ ,ᵉ
      cohᵉ)

  is-transpose-coherently-invertible-transpose-coherence-is-invertibleᵉ :
    transpose-coherence-is-invertibleᵉ → is-transpose-coherently-invertibleᵉ fᵉ
  is-transpose-coherently-invertible-transpose-coherence-is-invertibleᵉ cohᵉ =
    ( map-inv-is-invertibleᵉ Hᵉ ,ᵉ
      is-section-map-inv-is-invertibleᵉ Hᵉ ,ᵉ
      is-retraction-map-inv-is-invertibleᵉ Hᵉ ,ᵉ
      cohᵉ)
```

## Properties

### The inverse of a coherently invertible map is transpose coherently invertible and vice versa

Theᵉ inverseᵉ ofᵉ aᵉ coherentlyᵉ invertibleᵉ mapᵉ isᵉ transposeᵉ coherentlyᵉ invertible.ᵉ
Conversely,ᵉ theᵉ inverseᵉ ofᵉ aᵉ transposeᵉ coherentlyᵉ invertibleᵉ mapᵉ isᵉ coherentlyᵉ
invertible.ᵉ Sinceᵉ theseᵉ areᵉ definedᵉ byᵉ simplyᵉ movingᵉ data around,ᵉ theyᵉ areᵉ
strictᵉ inversesᵉ to oneᵉ another.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-transpose-coherently-invertible-map-inv-is-coherently-invertibleᵉ :
    {fᵉ : Aᵉ → Bᵉ} (Hᵉ : is-coherently-invertibleᵉ fᵉ) →
    is-transpose-coherently-invertibleᵉ (map-inv-is-coherently-invertibleᵉ Hᵉ)
  is-transpose-coherently-invertible-map-inv-is-coherently-invertibleᵉ {fᵉ} Hᵉ =
    ( fᵉ ,ᵉ
      is-retraction-map-inv-is-coherently-invertibleᵉ Hᵉ ,ᵉ
      is-section-map-inv-is-coherently-invertibleᵉ Hᵉ ,ᵉ
      coh-is-coherently-invertibleᵉ Hᵉ)

  is-coherently-invertible-map-inv-is-transpose-coherently-invertibleᵉ :
    {fᵉ : Aᵉ → Bᵉ} (Hᵉ : is-transpose-coherently-invertibleᵉ fᵉ) →
    is-coherently-invertibleᵉ (map-inv-is-transpose-coherently-invertibleᵉ Hᵉ)
  is-coherently-invertible-map-inv-is-transpose-coherently-invertibleᵉ {fᵉ} Hᵉ =
    ( fᵉ ,ᵉ
      is-retraction-map-inv-is-transpose-coherently-invertibleᵉ Hᵉ ,ᵉ
      is-section-map-inv-is-transpose-coherently-invertibleᵉ Hᵉ ,ᵉ
      coh-is-transpose-coherently-invertibleᵉ Hᵉ)

  transpose-coherently-invertible-map-inv-coherently-invertible-mapᵉ :
    coherently-invertible-mapᵉ Aᵉ Bᵉ → transpose-coherently-invertible-mapᵉ Bᵉ Aᵉ
  transpose-coherently-invertible-map-inv-coherently-invertible-mapᵉ eᵉ =
    ( map-inv-coherently-invertible-mapᵉ eᵉ ,ᵉ
      is-transpose-coherently-invertible-map-inv-is-coherently-invertibleᵉ
        ( is-coherently-invertible-map-coherently-invertible-mapᵉ eᵉ))

  coherently-invertible-map-inv-transpose-coherently-invertible-mapᵉ :
    transpose-coherently-invertible-mapᵉ Aᵉ Bᵉ → coherently-invertible-mapᵉ Bᵉ Aᵉ
  coherently-invertible-map-inv-transpose-coherently-invertible-mapᵉ eᵉ =
    ( map-inv-transpose-coherently-invertible-mapᵉ eᵉ ,ᵉ
      is-coherently-invertible-map-inv-is-transpose-coherently-invertibleᵉ
        ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-mapᵉ
          ( eᵉ)))
```

### Invertible maps are coherently invertible

Thisᵉ resultᵉ isᵉ knownᵉ asᵉ
[Vogt'sᵉ lemma](https://ncatlab.org/nlab/show/homotopy+equivalence#vogts_lemmaᵉ)
in point-setᵉ topology.ᵉ Theᵉ constructionᵉ followsᵉ Lemmaᵉ 10.4.5ᵉ in {{#citeᵉ Rij22}}.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} (Hᵉ : is-invertibleᵉ fᵉ)
  where

  is-retraction-map-inv-is-coherently-invertible-is-invertibleᵉ :
    map-inv-is-invertibleᵉ Hᵉ ∘ᵉ fᵉ ~ᵉ idᵉ
  is-retraction-map-inv-is-coherently-invertible-is-invertibleᵉ =
    is-retraction-map-inv-is-invertibleᵉ Hᵉ

  abstract
    is-section-map-inv-is-coherently-invertible-is-invertibleᵉ :
      fᵉ ∘ᵉ map-inv-is-invertibleᵉ Hᵉ ~ᵉ idᵉ
    is-section-map-inv-is-coherently-invertible-is-invertibleᵉ =
      ( ( inv-htpyᵉ (is-section-map-inv-is-invertibleᵉ Hᵉ)) ·rᵉ
        ( fᵉ ∘ᵉ map-inv-is-invertibleᵉ Hᵉ)) ∙hᵉ
      ( ( ( fᵉ) ·lᵉ
          ( is-retraction-map-inv-is-invertibleᵉ Hᵉ) ·rᵉ
          ( map-inv-is-invertibleᵉ Hᵉ)) ∙hᵉ
        ( is-section-map-inv-is-invertibleᵉ Hᵉ))

  abstract
    inv-coh-is-coherently-invertible-is-invertibleᵉ :
      fᵉ ·lᵉ is-retraction-map-inv-is-coherently-invertible-is-invertibleᵉ ~ᵉ
      is-section-map-inv-is-coherently-invertible-is-invertibleᵉ ·rᵉ fᵉ
    inv-coh-is-coherently-invertible-is-invertibleᵉ =
      left-transpose-htpy-concatᵉ
        ( ( is-section-map-inv-is-invertibleᵉ Hᵉ) ·rᵉ
          ( fᵉ ∘ᵉ map-inv-is-invertibleᵉ Hᵉ ∘ᵉ fᵉ))
        ( fᵉ ·lᵉ is-retraction-map-inv-is-invertibleᵉ Hᵉ)
        ( ( ( fᵉ) ·lᵉ
            ( is-retraction-map-inv-is-invertibleᵉ Hᵉ) ·rᵉ
            ( map-inv-is-invertibleᵉ Hᵉ ∘ᵉ fᵉ)) ∙hᵉ
          ( is-section-map-inv-is-invertibleᵉ Hᵉ ·rᵉ fᵉ))
        ( ( ( nat-htpyᵉ (is-section-map-inv-is-invertibleᵉ Hᵉ ·rᵉ fᵉ)) ·rᵉ
            ( is-retraction-map-inv-is-invertibleᵉ Hᵉ)) ∙hᵉ
          ( right-whisker-concat-htpyᵉ
            ( ( inv-preserves-comp-left-whisker-compᵉ
                ( fᵉ)
                ( map-inv-is-invertibleᵉ Hᵉ ∘ᵉ fᵉ)
                ( is-retraction-map-inv-is-invertibleᵉ Hᵉ)) ∙hᵉ
              ( left-whisker-comp²ᵉ
                ( fᵉ)
                ( inv-coh-htpy-idᵉ (is-retraction-map-inv-is-invertibleᵉ Hᵉ))))
            ( is-section-map-inv-is-invertibleᵉ Hᵉ ·rᵉ fᵉ)))

  abstract
    coh-is-coherently-invertible-is-invertibleᵉ :
      coherence-is-coherently-invertibleᵉ
        ( fᵉ)
        ( map-inv-is-invertibleᵉ Hᵉ)
        ( is-section-map-inv-is-coherently-invertible-is-invertibleᵉ)
        ( is-retraction-map-inv-is-coherently-invertible-is-invertibleᵉ)
    coh-is-coherently-invertible-is-invertibleᵉ =
      inv-htpyᵉ inv-coh-is-coherently-invertible-is-invertibleᵉ

  is-coherently-invertible-is-invertibleᵉ : is-coherently-invertibleᵉ fᵉ
  is-coherently-invertible-is-invertibleᵉ =
    ( map-inv-is-invertibleᵉ Hᵉ ,ᵉ
      is-section-map-inv-is-coherently-invertible-is-invertibleᵉ ,ᵉ
      is-retraction-map-inv-is-coherently-invertible-is-invertibleᵉ ,ᵉ
      coh-is-coherently-invertible-is-invertibleᵉ)
```

Weᵉ getᵉ theᵉ transposeᵉ versionᵉ forᵉ freeᵉ:

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} (Hᵉ : is-invertibleᵉ fᵉ)
  where

  is-transpose-coherently-invertible-is-invertibleᵉ :
    is-transpose-coherently-invertibleᵉ fᵉ
  is-transpose-coherently-invertible-is-invertibleᵉ =
    is-transpose-coherently-invertible-map-inv-is-coherently-invertibleᵉ
      ( is-coherently-invertible-is-invertibleᵉ
        ( is-invertible-map-inv-is-invertibleᵉ Hᵉ))
```

### Coherently invertible maps are injective

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  is-injective-is-coherently-invertibleᵉ :
    (Hᵉ : is-coherently-invertibleᵉ fᵉ) {xᵉ yᵉ : Aᵉ} → fᵉ xᵉ ＝ᵉ fᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  is-injective-is-coherently-invertibleᵉ Hᵉ =
    is-injective-is-invertibleᵉ
      ( is-invertible-is-coherently-invertibleᵉ Hᵉ)

  is-injective-is-transpose-coherently-invertibleᵉ :
    (Hᵉ : is-transpose-coherently-invertibleᵉ fᵉ) {xᵉ yᵉ : Aᵉ} → fᵉ xᵉ ＝ᵉ fᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  is-injective-is-transpose-coherently-invertibleᵉ Hᵉ =
    is-injective-is-invertibleᵉ
      ( is-invertible-is-transpose-coherently-invertibleᵉ Hᵉ)
```

### Coherently invertible maps are embeddings

Weᵉ showᵉ thatᵉ `is-injective-is-coherently-invertible`ᵉ isᵉ aᵉ
[section](foundation-core.sections.mdᵉ) andᵉ
[retraction](foundation-core.retractions.mdᵉ) ofᵉ `apᵉ f`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  (Hᵉ : is-coherently-invertibleᵉ fᵉ) {xᵉ yᵉ : Aᵉ}
  where

  abstract
    is-section-is-injective-is-coherently-invertibleᵉ :
      apᵉ fᵉ {xᵉ} {yᵉ} ∘ᵉ is-injective-is-coherently-invertibleᵉ Hᵉ ~ᵉ idᵉ
    is-section-is-injective-is-coherently-invertibleᵉ pᵉ =
      ( ap-concatᵉ fᵉ
        ( invᵉ (is-retraction-map-inv-is-coherently-invertibleᵉ Hᵉ xᵉ))
        ( ( apᵉ (map-inv-is-coherently-invertibleᵉ Hᵉ) pᵉ) ∙ᵉ
          ( is-retraction-map-inv-is-coherently-invertibleᵉ Hᵉ yᵉ))) ∙ᵉ
      ( ap-binaryᵉ
        ( _∙ᵉ_)
        ( ap-invᵉ fᵉ (is-retraction-map-inv-is-coherently-invertibleᵉ Hᵉ xᵉ))
        ( ( ap-concatᵉ fᵉ
            ( apᵉ (map-inv-is-coherently-invertibleᵉ Hᵉ) pᵉ)
            ( is-retraction-map-inv-is-coherently-invertibleᵉ Hᵉ yᵉ)) ∙ᵉ
          ( ap-binaryᵉ
            ( _∙ᵉ_)
            ( invᵉ (ap-compᵉ fᵉ (map-inv-is-coherently-invertibleᵉ Hᵉ) pᵉ))
            ( invᵉ (coh-is-coherently-invertibleᵉ Hᵉ yᵉ))))) ∙ᵉ
      ( invᵉ
        ( left-transpose-eq-concatᵉ
          ( apᵉ fᵉ (is-retraction-map-inv-is-coherently-invertibleᵉ Hᵉ xᵉ))
          ( pᵉ)
          ( ( apᵉ (fᵉ ∘ᵉ map-inv-is-coherently-invertibleᵉ Hᵉ) pᵉ) ∙ᵉ
            ( is-section-map-inv-is-coherently-invertibleᵉ Hᵉ (fᵉ yᵉ)))
          ( ( ap-binaryᵉ
              ( _∙ᵉ_)
              ( invᵉ (coh-is-coherently-invertibleᵉ Hᵉ xᵉ))
              ( invᵉ (ap-idᵉ pᵉ))) ∙ᵉ
            ( nat-htpyᵉ (is-section-map-inv-is-coherently-invertibleᵉ Hᵉ) pᵉ))))

  abstract
    is-retraction-is-injective-is-coherently-invertibleᵉ :
      is-injective-is-coherently-invertibleᵉ Hᵉ ∘ᵉ apᵉ fᵉ {xᵉ} {yᵉ} ~ᵉ idᵉ
    is-retraction-is-injective-is-coherently-invertibleᵉ reflᵉ =
      left-invᵉ (is-retraction-map-inv-is-coherently-invertibleᵉ Hᵉ xᵉ)

  is-invertible-ap-is-coherently-invertibleᵉ : is-invertibleᵉ (apᵉ fᵉ {xᵉ} {yᵉ})
  is-invertible-ap-is-coherently-invertibleᵉ =
    ( is-injective-is-coherently-invertibleᵉ Hᵉ ,ᵉ
      is-section-is-injective-is-coherently-invertibleᵉ ,ᵉ
      is-retraction-is-injective-is-coherently-invertibleᵉ)

  is-coherently-invertible-ap-is-coherently-invertibleᵉ :
    is-coherently-invertibleᵉ (apᵉ fᵉ {xᵉ} {yᵉ})
  is-coherently-invertible-ap-is-coherently-invertibleᵉ =
    is-coherently-invertible-is-invertibleᵉ
      ( is-invertible-ap-is-coherently-invertibleᵉ)
```

### Coherently invertible maps are transpose coherently invertible

Theᵉ proofᵉ followsᵉ Lemmaᵉ 4.2.2ᵉ in {{#citeᵉ UF13}}.ᵉ

**Proof.**ᵉ Byᵉ naturalityᵉ ofᵉ homotopiesᵉ weᵉ haveᵉ

```text
                   gfRgᵉ
     gfgfgᵉ -------------------->ᵉ gfgᵉ
       |                          |
  Rgfgᵉ |  nat-htpyᵉ Rᵉ ·rᵉ (Rᵉ ·rᵉ gᵉ)  | Rgᵉ
       ∨ᵉ                          ∨ᵉ
      gfgᵉ ---------------------->ᵉ g.ᵉ
                    Rgᵉ
```

Weᵉ canᵉ pasteᵉ theᵉ homotopyᵉ

```text
  gᵉ (inv-coh-htpy-idᵉ Sᵉ) ∙ᵉ gHgᵉ : Sgfgᵉ ~ᵉ gfSgᵉ ~ᵉ gfRgᵉ
```

alongᵉ theᵉ topᵉ edgeᵉ ofᵉ thisᵉ naturalityᵉ squareᵉ obtainingᵉ theᵉ coherenceᵉ squareᵉ

```text
             gfgSᵉ
     gfgfgᵉ ------->ᵉ gfgᵉ
       |             |
  Rgfgᵉ |             | Rgᵉ
       ∨ᵉ             ∨ᵉ
      gfgᵉ --------->ᵉ g.ᵉ
              Rgᵉ
```

Thereᵉ isᵉ alsoᵉ theᵉ naturalityᵉ squareᵉ

```text
                   gfgSᵉ
     gfgfgᵉ -------------------->ᵉ gfgᵉ
       |                          |
  Rgfgᵉ |  nat-htpyᵉ (Rᵉ ·rᵉ gᵉ) ·rᵉ Sᵉ  | Rgᵉ
       ∨ᵉ                          ∨ᵉ
      gfgᵉ ---------------------->ᵉ g.ᵉ
                    gSᵉ
```

Now,ᵉ byᵉ pastingᵉ theseᵉ alongᵉ theᵉ commonᵉ edgeᵉ `Rgfg`,ᵉ weᵉ obtainᵉ

```text
            gfgSᵉ           gfgSᵉ
      gfgᵉ <-------ᵉ gfgfgᵉ ------->ᵉ gfgᵉ
       |             |             |
    Rgᵉ |             | Rgfgᵉ        | Rgᵉ
       ∨ᵉ             ∨ᵉ             ∨ᵉ
       gᵉ <---------ᵉ gfgᵉ -------->ᵉ gmᵉ
             Rgᵉ             gSᵉ
```

Afterᵉ cancellingᵉ `gfgS`ᵉ andᵉ `Rg`ᵉ with themselves,ᵉ weᵉ areᵉ leftᵉ with `Rgᵉ ~ᵉ gS`ᵉ asᵉ
desired.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → Bᵉ)
  (gᵉ : Bᵉ → Aᵉ)
  (Sᵉ : is-sectionᵉ fᵉ gᵉ)
  (Rᵉ : is-retractionᵉ fᵉ gᵉ)
  (Hᵉ : coherence-is-coherently-invertibleᵉ fᵉ gᵉ Sᵉ Rᵉ)
  where

  abstract
    coh-transposition-coherence-is-coherently-invertibleᵉ :
      (gᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ) ·lᵉ Sᵉ ~ᵉ (gᵉ ∘ᵉ fᵉ) ·lᵉ Rᵉ ·rᵉ gᵉ
    coh-transposition-coherence-is-coherently-invertibleᵉ =
      ( inv-preserves-comp-left-whisker-compᵉ gᵉ (fᵉ ∘ᵉ gᵉ) Sᵉ) ∙hᵉ
      ( left-whisker-comp²ᵉ gᵉ (inv-coh-htpy-idᵉ Sᵉ)) ∙hᵉ
      ( double-whisker-comp²ᵉ gᵉ Hᵉ gᵉ) ∙hᵉ
      ( preserves-comp-left-whisker-compᵉ gᵉ fᵉ (Rᵉ ·rᵉ gᵉ))

  abstract
    naturality-square-transposition-coherence-is-coherently-invertibleᵉ :
      coherence-square-homotopiesᵉ
        ( Rᵉ ·rᵉ (gᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ))
        ( (gᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ) ·lᵉ Sᵉ)
        ( Rᵉ ·rᵉ gᵉ)
        ( Rᵉ ·rᵉ gᵉ)
    naturality-square-transposition-coherence-is-coherently-invertibleᵉ =
      ( ap-concat-htpy'ᵉ
        ( Rᵉ ·rᵉ gᵉ)
        ( coh-transposition-coherence-is-coherently-invertibleᵉ)) ∙hᵉ
      ( inv-htpyᵉ (nat-htpyᵉ Rᵉ ·rᵉ (Rᵉ ·rᵉ gᵉ))) ∙hᵉ
      ( ap-concat-htpyᵉ
        ( Rᵉ ·rᵉ (gᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ))
        ( left-unit-law-left-whisker-compᵉ (Rᵉ ·rᵉ gᵉ)))

  abstract
    coherence-transposition-coherence-is-coherently-invertibleᵉ :
      coherence-is-transpose-coherently-invertibleᵉ fᵉ gᵉ Sᵉ Rᵉ
    coherence-transposition-coherence-is-coherently-invertibleᵉ =
      ( ap-concat-htpy'ᵉ
        ( Rᵉ ·rᵉ gᵉ)
        ( inv-htpyᵉ (left-inv-htpyᵉ ((gᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ) ·lᵉ Sᵉ)))) ∙hᵉ
      ( assoc-htpyᵉ (inv-htpyᵉ ((gᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ) ·lᵉ Sᵉ)) ((gᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ) ·lᵉ Sᵉ) (Rᵉ ·rᵉ gᵉ)) ∙hᵉ
      ( ap-concat-htpyᵉ
        ( inv-htpyᵉ ((gᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ) ·lᵉ Sᵉ))
        ( inv-htpyᵉ (nat-htpyᵉ (Rᵉ ·rᵉ gᵉ) ·rᵉ Sᵉ))) ∙hᵉ
      ( inv-htpyᵉ
        ( assoc-htpyᵉ
          ( inv-htpyᵉ ((gᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ) ·lᵉ Sᵉ))
          ( Rᵉ ·rᵉ (gᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ))
          ( gᵉ ·lᵉ Sᵉ))) ∙hᵉ
      ( ap-concat-htpy'ᵉ
        ( gᵉ ·lᵉ Sᵉ)
        ( ( vertical-inv-coherence-square-homotopiesᵉ
            ( Rᵉ ·rᵉ (gᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ)) ((gᵉ ∘ᵉ fᵉ ∘ᵉ gᵉ) ·lᵉ Sᵉ) (Rᵉ ·rᵉ gᵉ) (Rᵉ ·rᵉ gᵉ)
            ( naturality-square-transposition-coherence-is-coherently-invertibleᵉ)) ∙hᵉ
          ( right-inv-htpyᵉ (Rᵉ ·rᵉ gᵉ))))
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  coherence-transposition-is-coherently-invertibleᵉ :
    (Hᵉ : is-coherently-invertibleᵉ fᵉ) →
    coherence-is-transpose-coherently-invertibleᵉ
      ( fᵉ)
      ( map-inv-is-coherently-invertibleᵉ Hᵉ)
      ( is-section-map-inv-is-coherently-invertibleᵉ Hᵉ)
      ( is-retraction-map-inv-is-coherently-invertibleᵉ Hᵉ)
  coherence-transposition-is-coherently-invertibleᵉ
    ( gᵉ ,ᵉ Sᵉ ,ᵉ Rᵉ ,ᵉ Hᵉ) =
    coherence-transposition-coherence-is-coherently-invertibleᵉ fᵉ gᵉ Sᵉ Rᵉ Hᵉ

  transposition-is-coherently-invertibleᵉ :
    is-coherently-invertibleᵉ fᵉ → is-transpose-coherently-invertibleᵉ fᵉ
  transposition-is-coherently-invertibleᵉ Hᵉ =
    is-transpose-coherently-invertible-transpose-coherence-is-invertibleᵉ
      ( is-invertible-is-coherently-invertibleᵉ Hᵉ)
      ( coherence-transposition-is-coherently-invertibleᵉ Hᵉ)
```

### Transpose coherently invertible maps are coherently invertible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  coherence-transposition-is-transpose-coherently-invertibleᵉ :
    (Hᵉ : is-transpose-coherently-invertibleᵉ fᵉ) →
    coherence-is-coherently-invertibleᵉ
      ( fᵉ)
      ( map-inv-is-transpose-coherently-invertibleᵉ Hᵉ)
      ( is-section-map-inv-is-transpose-coherently-invertibleᵉ Hᵉ)
      ( is-retraction-map-inv-is-transpose-coherently-invertibleᵉ Hᵉ)
  coherence-transposition-is-transpose-coherently-invertibleᵉ Hᵉ =
    coherence-transposition-is-coherently-invertibleᵉ
      ( is-coherently-invertible-map-inv-is-transpose-coherently-invertibleᵉ Hᵉ)

  transposition-is-transpose-coherently-invertibleᵉ :
    is-transpose-coherently-invertibleᵉ fᵉ → is-coherently-invertibleᵉ fᵉ
  transposition-is-transpose-coherently-invertibleᵉ Hᵉ =
    is-coherently-invertible-coherence-is-invertibleᵉ
      ( is-invertible-is-transpose-coherently-invertibleᵉ Hᵉ)
      ( coherence-transposition-is-transpose-coherently-invertibleᵉ Hᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  transposition-coherently-invertible-mapᵉ :
    coherently-invertible-mapᵉ Aᵉ Bᵉ → transpose-coherently-invertible-mapᵉ Aᵉ Bᵉ
  transposition-coherently-invertible-mapᵉ (fᵉ ,ᵉ Hᵉ) =
    ( fᵉ ,ᵉ transposition-is-coherently-invertibleᵉ Hᵉ)

  transposition-transpose-coherently-invertible-mapᵉ :
    transpose-coherently-invertible-mapᵉ Aᵉ Bᵉ → coherently-invertible-mapᵉ Aᵉ Bᵉ
  transposition-transpose-coherently-invertible-mapᵉ (fᵉ ,ᵉ Hᵉ) =
    ( fᵉ ,ᵉ transposition-is-transpose-coherently-invertibleᵉ Hᵉ)
```

### Coherently invertible maps are closed under homotopies

**Proof.**ᵉ Assumeᵉ givenᵉ aᵉ coherentlyᵉ invertibleᵉ mapᵉ `f`ᵉ with inverseᵉ `g`,ᵉ
homotopiesᵉ `Sᵉ : fᵉ ∘ᵉ gᵉ ~ᵉ id`,ᵉ `Rᵉ : gᵉ ∘ᵉ fᵉ ~ᵉ id`ᵉ andᵉ coherenceᵉ `Cᵉ : Sfᵉ ~ᵉ fR`.ᵉ
Moreover,ᵉ assumeᵉ theᵉ mapᵉ `f'`ᵉ isᵉ homotopicᵉ to `f`ᵉ with homotopyᵉ `Hᵉ : f'ᵉ ~ᵉ f`.ᵉ
Thenᵉ `g`ᵉ isᵉ alsoᵉ aᵉ two-sidedᵉ inverseᵉ to `f'`ᵉ viaᵉ theᵉ homotopiesᵉ

```text
  S'ᵉ :=ᵉ Hgᵉ ∙ᵉ Sᵉ : f'ᵉ ∘ᵉ gᵉ ~ᵉ idᵉ    andᵉ    R'ᵉ :=ᵉ gHᵉ ∙ᵉ Rᵉ : gᵉ ∘ᵉ f'ᵉ ~ᵉ id.ᵉ
```

Moreover,ᵉ theseᵉ witnessesᵉ areᵉ partᵉ ofᵉ aᵉ coherentᵉ inverseᵉ to `f'`.ᵉ Toᵉ showᵉ this,ᵉ
weᵉ mustᵉ constructᵉ aᵉ coherenceᵉ `C'`ᵉ ofᵉ theᵉ squareᵉ

```text
           Hgf'ᵉ
    f'gf'ᵉ ----->ᵉ f'gfᵉ
      |           |
 f'gHᵉ |           | Sf'ᵉ
      ∨ᵉ           ∨ᵉ
    f'gfᵉ ------->ᵉ f'.ᵉ
           f'Rᵉ
```

Weᵉ beginᵉ byᵉ observingᵉ thatᵉ `C`ᵉ fitsᵉ somewhereᵉ alongᵉ theᵉ diagonalᵉ ofᵉ thisᵉ squareᵉ
viaᵉ theᵉ compositeᵉ

```text
                        Sfᵉ
            HgHᵉ       ------>ᵉ     H⁻¹ᵉ
    f'gf'ᵉ ------>ᵉ fgfᵉ    Cᵉ    fᵉ ------>ᵉ f'.ᵉ
                      ------>ᵉ
                        fRᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ f'ᵉ : Aᵉ → Bᵉ} (Hᵉ : f'ᵉ ~ᵉ fᵉ)
  (gᵉ : Bᵉ → Aᵉ) (Sᵉ : fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ) (Rᵉ : gᵉ ∘ᵉ fᵉ ~ᵉ idᵉ) (Cᵉ : Sᵉ ·rᵉ fᵉ ~ᵉ fᵉ ·lᵉ Rᵉ)
  where

  coh-coh-is-coherently-invertible-htpyᵉ :
    horizontal-concat-htpy'ᵉ (Hᵉ ·rᵉ gᵉ) Hᵉ ∙hᵉ (Sᵉ ·rᵉ fᵉ ∙hᵉ inv-htpyᵉ Hᵉ) ~ᵉ
    horizontal-concat-htpy'ᵉ (Hᵉ ·rᵉ gᵉ) Hᵉ ∙hᵉ (fᵉ ·lᵉ Rᵉ ∙hᵉ inv-htpyᵉ Hᵉ)
  coh-coh-is-coherently-invertible-htpyᵉ =
    left-whisker-concat-htpyᵉ
      ( horizontal-concat-htpy'ᵉ (Hᵉ ·rᵉ gᵉ) Hᵉ)
      ( right-whisker-concat-htpyᵉ Cᵉ (inv-htpyᵉ Hᵉ))
```

Nowᵉ theᵉ problemᵉ isᵉ reducedᵉ to constructingᵉ twoᵉ homotopiesᵉ

```text
  Hgf'ᵉ ∙ᵉ Sf'ᵉ ~ᵉ HgHᵉ ∙ᵉ Sfᵉ ∙ᵉ H⁻¹ᵉ    andᵉ    f'gHᵉ ∙ᵉ f'Rᵉ ~ᵉ HgHᵉ ∙ᵉ fRᵉ ∙ᵉ H⁻¹.ᵉ
```

Byᵉ theᵉ twoᵉ equivalentᵉ constructionsᵉ ofᵉ theᵉ horizontalᵉ compositeᵉ `HgH`ᵉ

```text
    Hgf'ᵉ ∙ᵉ fgHᵉ ~ᵉ HgHᵉ ~ᵉ f'gHᵉ ∙ᵉ Hgfᵉ
```

constructingᵉ theᵉ twoᵉ homotopiesᵉ isᵉ equivalentᵉ to constructingᵉ coherencesᵉ ofᵉ theᵉ
squaresᵉ

```text
            fgHᵉ                        Hgfᵉ
     fgf'ᵉ ------->ᵉ fgfᵉ          f'gfᵉ ------->ᵉ fgfᵉ
      |             |            |             |
  Sf'ᵉ |             | Sfᵉ     f'Rᵉ |             | fRᵉ
      ∨ᵉ             ∨ᵉ            ∨ᵉ             ∨ᵉ
      f'ᵉ --------->ᵉ fᵉ            f'ᵉ --------->ᵉ f.ᵉ
             Hᵉ                          Hᵉ
```

However,ᵉ theseᵉ squaresᵉ areᵉ naturalityᵉ squares,ᵉ soᵉ weᵉ areᵉ done.ᵉ

```agda
  coh-section-is-coherently-invertible-htpyᵉ :
    (Hᵉ ·rᵉ gᵉ ∙hᵉ Sᵉ) ·rᵉ f'ᵉ ~ᵉ
    horizontal-concat-htpy'ᵉ (Hᵉ ·rᵉ gᵉ) Hᵉ ∙hᵉ ((Sᵉ ·rᵉ fᵉ) ∙hᵉ inv-htpyᵉ Hᵉ)
  coh-section-is-coherently-invertible-htpyᵉ =
    ( left-whisker-concat-htpyᵉ
      ( Hᵉ ·rᵉ (gᵉ ∘ᵉ f'ᵉ))
      ( right-transpose-htpy-concatᵉ (Sᵉ ·rᵉ f'ᵉ) Hᵉ ((fᵉ ∘ᵉ gᵉ) ·lᵉ Hᵉ ∙hᵉ Sᵉ ·rᵉ fᵉ)
        ( ( ap-concat-htpyᵉ
            ( Sᵉ ·rᵉ f'ᵉ)
            ( inv-htpyᵉ (left-unit-law-left-whisker-compᵉ Hᵉ))) ∙hᵉ
          ( nat-htpyᵉ Sᵉ ·rᵉ Hᵉ)))) ∙hᵉ
    ( ( ap-concat-htpyᵉ
        ( Hᵉ ·rᵉ (gᵉ ∘ᵉ f'ᵉ))
        ( assoc-htpyᵉ ((fᵉ ∘ᵉ gᵉ) ·lᵉ Hᵉ) (Sᵉ ·rᵉ fᵉ) (inv-htpyᵉ Hᵉ))) ∙hᵉ
      ( inv-htpyᵉ
        ( assoc-htpyᵉ (Hᵉ ·rᵉ (gᵉ ∘ᵉ f'ᵉ)) ((fᵉ ∘ᵉ gᵉ) ·lᵉ Hᵉ) ((Sᵉ ·rᵉ fᵉ) ∙hᵉ inv-htpyᵉ Hᵉ))))

  coh-retraction-is-coherently-invertible-htpyᵉ :
    horizontal-concat-htpy'ᵉ (Hᵉ ·rᵉ gᵉ) Hᵉ ∙hᵉ ((fᵉ ·lᵉ Rᵉ) ∙hᵉ inv-htpyᵉ Hᵉ) ~ᵉ
    f'ᵉ ·lᵉ ((gᵉ ·lᵉ Hᵉ) ∙hᵉ Rᵉ)
  coh-retraction-is-coherently-invertible-htpyᵉ =
    ( ap-concat-htpy'ᵉ
      ( fᵉ ·lᵉ Rᵉ ∙hᵉ inv-htpyᵉ Hᵉ)
      ( coh-horizontal-concat-htpyᵉ (Hᵉ ·rᵉ gᵉ) Hᵉ)) ∙hᵉ
    ( assoc-htpyᵉ ((f'ᵉ ∘ᵉ gᵉ) ·lᵉ Hᵉ) (Hᵉ ·rᵉ (gᵉ ∘ᵉ fᵉ)) (fᵉ ·lᵉ Rᵉ ∙hᵉ inv-htpyᵉ Hᵉ)) ∙hᵉ
    ( ap-concat-htpyᵉ
      ( (f'ᵉ ∘ᵉ gᵉ) ·lᵉ Hᵉ)
      ( inv-htpyᵉ (assoc-htpyᵉ (Hᵉ ·rᵉ (gᵉ ∘ᵉ fᵉ)) (fᵉ ·lᵉ Rᵉ) (inv-htpyᵉ Hᵉ)))) ∙hᵉ
    ( left-whisker-concat-htpyᵉ
      ( (f'ᵉ ∘ᵉ gᵉ) ·lᵉ Hᵉ)
      ( inv-htpyᵉ
        ( right-transpose-htpy-concatᵉ (f'ᵉ ·lᵉ Rᵉ) Hᵉ ((Hᵉ ·rᵉ (gᵉ ∘ᵉ fᵉ) ∙hᵉ fᵉ ·lᵉ Rᵉ))
          ( inv-htpyᵉ (nat-htpyᵉ Hᵉ ·rᵉ Rᵉ))))) ∙hᵉ
    ( ap-concat-htpy'ᵉ
      ( f'ᵉ ·lᵉ Rᵉ)
      ( inv-preserves-comp-left-whisker-compᵉ f'ᵉ gᵉ Hᵉ)) ∙hᵉ
    ( inv-htpyᵉ (distributive-left-whisker-comp-concatᵉ f'ᵉ (gᵉ ·lᵉ Hᵉ) Rᵉ))
```

Finally,ᵉ weᵉ concatenateᵉ theᵉ threeᵉ coherencesᵉ to obtainᵉ ourᵉ desiredᵉ result.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ f'ᵉ : Aᵉ → Bᵉ}
  where

  abstract
    coh-is-coherently-invertible-htpyᵉ :
      (Hᵉ : f'ᵉ ~ᵉ fᵉ) (Fᵉ : is-coherently-invertibleᵉ fᵉ) →
      coherence-is-coherently-invertibleᵉ
        ( f'ᵉ)
        ( map-inv-is-coherently-invertibleᵉ Fᵉ)
        ( is-section-map-inv-is-invertible-htpyᵉ
          ( Hᵉ)
          ( is-invertible-is-coherently-invertibleᵉ Fᵉ))
        ( is-retraction-map-inv-is-invertible-htpyᵉ
          ( Hᵉ)
          ( is-invertible-is-coherently-invertibleᵉ Fᵉ))
    coh-is-coherently-invertible-htpyᵉ Hᵉ Fᵉ =
      ( coh-section-is-coherently-invertible-htpyᵉ Hᵉ
        ( map-inv-is-coherently-invertibleᵉ Fᵉ)
        ( is-section-map-inv-is-coherently-invertibleᵉ Fᵉ)
        ( is-retraction-map-inv-is-coherently-invertibleᵉ Fᵉ)
        ( coh-is-coherently-invertibleᵉ Fᵉ)) ∙hᵉ
      ( coh-coh-is-coherently-invertible-htpyᵉ Hᵉ
        ( map-inv-is-coherently-invertibleᵉ Fᵉ)
        ( is-section-map-inv-is-coherently-invertibleᵉ Fᵉ)
        ( is-retraction-map-inv-is-coherently-invertibleᵉ Fᵉ)
        ( coh-is-coherently-invertibleᵉ Fᵉ)) ∙hᵉ
      ( coh-retraction-is-coherently-invertible-htpyᵉ Hᵉ
        ( map-inv-is-coherently-invertibleᵉ Fᵉ)
        ( is-section-map-inv-is-coherently-invertibleᵉ Fᵉ)
        ( is-retraction-map-inv-is-coherently-invertibleᵉ Fᵉ)
        ( coh-is-coherently-invertibleᵉ Fᵉ))

  is-coherently-invertible-htpyᵉ :
    f'ᵉ ~ᵉ fᵉ → is-coherently-invertibleᵉ fᵉ → is-coherently-invertibleᵉ f'ᵉ
  is-coherently-invertible-htpyᵉ Hᵉ Fᵉ =
    is-coherently-invertible-coherence-is-invertibleᵉ
      ( is-invertible-htpyᵉ Hᵉ (is-invertible-is-coherently-invertibleᵉ Fᵉ))
      ( coh-is-coherently-invertible-htpyᵉ Hᵉ Fᵉ)

  is-coherently-invertible-inv-htpyᵉ :
    fᵉ ~ᵉ f'ᵉ → is-coherently-invertibleᵉ fᵉ → is-coherently-invertibleᵉ f'ᵉ
  is-coherently-invertible-inv-htpyᵉ Hᵉ =
    is-coherently-invertible-htpyᵉ (inv-htpyᵉ Hᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  is-coherently-invertible-htpy-coherently-invertible-mapᵉ :
    (eᵉ : coherently-invertible-mapᵉ Aᵉ Bᵉ) →
    fᵉ ~ᵉ map-coherently-invertible-mapᵉ eᵉ →
    is-coherently-invertibleᵉ fᵉ
  is-coherently-invertible-htpy-coherently-invertible-mapᵉ (eᵉ ,ᵉ Eᵉ) Hᵉ =
    is-coherently-invertible-htpyᵉ Hᵉ Eᵉ

  is-coherently-invertible-inv-htpy-coherently-invertible-mapᵉ :
    (eᵉ : coherently-invertible-mapᵉ Aᵉ Bᵉ) →
    map-coherently-invertible-mapᵉ eᵉ ~ᵉ fᵉ →
    is-coherently-invertibleᵉ fᵉ
  is-coherently-invertible-inv-htpy-coherently-invertible-mapᵉ (eᵉ ,ᵉ Eᵉ) Hᵉ =
    is-coherently-invertible-inv-htpyᵉ Hᵉ Eᵉ
```

### The identity map is coherently invertible

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-coherently-invertible-idᵉ :
    is-coherently-invertibleᵉ (idᵉ {Aᵉ = Aᵉ})
  is-coherently-invertible-idᵉ =
    is-coherently-invertible-coherence-is-invertibleᵉ is-invertible-idᵉ refl-htpyᵉ

  id-coherently-invertible-mapᵉ : coherently-invertible-mapᵉ Aᵉ Aᵉ
  id-coherently-invertible-mapᵉ =
    ( idᵉ ,ᵉ is-coherently-invertible-idᵉ)

  is-transpose-coherently-invertible-idᵉ :
    is-transpose-coherently-invertibleᵉ (idᵉ {Aᵉ = Aᵉ})
  is-transpose-coherently-invertible-idᵉ =
    is-transpose-coherently-invertible-map-inv-is-coherently-invertibleᵉ
      ( is-coherently-invertible-idᵉ)

  id-transpose-coherently-invertible-mapᵉ :
    transpose-coherently-invertible-mapᵉ Aᵉ Aᵉ
  id-transpose-coherently-invertible-mapᵉ =
    ( idᵉ ,ᵉ is-transpose-coherently-invertible-idᵉ)
```

### Inversion of coherently invertible maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-coherently-invertible-map-inv-is-coherently-invertibleᵉ :
    {fᵉ : Aᵉ → Bᵉ} (Hᵉ : is-coherently-invertibleᵉ fᵉ) →
    is-coherently-invertibleᵉ (map-inv-is-coherently-invertibleᵉ Hᵉ)
  is-coherently-invertible-map-inv-is-coherently-invertibleᵉ Hᵉ =
    is-coherently-invertible-map-inv-is-transpose-coherently-invertibleᵉ
      ( transposition-is-coherently-invertibleᵉ Hᵉ)

  is-transpose-coherently-invertible-map-inv-is-transpose-coherently-invertibleᵉ :
    {fᵉ : Aᵉ → Bᵉ} (Hᵉ : is-transpose-coherently-invertibleᵉ fᵉ) →
    is-transpose-coherently-invertibleᵉ
      ( map-inv-is-transpose-coherently-invertibleᵉ Hᵉ)
  is-transpose-coherently-invertible-map-inv-is-transpose-coherently-invertibleᵉ
    Hᵉ =
    transposition-is-coherently-invertibleᵉ
      ( is-coherently-invertible-map-inv-is-transpose-coherently-invertibleᵉ Hᵉ)

  inv-coherently-invertible-mapᵉ :
    coherently-invertible-mapᵉ Aᵉ Bᵉ → coherently-invertible-mapᵉ Bᵉ Aᵉ
  inv-coherently-invertible-mapᵉ (fᵉ ,ᵉ Hᵉ) =
    ( map-inv-is-coherently-invertibleᵉ Hᵉ ,ᵉ
      is-coherently-invertible-map-inv-is-coherently-invertibleᵉ Hᵉ)

  inv-transpose-coherently-invertible-mapᵉ :
    transpose-coherently-invertible-mapᵉ Aᵉ Bᵉ →
    transpose-coherently-invertible-mapᵉ Bᵉ Aᵉ
  inv-transpose-coherently-invertible-mapᵉ (fᵉ ,ᵉ Hᵉ) =
    ( map-inv-is-transpose-coherently-invertibleᵉ Hᵉ ,ᵉ
      is-transpose-coherently-invertible-map-inv-is-transpose-coherently-invertibleᵉ
        ( Hᵉ))
```

### Composition of coherently invertible maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
    (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ)
    (Gᵉ : is-coherently-invertibleᵉ gᵉ)
    (Fᵉ : is-coherently-invertibleᵉ fᵉ)
  where

  coh-is-coherently-invertible-compᵉ :
    coherence-is-coherently-invertibleᵉ
      ( gᵉ ∘ᵉ fᵉ)
      ( map-inv-is-invertible-compᵉ gᵉ fᵉ
        ( is-invertible-is-coherently-invertibleᵉ Gᵉ)
        ( is-invertible-is-coherently-invertibleᵉ Fᵉ))
      ( is-section-map-inv-is-invertible-compᵉ gᵉ fᵉ
        ( is-invertible-is-coherently-invertibleᵉ Gᵉ)
        ( is-invertible-is-coherently-invertibleᵉ Fᵉ))
      ( is-retraction-map-inv-is-invertible-compᵉ gᵉ fᵉ
        ( is-invertible-is-coherently-invertibleᵉ Gᵉ)
        ( is-invertible-is-coherently-invertibleᵉ Fᵉ))
  coh-is-coherently-invertible-compᵉ =
    ( ap-concat-htpyᵉ
      ( ( gᵉ) ·lᵉ
        ( is-section-map-inv-is-coherently-invertibleᵉ Fᵉ) ·rᵉ
        ( map-inv-is-coherently-invertibleᵉ Gᵉ ∘ᵉ gᵉ ∘ᵉ fᵉ))
      ( coh-is-coherently-invertibleᵉ Gᵉ ·rᵉ fᵉ)) ∙hᵉ
    ( right-whisker-comp²ᵉ
      ( ( nat-htpyᵉ (gᵉ ·lᵉ is-section-map-inv-is-coherently-invertibleᵉ Fᵉ)) ·rᵉ
        ( is-retraction-map-inv-is-coherently-invertibleᵉ Gᵉ))
      ( fᵉ)) ∙hᵉ
    ( ap-binary-concat-htpyᵉ
      ( inv-preserves-comp-left-whisker-compᵉ
          ( gᵉ ∘ᵉ fᵉ)
          ( map-inv-is-coherently-invertibleᵉ Fᵉ)
          ( is-retraction-map-inv-is-coherently-invertibleᵉ Gᵉ ·rᵉ fᵉ))
      ( ( left-whisker-comp²ᵉ gᵉ (coh-is-coherently-invertibleᵉ Fᵉ)) ∙hᵉ
        ( preserves-comp-left-whisker-compᵉ gᵉ fᵉ
          ( is-retraction-map-inv-is-coherently-invertibleᵉ Fᵉ)))) ∙hᵉ
    ( inv-htpyᵉ
      ( distributive-left-whisker-comp-concatᵉ
        ( gᵉ ∘ᵉ fᵉ)
        ( ( map-inv-is-coherently-invertibleᵉ Fᵉ) ·lᵉ
          ( is-retraction-map-inv-is-coherently-invertibleᵉ Gᵉ ·rᵉ fᵉ))
        ( is-retraction-map-inv-is-coherently-invertibleᵉ Fᵉ)))

  is-coherently-invertible-compᵉ : is-coherently-invertibleᵉ (gᵉ ∘ᵉ fᵉ)
  is-coherently-invertible-compᵉ =
    is-coherently-invertible-coherence-is-invertibleᵉ
      ( is-invertible-compᵉ gᵉ fᵉ
        ( is-invertible-is-coherently-invertibleᵉ Gᵉ)
        ( is-invertible-is-coherently-invertibleᵉ Fᵉ))
      ( coh-is-coherently-invertible-compᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
    (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ)
    (Gᵉ : is-transpose-coherently-invertibleᵉ gᵉ)
    (Fᵉ : is-transpose-coherently-invertibleᵉ fᵉ)
  where

  coh-is-transpose-coherently-invertible-compᵉ :
    coherence-is-transpose-coherently-invertibleᵉ
      ( gᵉ ∘ᵉ fᵉ)
      ( map-inv-is-invertible-compᵉ gᵉ fᵉ
        ( is-invertible-is-transpose-coherently-invertibleᵉ Gᵉ)
        ( is-invertible-is-transpose-coherently-invertibleᵉ Fᵉ))
      ( is-section-map-inv-is-invertible-compᵉ gᵉ fᵉ
        ( is-invertible-is-transpose-coherently-invertibleᵉ Gᵉ)
        ( is-invertible-is-transpose-coherently-invertibleᵉ Fᵉ))
      ( is-retraction-map-inv-is-invertible-compᵉ gᵉ fᵉ
        ( is-invertible-is-transpose-coherently-invertibleᵉ Gᵉ)
        ( is-invertible-is-transpose-coherently-invertibleᵉ Fᵉ))
  coh-is-transpose-coherently-invertible-compᵉ =
    coh-is-coherently-invertible-compᵉ
      ( map-inv-is-transpose-coherently-invertibleᵉ Fᵉ)
      ( map-inv-is-transpose-coherently-invertibleᵉ Gᵉ)
      ( is-coherently-invertible-map-inv-is-transpose-coherently-invertibleᵉ Fᵉ)
      ( is-coherently-invertible-map-inv-is-transpose-coherently-invertibleᵉ Gᵉ)

  is-transpose-coherently-invertible-compᵉ :
    is-transpose-coherently-invertibleᵉ (gᵉ ∘ᵉ fᵉ)
  is-transpose-coherently-invertible-compᵉ =
    is-transpose-coherently-invertible-transpose-coherence-is-invertibleᵉ
      ( is-invertible-compᵉ gᵉ fᵉ
        ( is-invertible-is-transpose-coherently-invertibleᵉ Gᵉ)
        ( is-invertible-is-transpose-coherently-invertibleᵉ Fᵉ))
      ( coh-is-transpose-coherently-invertible-compᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  comp-coherently-invertible-mapᵉ :
    coherently-invertible-mapᵉ Bᵉ Cᵉ →
    coherently-invertible-mapᵉ Aᵉ Bᵉ →
    coherently-invertible-mapᵉ Aᵉ Cᵉ
  comp-coherently-invertible-mapᵉ (gᵉ ,ᵉ Gᵉ) (fᵉ ,ᵉ Fᵉ) =
    ( gᵉ ∘ᵉ fᵉ ,ᵉ is-coherently-invertible-compᵉ gᵉ fᵉ Gᵉ Fᵉ)

  comp-transpose-coherently-invertible-mapᵉ :
    transpose-coherently-invertible-mapᵉ Bᵉ Cᵉ →
    transpose-coherently-invertible-mapᵉ Aᵉ Bᵉ →
    transpose-coherently-invertible-mapᵉ Aᵉ Cᵉ
  comp-transpose-coherently-invertible-mapᵉ (gᵉ ,ᵉ Gᵉ) (fᵉ ,ᵉ Fᵉ) =
    ( gᵉ ∘ᵉ fᵉ ,ᵉ is-transpose-coherently-invertible-compᵉ gᵉ fᵉ Gᵉ Fᵉ)
```

### The 3-for-2 property of coherently invertible maps

Theᵉ
{{#conceptᵉ "3-for-2ᵉ property"ᵉ Disambiguation="ofᵉ coherentlyᵉ invertibleᵉ maps"ᵉ}}
ofᵉ coherentlyᵉ invertibleᵉ mapsᵉ assertsᵉ thatᵉ forᵉ anyᵉ
[commutingᵉ triangle](foundation-core.commuting-triangles-of-maps.mdᵉ) ofᵉ mapsᵉ

```text
       hᵉ
  Aᵉ ------>ᵉ Bᵉ
   \ᵉ       /ᵉ
   f\ᵉ     /gᵉ
     \ᵉ   /ᵉ
      ∨ᵉ ∨ᵉ
       X,ᵉ
```

ifᵉ twoᵉ ofᵉ theᵉ threeᵉ mapsᵉ areᵉ coherentlyᵉ invertible,ᵉ thenᵉ soᵉ isᵉ theᵉ third.ᵉ

Weᵉ alsoᵉ record specialᵉ casesᵉ ofᵉ theᵉ 3-for-2ᵉ propertyᵉ ofᵉ coherentlyᵉ invertibleᵉ
maps,ᵉ where weᵉ onlyᵉ assumeᵉ mapsᵉ `gᵉ : Bᵉ → X`ᵉ andᵉ `hᵉ : Aᵉ → B`.ᵉ Inᵉ thisᵉ specialᵉ
case,ᵉ weᵉ setᵉ `fᵉ :=ᵉ gᵉ ∘ᵉ h`ᵉ andᵉ theᵉ triangleᵉ commutesᵉ byᵉ `refl-htpy`.ᵉ

[Andréᵉ Joyal](https://en.wikipedia.org/wiki/André_Joyalᵉ) proposedᵉ callingᵉ thisᵉ
propertyᵉ theᵉ 3-for-2ᵉ property,ᵉ despiteᵉ mostᵉ mathematiciansᵉ callingᵉ itᵉ theᵉ
_2-out-of-3ᵉ property_.ᵉ Theᵉ storyᵉ goesᵉ thatᵉ onᵉ theᵉ produceᵉ marketᵉ isᵉ isᵉ commonᵉ to
advertiseᵉ aᵉ discountᵉ asᵉ "3-for-2".ᵉ Ifᵉ youᵉ buyᵉ twoᵉ apples,ᵉ thenᵉ youᵉ getᵉ theᵉ thirdᵉ
forᵉ free.ᵉ Similarly,ᵉ ifᵉ youᵉ proveᵉ thatᵉ twoᵉ mapsᵉ in aᵉ commutingᵉ triangleᵉ areᵉ
coherentlyᵉ invertible,ᵉ thenᵉ youᵉ getᵉ theᵉ thirdᵉ proofᵉ forᵉ free.ᵉ

#### The left map in a commuting triangle is coherently invertible if the other two maps are

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Tᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ)
  where

  is-coherently-invertible-left-map-triangleᵉ :
    is-coherently-invertibleᵉ hᵉ →
    is-coherently-invertibleᵉ gᵉ →
    is-coherently-invertibleᵉ fᵉ
  is-coherently-invertible-left-map-triangleᵉ Hᵉ Gᵉ =
    is-coherently-invertible-htpyᵉ Tᵉ (is-coherently-invertible-compᵉ gᵉ hᵉ Gᵉ Hᵉ)
```

#### The right map in a commuting triangle is coherently invertible if the other two maps are

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Tᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ)
  where

  is-coherently-invertible-right-map-triangleᵉ :
    is-coherently-invertibleᵉ fᵉ →
    is-coherently-invertibleᵉ hᵉ →
    is-coherently-invertibleᵉ gᵉ
  is-coherently-invertible-right-map-triangleᵉ Fᵉ Hᵉ =
    is-coherently-invertible-htpyᵉ
      ( ( gᵉ ·lᵉ inv-htpyᵉ (is-section-map-inv-is-coherently-invertibleᵉ Hᵉ)) ∙hᵉ
        ( inv-htpyᵉ Tᵉ ·rᵉ map-inv-is-coherently-invertibleᵉ Hᵉ))
      ( is-coherently-invertible-compᵉ
        ( fᵉ)
        ( map-inv-is-coherently-invertibleᵉ Hᵉ)
        ( Fᵉ)
        ( is-coherently-invertible-map-inv-is-coherently-invertibleᵉ Hᵉ))
```

#### The top map in a commuting triangle is coherently invertible if the other two maps are

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Tᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ)
  where

  is-coherently-invertible-top-map-triangleᵉ :
    is-coherently-invertibleᵉ gᵉ →
    is-coherently-invertibleᵉ fᵉ →
    is-coherently-invertibleᵉ hᵉ
  is-coherently-invertible-top-map-triangleᵉ Gᵉ Fᵉ =
    is-coherently-invertible-htpyᵉ
      ( ( inv-htpyᵉ (is-retraction-map-inv-is-coherently-invertibleᵉ Gᵉ) ·rᵉ hᵉ) ∙hᵉ
        ( map-inv-is-coherently-invertibleᵉ Gᵉ ·lᵉ inv-htpyᵉ Tᵉ))
      ( is-coherently-invertible-compᵉ
        ( map-inv-is-coherently-invertibleᵉ Gᵉ)
        ( fᵉ)
        ( is-coherently-invertible-map-inv-is-coherently-invertibleᵉ Gᵉ)
        ( Fᵉ))
```

#### If a composite and its right factor are coherently invertible, then so is its left factor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  is-coherently-invertible-left-factorᵉ :
    (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-coherently-invertibleᵉ (gᵉ ∘ᵉ hᵉ) →
    is-coherently-invertibleᵉ hᵉ →
    is-coherently-invertibleᵉ gᵉ
  is-coherently-invertible-left-factorᵉ gᵉ hᵉ GHᵉ Hᵉ =
    is-coherently-invertible-right-map-triangleᵉ (gᵉ ∘ᵉ hᵉ) gᵉ hᵉ refl-htpyᵉ GHᵉ Hᵉ
```

#### If a composite and its left factor are coherently invertible, then so is its right factor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  is-coherently-invertible-right-factorᵉ :
    (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-coherently-invertibleᵉ gᵉ →
    is-coherently-invertibleᵉ (gᵉ ∘ᵉ hᵉ) →
    is-coherently-invertibleᵉ hᵉ
  is-coherently-invertible-right-factorᵉ gᵉ hᵉ Gᵉ GHᵉ =
    is-coherently-invertible-top-map-triangleᵉ (gᵉ ∘ᵉ hᵉ) gᵉ hᵉ refl-htpyᵉ Gᵉ GHᵉ
```

### Any section of a coherently invertible map is coherently invertible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-coherently-invertible-is-sectionᵉ :
    {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ} →
    is-coherently-invertibleᵉ fᵉ → fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ → is-coherently-invertibleᵉ gᵉ
  is-coherently-invertible-is-sectionᵉ {fᵉ = fᵉ} {gᵉ} Fᵉ Hᵉ =
    is-coherently-invertible-top-map-triangleᵉ idᵉ fᵉ gᵉ
      ( inv-htpyᵉ Hᵉ)
      ( Fᵉ)
      ( is-coherently-invertible-idᵉ)
```

### Any retraction of a coherently invertible map is coherently invertible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-coherently-invertible-is-retractionᵉ :
    {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ} →
    is-coherently-invertibleᵉ fᵉ → (gᵉ ∘ᵉ fᵉ) ~ᵉ idᵉ → is-coherently-invertibleᵉ gᵉ
  is-coherently-invertible-is-retractionᵉ {fᵉ = fᵉ} {gᵉ} Fᵉ Hᵉ =
    is-coherently-invertible-right-map-triangleᵉ idᵉ gᵉ fᵉ
      ( inv-htpyᵉ Hᵉ)
      ( is-coherently-invertible-idᵉ)
      ( Fᵉ)
```

### If a section of `f` is coherently invertible, then `f` is coherently invertible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

    is-coherently-invertible-is-coherently-invertible-sectionᵉ :
      (sᵉ : sectionᵉ fᵉ) →
      is-coherently-invertibleᵉ (map-sectionᵉ fᵉ sᵉ) → is-coherently-invertibleᵉ fᵉ
    is-coherently-invertible-is-coherently-invertible-sectionᵉ (gᵉ ,ᵉ Gᵉ) Sᵉ =
      is-coherently-invertible-is-retractionᵉ Sᵉ Gᵉ
```

### If a retraction of `f` is coherently invertible, then `f` is coherently invertible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-coherently-invertible-is-coherently-invertible-retractionᵉ :
      (rᵉ : retractionᵉ fᵉ) →
      is-coherently-invertibleᵉ (map-retractionᵉ fᵉ rᵉ) → is-coherently-invertibleᵉ fᵉ
    is-coherently-invertible-is-coherently-invertible-retractionᵉ (gᵉ ,ᵉ Gᵉ) Rᵉ =
      is-coherently-invertible-is-sectionᵉ Rᵉ Gᵉ
```

### Any section of a coherently invertible map is homotopic to its inverse

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : coherently-invertible-mapᵉ Aᵉ Bᵉ)
  where

  htpy-map-inv-coherently-invertible-map-sectionᵉ :
    (fᵉ : sectionᵉ (map-coherently-invertible-mapᵉ eᵉ)) →
    map-inv-coherently-invertible-mapᵉ eᵉ ~ᵉ
    map-sectionᵉ (map-coherently-invertible-mapᵉ eᵉ) fᵉ
  htpy-map-inv-coherently-invertible-map-sectionᵉ =
    htpy-map-inv-invertible-map-sectionᵉ
      ( invertible-map-coherently-invertible-mapᵉ eᵉ)
```

### Any retraction of a coherently invertible map is homotopic to its inverse

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : coherently-invertible-mapᵉ Aᵉ Bᵉ)
  where

  htpy-map-inv-coherently-invertible-map-retractionᵉ :
    (fᵉ : retractionᵉ (map-coherently-invertible-mapᵉ eᵉ)) →
    map-inv-coherently-invertible-mapᵉ eᵉ ~ᵉ
    map-retractionᵉ (map-coherently-invertible-mapᵉ eᵉ) fᵉ
  htpy-map-inv-coherently-invertible-map-retractionᵉ =
    htpy-map-inv-invertible-map-retractionᵉ
      ( invertible-map-coherently-invertible-mapᵉ eᵉ)
```

## References

{{#bibliographyᵉ}}

## See also

-ᵉ Forᵉ theᵉ notionᵉ ofᵉ biinvertibleᵉ mapsᵉ seeᵉ
  [`foundation.equivalences`](foundation.equivalences.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ mapsᵉ with contractibleᵉ fibersᵉ seeᵉ
  [`foundation.contractible-maps`](foundation.contractible-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ path-splitᵉ mapsᵉ seeᵉ
  [`foundation.path-split-maps`](foundation.path-split-maps.md).ᵉ

## External links

-ᵉ [Adjointᵉ equivalences](https://1lab.dev/1Lab.Equiv.HalfAdjoint.htmlᵉ) atᵉ 1labᵉ
-ᵉ [adjointᵉ equivalence](https://ncatlab.org/nlab/show/adjoint+equivalenceᵉ) atᵉ
  $n$Labᵉ