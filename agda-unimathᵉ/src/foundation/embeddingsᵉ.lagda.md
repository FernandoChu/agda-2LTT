# Embeddings

```agda
module foundation.embeddingsᵉ where

open import foundation-core.embeddingsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.truncated-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.pullbacksᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Properties

### Being an embedding is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-property-is-embᵉ : (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (is-embᵉ fᵉ)
  is-property-is-embᵉ fᵉ =
    is-prop-Πᵉ (λ xᵉ → is-prop-Πᵉ (λ yᵉ → is-property-is-equivᵉ (apᵉ fᵉ)))

  is-emb-Propᵉ : (Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (is-emb-Propᵉ fᵉ) = is-embᵉ fᵉ
  pr2ᵉ (is-emb-Propᵉ fᵉ) = is-property-is-embᵉ fᵉ
```

### Embeddings are closed under homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-emb-htpyᵉ : {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) → is-embᵉ gᵉ → is-embᵉ fᵉ
    is-emb-htpyᵉ {fᵉ} {gᵉ} Hᵉ is-emb-gᵉ xᵉ yᵉ =
      is-equiv-top-is-equiv-left-squareᵉ
        ( apᵉ gᵉ)
        ( concat'ᵉ (fᵉ xᵉ) (Hᵉ yᵉ))
        ( apᵉ fᵉ)
        ( concatᵉ (Hᵉ xᵉ) (gᵉ yᵉ))
        ( nat-htpyᵉ Hᵉ)
        ( is-equiv-concatᵉ (Hᵉ xᵉ) (gᵉ yᵉ))
        ( is-emb-gᵉ xᵉ yᵉ)
        ( is-equiv-concat'ᵉ (fᵉ xᵉ) (Hᵉ yᵉ))

  is-emb-htpy-embᵉ : {fᵉ : Aᵉ → Bᵉ} (eᵉ : Aᵉ ↪ᵉ Bᵉ) → fᵉ ~ᵉ map-embᵉ eᵉ → is-embᵉ fᵉ
  is-emb-htpy-embᵉ eᵉ Hᵉ = is-emb-htpyᵉ Hᵉ (is-emb-map-embᵉ eᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-emb-htpy'ᵉ : {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) → is-embᵉ fᵉ → is-embᵉ gᵉ
    is-emb-htpy'ᵉ Hᵉ is-emb-fᵉ = is-emb-htpyᵉ (inv-htpyᵉ Hᵉ) is-emb-fᵉ

  is-emb-htpy-emb'ᵉ : (eᵉ : Aᵉ ↪ᵉ Bᵉ) {gᵉ : Aᵉ → Bᵉ} → map-embᵉ eᵉ ~ᵉ gᵉ → is-embᵉ gᵉ
  is-emb-htpy-emb'ᵉ eᵉ Hᵉ = is-emb-htpy'ᵉ Hᵉ (is-emb-map-embᵉ eᵉ)
```

### Any map between propositions is an embedding

```agda
is-emb-is-propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
  is-propᵉ Aᵉ → is-propᵉ Bᵉ → is-embᵉ fᵉ
is-emb-is-propᵉ Hᵉ Kᵉ =
  is-emb-is-prop-mapᵉ (is-trunc-map-is-trunc-domain-codomainᵉ neg-one-𝕋ᵉ Hᵉ Kᵉ)
```

### Embeddings are closed under composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  is-emb-compᵉ :
    (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ) → is-embᵉ gᵉ → is-embᵉ hᵉ → is-embᵉ (gᵉ ∘ᵉ hᵉ)
  is-emb-compᵉ gᵉ hᵉ is-emb-gᵉ is-emb-hᵉ xᵉ yᵉ =
    is-equiv-left-map-triangleᵉ
      ( apᵉ (gᵉ ∘ᵉ hᵉ))
      ( apᵉ gᵉ)
      ( apᵉ hᵉ)
      ( ap-compᵉ gᵉ hᵉ)
      ( is-emb-hᵉ xᵉ yᵉ)
      ( is-emb-gᵉ (hᵉ xᵉ) (hᵉ yᵉ))

  abstract
    is-emb-left-map-triangleᵉ :
      (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ) →
      is-embᵉ gᵉ → is-embᵉ hᵉ → is-embᵉ fᵉ
    is-emb-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ is-emb-gᵉ is-emb-hᵉ =
      is-emb-htpyᵉ Hᵉ (is-emb-compᵉ gᵉ hᵉ is-emb-gᵉ is-emb-hᵉ)

  comp-embᵉ :
    (Bᵉ ↪ᵉ Cᵉ) → (Aᵉ ↪ᵉ Bᵉ) → (Aᵉ ↪ᵉ Cᵉ)
  pr1ᵉ (comp-embᵉ (gᵉ ,ᵉ Hᵉ) (fᵉ ,ᵉ Kᵉ)) = gᵉ ∘ᵉ fᵉ
  pr2ᵉ (comp-embᵉ (gᵉ ,ᵉ Hᵉ) (fᵉ ,ᵉ Kᵉ)) = is-emb-compᵉ gᵉ fᵉ Hᵉ Kᵉ
```

### The right factor of a composed embedding is an embedding

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  is-emb-right-factorᵉ :
    (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-embᵉ gᵉ → is-embᵉ (gᵉ ∘ᵉ hᵉ) → is-embᵉ hᵉ
  is-emb-right-factorᵉ gᵉ hᵉ is-emb-gᵉ is-emb-ghᵉ xᵉ yᵉ =
    is-equiv-top-map-triangleᵉ
      ( apᵉ (gᵉ ∘ᵉ hᵉ))
      ( apᵉ gᵉ)
      ( apᵉ hᵉ)
      ( ap-compᵉ gᵉ hᵉ)
      ( is-emb-gᵉ (hᵉ xᵉ) (hᵉ yᵉ))
      ( is-emb-ghᵉ xᵉ yᵉ)

  abstract
    is-emb-top-map-triangleᵉ :
      (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ) →
      is-embᵉ gᵉ → is-embᵉ fᵉ → is-embᵉ hᵉ
    is-emb-top-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ is-emb-gᵉ is-emb-fᵉ xᵉ yᵉ =
      is-equiv-top-map-triangleᵉ
        ( apᵉ (gᵉ ∘ᵉ hᵉ))
        ( apᵉ gᵉ)
        ( apᵉ hᵉ)
        ( ap-compᵉ gᵉ hᵉ)
        ( is-emb-gᵉ (hᵉ xᵉ) (hᵉ yᵉ))
        ( is-emb-htpyᵉ (inv-htpyᵉ Hᵉ) is-emb-fᵉ xᵉ yᵉ)

  abstract
    is-emb-triangle-is-equivᵉ :
      (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ) (eᵉ : Aᵉ → Bᵉ) (Hᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ eᵉ) →
      is-equivᵉ eᵉ → is-embᵉ gᵉ → is-embᵉ fᵉ
    is-emb-triangle-is-equivᵉ fᵉ gᵉ eᵉ Hᵉ is-equiv-eᵉ is-emb-gᵉ =
      is-emb-left-map-triangleᵉ fᵉ gᵉ eᵉ Hᵉ is-emb-gᵉ (is-emb-is-equivᵉ is-equiv-eᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  abstract
    is-emb-triangle-is-equiv'ᵉ :
      (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ) (eᵉ : Aᵉ → Bᵉ) (Hᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ eᵉ) →
      is-equivᵉ eᵉ → is-embᵉ fᵉ → is-embᵉ gᵉ
    is-emb-triangle-is-equiv'ᵉ fᵉ gᵉ eᵉ Hᵉ is-equiv-eᵉ is-emb-fᵉ =
      is-emb-triangle-is-equivᵉ gᵉ fᵉ
        ( map-inv-is-equivᵉ is-equiv-eᵉ)
        ( triangle-sectionᵉ fᵉ gᵉ eᵉ Hᵉ
          ( pairᵉ
            ( map-inv-is-equivᵉ is-equiv-eᵉ)
            ( is-section-map-inv-is-equivᵉ is-equiv-eᵉ)))
        ( is-equiv-map-inv-is-equivᵉ is-equiv-eᵉ)
        ( is-emb-fᵉ)
```

### The map on total spaces induced by a family of embeddings is an embedding

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  is-emb-totᵉ :
    {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ} → ((xᵉ : Aᵉ) → is-embᵉ (fᵉ xᵉ)) → is-embᵉ (totᵉ fᵉ)
  is-emb-totᵉ Hᵉ =
    is-emb-is-prop-mapᵉ (is-prop-map-totᵉ (λ xᵉ → is-prop-map-is-embᵉ (Hᵉ xᵉ)))

  emb-totᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ ↪ᵉ Cᵉ xᵉ) → Σᵉ Aᵉ Bᵉ ↪ᵉ Σᵉ Aᵉ Cᵉ
  pr1ᵉ (emb-totᵉ fᵉ) = totᵉ (λ xᵉ → map-embᵉ (fᵉ xᵉ))
  pr2ᵉ (emb-totᵉ fᵉ) = is-emb-totᵉ (λ xᵉ → is-emb-map-embᵉ (fᵉ xᵉ))
```

### The functoriality of dependent pair types preserves embeddings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-emb-map-Σ-map-baseᵉ :
      {fᵉ : Aᵉ → Bᵉ} (Cᵉ : Bᵉ → UUᵉ l3ᵉ) → is-embᵉ fᵉ → is-embᵉ (map-Σ-map-baseᵉ fᵉ Cᵉ)
    is-emb-map-Σ-map-baseᵉ Cᵉ Hᵉ =
      is-emb-is-prop-mapᵉ (is-prop-map-map-Σ-map-baseᵉ Cᵉ (is-prop-map-is-embᵉ Hᵉ))

  emb-Σ-emb-baseᵉ :
    (fᵉ : Aᵉ ↪ᵉ Bᵉ) (Cᵉ : Bᵉ → UUᵉ l3ᵉ) → Σᵉ Aᵉ (λ aᵉ → Cᵉ (map-embᵉ fᵉ aᵉ)) ↪ᵉ Σᵉ Bᵉ Cᵉ
  pr1ᵉ (emb-Σ-emb-baseᵉ fᵉ Cᵉ) = map-Σ-map-baseᵉ (map-embᵉ fᵉ) Cᵉ
  pr2ᵉ (emb-Σ-emb-baseᵉ fᵉ Cᵉ) =
    is-emb-map-Σ-map-baseᵉ Cᵉ (is-emb-map-embᵉ fᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  is-emb-map-Σᵉ :
    (Dᵉ : Bᵉ → UUᵉ l4ᵉ) {fᵉ : Aᵉ → Bᵉ} {gᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ → Dᵉ (fᵉ xᵉ)} →
    is-embᵉ fᵉ → ((xᵉ : Aᵉ) → is-embᵉ (gᵉ xᵉ)) → is-embᵉ (map-Σᵉ Dᵉ fᵉ gᵉ)
  is-emb-map-Σᵉ Dᵉ Hᵉ Kᵉ =
    is-emb-is-prop-mapᵉ
      ( is-prop-map-map-Σᵉ Dᵉ
        ( is-prop-map-is-embᵉ Hᵉ)
        ( λ xᵉ → is-prop-map-is-embᵉ (Kᵉ xᵉ)))

  emb-Σᵉ :
    (Dᵉ : Bᵉ → UUᵉ l4ᵉ) (fᵉ : Aᵉ ↪ᵉ Bᵉ) (gᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ ↪ᵉ Dᵉ (map-embᵉ fᵉ xᵉ)) →
    Σᵉ Aᵉ Cᵉ ↪ᵉ Σᵉ Bᵉ Dᵉ
  pr1ᵉ (emb-Σᵉ Dᵉ fᵉ gᵉ) = map-Σᵉ Dᵉ (map-embᵉ fᵉ) (λ xᵉ → map-embᵉ (gᵉ xᵉ))
  pr2ᵉ (emb-Σᵉ Dᵉ fᵉ gᵉ) =
    is-emb-map-Σᵉ Dᵉ (is-emb-map-embᵉ fᵉ) (λ xᵉ → is-emb-map-embᵉ (gᵉ xᵉ))
```

### Equivalence on total spaces induced by embedding on the base types

Weᵉ sawᵉ aboveᵉ thatᵉ givenᵉ anᵉ embeddingᵉ `fᵉ : Aᵉ ↪ᵉ B`ᵉ andᵉ aᵉ typeᵉ familyᵉ `C`ᵉ overᵉ `B`ᵉ
weᵉ obtainᵉ anᵉ embeddingᵉ

```text
  Σᵉ Aᵉ (Cᵉ ∘ᵉ fᵉ) ↪ᵉ Σᵉ Bᵉ C.ᵉ
```

Thisᵉ embeddingᵉ canᵉ beᵉ upgradedᵉ to anᵉ equivalenceᵉ ifᵉ weᵉ furthermoreᵉ knowᵉ thatᵉ theᵉ
supportᵉ ofᵉ `C`ᵉ isᵉ containedᵉ in theᵉ imageᵉ ofᵉ `f`.ᵉ Moreᵉ precisely,ᵉ ifᵉ weᵉ areᵉ givenᵉ
aᵉ sectionᵉ `((bᵉ ,ᵉ cᵉ) : Σᵉ Bᵉ Cᵉ) → fiberᵉ fᵉ b`,ᵉ thenᵉ itᵉ followsᵉ thatᵉ

```text
  Σᵉ Aᵉ (Cᵉ ∘ᵉ fᵉ) ≃ᵉ Σᵉ Bᵉ C.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Bᵉ → UUᵉ l3ᵉ} (fᵉ : Aᵉ ↪ᵉ Bᵉ)
  (Hᵉ : ((bᵉ ,ᵉ cᵉ) : Σᵉ Bᵉ Cᵉ) → fiberᵉ (map-embᵉ fᵉ) bᵉ)
  where

  map-inv-Σ-emb-baseᵉ : Σᵉ Bᵉ Cᵉ → Σᵉ Aᵉ (Cᵉ ∘ᵉ map-embᵉ fᵉ)
  pr1ᵉ (map-inv-Σ-emb-baseᵉ uᵉ) = pr1ᵉ (Hᵉ uᵉ)
  pr2ᵉ (map-inv-Σ-emb-baseᵉ uᵉ) = inv-trᵉ Cᵉ (pr2ᵉ (Hᵉ uᵉ)) (pr2ᵉ uᵉ)

  is-section-map-inv-Σ-emb-baseᵉ :
    is-sectionᵉ (map-Σ-map-baseᵉ (map-embᵉ fᵉ) Cᵉ) map-inv-Σ-emb-baseᵉ
  is-section-map-inv-Σ-emb-baseᵉ (bᵉ ,ᵉ cᵉ) =
    apᵉ
      ( λ sᵉ → (pr1ᵉ sᵉ ,ᵉ inv-trᵉ Cᵉ (pr2ᵉ sᵉ) cᵉ))
      ( eq-is-contrᵉ (is-torsorial-Id'ᵉ bᵉ))

  is-retraction-map-inv-Σ-emb-baseᵉ :
    is-retractionᵉ (map-Σ-map-baseᵉ (map-embᵉ fᵉ) Cᵉ) map-inv-Σ-emb-baseᵉ
  is-retraction-map-inv-Σ-emb-baseᵉ (aᵉ ,ᵉ cᵉ) =
    apᵉ
      ( λ sᵉ → (pr1ᵉ sᵉ ,ᵉ inv-trᵉ Cᵉ (pr2ᵉ sᵉ) cᵉ))
      ( eq-is-propᵉ (is-prop-map-is-embᵉ (pr2ᵉ fᵉ) (map-embᵉ fᵉ aᵉ)))

  equiv-Σ-emb-baseᵉ : Σᵉ Aᵉ (Cᵉ ∘ᵉ map-embᵉ fᵉ) ≃ᵉ Σᵉ Bᵉ Cᵉ
  pr1ᵉ equiv-Σ-emb-baseᵉ = map-Σ-map-baseᵉ (map-embᵉ fᵉ) Cᵉ
  pr2ᵉ equiv-Σ-emb-baseᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-Σ-emb-baseᵉ
      is-section-map-inv-Σ-emb-baseᵉ
      is-retraction-map-inv-Σ-emb-baseᵉ
```

### The product of two embeddings is an embedding

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  where

  emb-productᵉ : (Aᵉ ↪ᵉ Cᵉ) → (Bᵉ ↪ᵉ Dᵉ) → ((Aᵉ ×ᵉ Bᵉ) ↪ᵉ (Cᵉ ×ᵉ Dᵉ))
  emb-productᵉ fᵉ gᵉ = emb-Σᵉ (λ _ → Dᵉ) fᵉ (λ _ → gᵉ)

  is-emb-map-productᵉ :
    (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Dᵉ) → is-embᵉ fᵉ → is-embᵉ gᵉ → (is-embᵉ (map-productᵉ fᵉ gᵉ))
  is-emb-map-productᵉ fᵉ gᵉ is-emb-fᵉ is-emb-gᵉ =
    is-emb-map-embᵉ (emb-productᵉ (fᵉ ,ᵉ is-emb-fᵉ) (gᵉ ,ᵉ is-emb-gᵉ))
```

### If the action on identifications has a section, then `f` is an embedding

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-emb-section-apᵉ :
      ((xᵉ yᵉ : Aᵉ) → sectionᵉ (apᵉ fᵉ {xᵉ} {yᵉ})) → is-embᵉ fᵉ
    is-emb-section-apᵉ section-ap-fᵉ xᵉ =
      fundamental-theorem-id-sectionᵉ xᵉ (λ yᵉ → apᵉ fᵉ) (section-ap-fᵉ xᵉ)
```

### If there is an equivalence `(f x = f y) ≃ (x = y)` that sends `refl` to `refl`, then f is an embedding

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-emb-equiv-refl-to-reflᵉ :
      (eᵉ : (xᵉ yᵉ : Aᵉ) → (fᵉ xᵉ ＝ᵉ fᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ yᵉ)) →
      ((xᵉ : Aᵉ) → map-equivᵉ (eᵉ xᵉ xᵉ) reflᵉ ＝ᵉ reflᵉ) →
      is-embᵉ fᵉ
    is-emb-equiv-refl-to-reflᵉ eᵉ pᵉ xᵉ yᵉ =
      is-equiv-htpy-equivᵉ
        ( inv-equivᵉ (eᵉ xᵉ yᵉ))
        ( λ where
          reflᵉ →
            invᵉ (is-retraction-map-inv-equivᵉ (eᵉ xᵉ xᵉ) reflᵉ) ∙ᵉ
            apᵉ (map-equivᵉ (inv-equivᵉ (eᵉ xᵉ xᵉ))) (pᵉ xᵉ))
```

### Embeddings are closed under pullback

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  abstract
    is-emb-vertical-map-cone-is-pullbackᵉ :
      is-pullbackᵉ fᵉ gᵉ cᵉ → is-embᵉ gᵉ → is-embᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ)
    is-emb-vertical-map-cone-is-pullbackᵉ pbᵉ is-emb-gᵉ =
      is-emb-is-prop-mapᵉ
        ( is-trunc-vertical-map-is-pullbackᵉ neg-one-𝕋ᵉ fᵉ gᵉ cᵉ pbᵉ
          ( is-prop-map-is-embᵉ is-emb-gᵉ))

  abstract
    is-emb-horizontal-map-cone-is-pullbackᵉ :
      is-pullbackᵉ fᵉ gᵉ cᵉ → is-embᵉ fᵉ → is-embᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
    is-emb-horizontal-map-cone-is-pullbackᵉ pbᵉ is-emb-fᵉ =
      is-emb-is-prop-mapᵉ
        ( is-trunc-horizontal-map-is-pullbackᵉ neg-one-𝕋ᵉ fᵉ gᵉ cᵉ pbᵉ
          ( is-prop-map-is-embᵉ is-emb-fᵉ))
```

### In a commuting square of which the sides are embeddings, the top map is an embedding if and only if the bottom map is an embedding

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (topᵉ : Aᵉ → Cᵉ) (leftᵉ : Aᵉ → Bᵉ) (rightᵉ : Cᵉ → Dᵉ) (bottomᵉ : Bᵉ → Dᵉ)
  (Hᵉ : coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ)
  where

  is-emb-top-is-emb-bottom-is-equiv-coherence-square-mapsᵉ :
    is-equivᵉ leftᵉ → is-equivᵉ rightᵉ → is-embᵉ bottomᵉ → is-embᵉ topᵉ
  is-emb-top-is-emb-bottom-is-equiv-coherence-square-mapsᵉ Kᵉ Lᵉ Mᵉ =
    is-emb-right-factorᵉ
      ( rightᵉ)
      ( topᵉ)
      ( is-emb-is-equivᵉ Lᵉ)
      ( is-emb-htpy'ᵉ
        ( Hᵉ)
        ( is-emb-compᵉ bottomᵉ leftᵉ Mᵉ (is-emb-is-equivᵉ Kᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (topᵉ : Aᵉ → Cᵉ) (leftᵉ : Aᵉ → Bᵉ) (rightᵉ : Cᵉ → Dᵉ) (bottomᵉ : Bᵉ → Dᵉ)
  (Hᵉ : coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ)
  where

  is-emb-bottom-is-emb-top-is-equiv-coherence-square-mapsᵉ :
    is-equivᵉ leftᵉ → is-equivᵉ rightᵉ → is-embᵉ topᵉ → is-embᵉ bottomᵉ
  is-emb-bottom-is-emb-top-is-equiv-coherence-square-mapsᵉ Kᵉ Lᵉ Mᵉ =
    is-emb-top-is-emb-bottom-is-equiv-coherence-square-mapsᵉ
      ( bottomᵉ)
      ( map-inv-is-equivᵉ Kᵉ)
      ( map-inv-is-equivᵉ Lᵉ)
      ( topᵉ)
      ( vertical-inv-equiv-coherence-square-mapsᵉ
        ( topᵉ)
        ( leftᵉ ,ᵉ Kᵉ)
        ( rightᵉ ,ᵉ Lᵉ)
        ( bottomᵉ)
        ( Hᵉ))
      ( is-equiv-map-inv-is-equivᵉ Kᵉ)
      ( is-equiv-map-inv-is-equivᵉ Lᵉ)
      ( Mᵉ)
```

### A map is an embedding if and only if it has contractible fibers at values

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-emb-is-contr-fibers-values'ᵉ :
    ((aᵉ : Aᵉ) → is-contrᵉ (fiber'ᵉ fᵉ (fᵉ aᵉ))) → is-embᵉ fᵉ
  is-emb-is-contr-fibers-values'ᵉ cᵉ aᵉ =
    fundamental-theorem-idᵉ (cᵉ aᵉ) (λ xᵉ → apᵉ fᵉ {aᵉ} {xᵉ})

  is-emb-is-contr-fibers-valuesᵉ :
    ((aᵉ : Aᵉ) → is-contrᵉ (fiberᵉ fᵉ (fᵉ aᵉ))) → is-embᵉ fᵉ
  is-emb-is-contr-fibers-valuesᵉ cᵉ =
    is-emb-is-contr-fibers-values'ᵉ
      ( λ aᵉ →
        is-contr-equiv'ᵉ
          ( fiberᵉ fᵉ (fᵉ aᵉ))
          ( equiv-fiberᵉ fᵉ (fᵉ aᵉ))
          ( cᵉ aᵉ))

  is-contr-fibers-values-is-emb'ᵉ :
    is-embᵉ fᵉ → ((aᵉ : Aᵉ) → is-contrᵉ (fiber'ᵉ fᵉ (fᵉ aᵉ)))
  is-contr-fibers-values-is-emb'ᵉ eᵉ aᵉ =
    fundamental-theorem-id'ᵉ (λ xᵉ → apᵉ fᵉ {aᵉ} {xᵉ}) (eᵉ aᵉ)

  is-contr-fibers-values-is-embᵉ :
    is-embᵉ fᵉ → ((aᵉ : Aᵉ) → is-contrᵉ (fiberᵉ fᵉ (fᵉ aᵉ)))
  is-contr-fibers-values-is-embᵉ eᵉ aᵉ =
    is-contr-equivᵉ
      ( fiber'ᵉ fᵉ (fᵉ aᵉ))
      ( equiv-fiberᵉ fᵉ (fᵉ aᵉ))
      ( is-contr-fibers-values-is-emb'ᵉ eᵉ aᵉ)
```