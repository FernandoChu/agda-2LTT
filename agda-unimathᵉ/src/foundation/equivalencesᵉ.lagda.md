# Equivalences

```agda
module foundation.equivalencesᵉ where

open import foundation-core.equivalencesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-fibers-of-mapsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.truncated-mapsᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.pullbacksᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.retracts-of-typesᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.truncation-levelsᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Properties

### Any equivalence is an embedding

Weᵉ alreadyᵉ provedᵉ in `foundation-core.equivalences`ᵉ thatᵉ equivalencesᵉ areᵉ
embeddings.ᵉ Hereᵉ weᵉ haveᵉ `_↪_`ᵉ available,ᵉ soᵉ weᵉ record theᵉ mapᵉ fromᵉ equivalencesᵉ
to embeddings.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-emb-equivᵉ : (eᵉ : Aᵉ ≃ᵉ Bᵉ) → is-embᵉ (map-equivᵉ eᵉ)
  is-emb-equivᵉ eᵉ = is-emb-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

  emb-equivᵉ : (Aᵉ ≃ᵉ Bᵉ) → (Aᵉ ↪ᵉ Bᵉ)
  pr1ᵉ (emb-equivᵉ eᵉ) = map-equivᵉ eᵉ
  pr2ᵉ (emb-equivᵉ eᵉ) = is-emb-equivᵉ eᵉ
```

### Equivalences have a contractible type of sections

**Proof:**ᵉ Sinceᵉ equivalencesᵉ areᵉ
[contractibleᵉ maps](foundation.contractible-maps.md),ᵉ andᵉ productsᵉ ofᵉ
[contractibleᵉ types](foundation-core.contractible-types.mdᵉ) areᵉ contractible,ᵉ itᵉ
followsᵉ thatᵉ theᵉ typeᵉ

```text
  (bᵉ : Bᵉ) → fiberᵉ fᵉ bᵉ
```

isᵉ contractible,ᵉ forᵉ anyᵉ equivalenceᵉ `f`.ᵉ However,ᵉ byᵉ theᵉ
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
    is-contr-section-is-equivᵉ : {fᵉ : Aᵉ → Bᵉ} → is-equivᵉ fᵉ → is-contrᵉ (sectionᵉ fᵉ)
    is-contr-section-is-equivᵉ {fᵉ} is-equiv-fᵉ =
      is-contr-equiv'ᵉ
        ( (bᵉ : Bᵉ) → fiberᵉ fᵉ bᵉ)
        ( distributive-Π-Σᵉ)
        ( is-contr-Πᵉ (is-contr-map-is-equivᵉ is-equiv-fᵉ))
```

### Equivalences have a contractible type of retractions

**Proof:**ᵉ Sinceᵉ precomposingᵉ byᵉ anᵉ equivalenceᵉ isᵉ anᵉ equivalence,ᵉ andᵉ
equivalencesᵉ areᵉ contractibleᵉ maps,ᵉ itᵉ followsᵉ thatᵉ theᵉ
[fiber](foundation-core.fibers-of-maps.mdᵉ) ofᵉ theᵉ mapᵉ

```text
  (Bᵉ → Aᵉ) → (Aᵉ → Aᵉ)
```

atᵉ `idᵉ : Aᵉ → A`ᵉ isᵉ contractible,ᵉ i.e.,ᵉ theᵉ typeᵉ `Σᵉ (Bᵉ → Aᵉ) (λ hᵉ → hᵉ ∘ᵉ fᵉ ＝ᵉ id)`ᵉ
isᵉ contractible.ᵉ Furthermore,ᵉ sinceᵉ fiberwiseᵉ equivalencesᵉ induceᵉ equivalencesᵉ
onᵉ totalᵉ spaces,ᵉ itᵉ followsᵉ fromᵉ
[functionᵉ extensionality](foundation.function-extensionality.md)`ᵉ thatᵉ theᵉ typeᵉ

```text
  Σᵉ (Bᵉ → Aᵉ) (λ hᵉ → hᵉ ∘ᵉ fᵉ ~ᵉ idᵉ)
```

isᵉ contractible.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ typeᵉ ofᵉ retractionsᵉ ofᵉ anᵉ equivalenceᵉ isᵉ
contractible.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-contr-retraction-is-equivᵉ :
      {fᵉ : Aᵉ → Bᵉ} → is-equivᵉ fᵉ → is-contrᵉ (retractionᵉ fᵉ)
    is-contr-retraction-is-equivᵉ {fᵉ} is-equiv-fᵉ =
      is-contr-equiv'ᵉ
        ( Σᵉ (Bᵉ → Aᵉ) (λ hᵉ → hᵉ ∘ᵉ fᵉ ＝ᵉ idᵉ))
        ( equiv-totᵉ (λ hᵉ → equiv-funextᵉ))
        ( is-contr-map-is-equivᵉ (is-equiv-precomp-is-equivᵉ fᵉ is-equiv-fᵉ Aᵉ) idᵉ)
```

### The underlying retract of an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  retract-equivᵉ : Aᵉ ≃ᵉ Bᵉ → Aᵉ retract-ofᵉ Bᵉ
  retract-equivᵉ eᵉ =
    ( map-equivᵉ eᵉ ,ᵉ map-inv-equivᵉ eᵉ ,ᵉ is-retraction-map-inv-equivᵉ eᵉ)

  retract-inv-equivᵉ : Bᵉ ≃ᵉ Aᵉ → Aᵉ retract-ofᵉ Bᵉ
  retract-inv-equivᵉ = retract-equivᵉ ∘ᵉ inv-equivᵉ
```

### Being an equivalence is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-contr-is-equiv-is-equivᵉ : {fᵉ : Aᵉ → Bᵉ} → is-equivᵉ fᵉ → is-contrᵉ (is-equivᵉ fᵉ)
  is-contr-is-equiv-is-equivᵉ is-equiv-fᵉ =
    is-contr-productᵉ
      ( is-contr-section-is-equivᵉ is-equiv-fᵉ)
      ( is-contr-retraction-is-equivᵉ is-equiv-fᵉ)

  abstract
    is-property-is-equivᵉ : (fᵉ : Aᵉ → Bᵉ) → (Hᵉ Kᵉ : is-equivᵉ fᵉ) → is-contrᵉ (Hᵉ ＝ᵉ Kᵉ)
    is-property-is-equivᵉ fᵉ Hᵉ =
      is-prop-is-contrᵉ (is-contr-is-equiv-is-equivᵉ Hᵉ) Hᵉ

  is-equiv-Propᵉ : (fᵉ : Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (is-equiv-Propᵉ fᵉ) = is-equivᵉ fᵉ
  pr2ᵉ (is-equiv-Propᵉ fᵉ) = is-property-is-equivᵉ fᵉ

  eq-equiv-eq-map-equivᵉ :
    {eᵉ e'ᵉ : Aᵉ ≃ᵉ Bᵉ} → (map-equivᵉ eᵉ) ＝ᵉ (map-equivᵉ e'ᵉ) → eᵉ ＝ᵉ e'ᵉ
  eq-equiv-eq-map-equivᵉ = eq-type-subtypeᵉ is-equiv-Propᵉ

  abstract
    is-emb-map-equivᵉ :
      is-embᵉ (map-equivᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ})
    is-emb-map-equivᵉ = is-emb-inclusion-subtypeᵉ is-equiv-Propᵉ

  is-injective-map-equivᵉ :
    is-injectiveᵉ (map-equivᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ})
  is-injective-map-equivᵉ = is-injective-is-embᵉ is-emb-map-equivᵉ

  emb-map-equivᵉ : (Aᵉ ≃ᵉ Bᵉ) ↪ᵉ (Aᵉ → Bᵉ)
  pr1ᵉ emb-map-equivᵉ = map-equivᵉ
  pr2ᵉ emb-map-equivᵉ = is-emb-map-equivᵉ
```

### The 3-for-2 property of being an equivalence

#### If the right factor is an equivalence, then the left factor being an equivalence is equivalent to the composite being one

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  equiv-is-equiv-right-map-triangleᵉ :
    { fᵉ : Aᵉ → Bᵉ} (eᵉ : Bᵉ ≃ᵉ Cᵉ) (hᵉ : Aᵉ → Cᵉ)
    ( Hᵉ : coherence-triangle-mapsᵉ hᵉ (map-equivᵉ eᵉ) fᵉ) →
    is-equivᵉ fᵉ ≃ᵉ is-equivᵉ hᵉ
  equiv-is-equiv-right-map-triangleᵉ {fᵉ} eᵉ hᵉ Hᵉ =
    equiv-iff-is-propᵉ
      ( is-property-is-equivᵉ fᵉ)
      ( is-property-is-equivᵉ hᵉ)
      ( λ is-equiv-fᵉ →
        is-equiv-left-map-triangleᵉ hᵉ (map-equivᵉ eᵉ) fᵉ Hᵉ is-equiv-fᵉ
          ( is-equiv-map-equivᵉ eᵉ))
      ( is-equiv-top-map-triangleᵉ hᵉ (map-equivᵉ eᵉ) fᵉ Hᵉ (is-equiv-map-equivᵉ eᵉ))

  equiv-is-equiv-left-factorᵉ :
    { fᵉ : Aᵉ → Bᵉ} (eᵉ : Bᵉ ≃ᵉ Cᵉ) →
    is-equivᵉ fᵉ ≃ᵉ is-equivᵉ (map-equivᵉ eᵉ ∘ᵉ fᵉ)
  equiv-is-equiv-left-factorᵉ {fᵉ} eᵉ =
    equiv-is-equiv-right-map-triangleᵉ eᵉ (map-equivᵉ eᵉ ∘ᵉ fᵉ) refl-htpyᵉ
```

#### If the left factor is an equivalence, then the right factor being an equivalence is equivalent to the composite being one

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  equiv-is-equiv-top-map-triangleᵉ :
    ( eᵉ : Aᵉ ≃ᵉ Bᵉ) {fᵉ : Bᵉ → Cᵉ} (hᵉ : Aᵉ → Cᵉ)
    ( Hᵉ : coherence-triangle-mapsᵉ hᵉ fᵉ (map-equivᵉ eᵉ)) →
    is-equivᵉ fᵉ ≃ᵉ is-equivᵉ hᵉ
  equiv-is-equiv-top-map-triangleᵉ eᵉ {fᵉ} hᵉ Hᵉ =
    equiv-iff-is-propᵉ
      ( is-property-is-equivᵉ fᵉ)
      ( is-property-is-equivᵉ hᵉ)
      ( is-equiv-left-map-triangleᵉ hᵉ fᵉ (map-equivᵉ eᵉ) Hᵉ (is-equiv-map-equivᵉ eᵉ))
      ( λ is-equiv-hᵉ →
        is-equiv-right-map-triangleᵉ hᵉ fᵉ
          ( map-equivᵉ eᵉ)
          ( Hᵉ)
          ( is-equiv-hᵉ)
          ( is-equiv-map-equivᵉ eᵉ))

  equiv-is-equiv-right-factorᵉ :
    ( eᵉ : Aᵉ ≃ᵉ Bᵉ) {fᵉ : Bᵉ → Cᵉ} →
    is-equivᵉ fᵉ ≃ᵉ is-equivᵉ (fᵉ ∘ᵉ map-equivᵉ eᵉ)
  equiv-is-equiv-right-factorᵉ eᵉ {fᵉ} =
    equiv-is-equiv-top-map-triangleᵉ eᵉ (fᵉ ∘ᵉ map-equivᵉ eᵉ) refl-htpyᵉ
```

### The 6-for-2 property of equivalences

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ mapsᵉ

```text
         iᵉ
    Aᵉ ------>ᵉ Xᵉ
    |       ∧ᵉ |
  fᵉ |     /ᵉ   | gᵉ
    |   hᵉ     |
    ∨ᵉ /ᵉ       ∨ᵉ
    Bᵉ ------>ᵉ Y.ᵉ
         jᵉ
```

Theᵉ **6-for-2ᵉ propertyᵉ ofᵉ equivalences**ᵉ assertsᵉ thatᵉ ifᵉ `i`ᵉ andᵉ `j`ᵉ areᵉ
equivalences,ᵉ thenᵉ soᵉ areᵉ `h`,ᵉ `f`,ᵉ `g`,ᵉ andᵉ theᵉ tripleᵉ compositeᵉ `gᵉ ∘ᵉ hᵉ ∘ᵉ f`.ᵉ
Theᵉ 6-for-2ᵉ propertyᵉ isᵉ alsoᵉ commonlyᵉ knownᵉ asᵉ theᵉ **2-out-of-6ᵉ property**.ᵉ

**Firstᵉ proof:**ᵉ Sinceᵉ `i`ᵉ isᵉ anᵉ equivalence,ᵉ itᵉ followsᵉ thatᵉ `i`ᵉ isᵉ surjective.ᵉ
Thisᵉ impliesᵉ thatᵉ `h`ᵉ isᵉ surjective.ᵉ Furthermore,ᵉ sinceᵉ `j`ᵉ isᵉ anᵉ equivalenceᵉ itᵉ
followsᵉ thatᵉ `j`ᵉ isᵉ anᵉ embedding.ᵉ Thisᵉ impliesᵉ thatᵉ `h`ᵉ isᵉ anᵉ embedding.ᵉ Theᵉ mapᵉ
`h`ᵉ isᵉ thereforeᵉ bothᵉ surjectiveᵉ andᵉ anᵉ embedding,ᵉ soᵉ itᵉ mustᵉ beᵉ anᵉ equivalence.ᵉ
Theᵉ factᵉ thatᵉ `f`ᵉ andᵉ `g`ᵉ areᵉ equivalencesᵉ nowᵉ followsᵉ fromᵉ aᵉ simpleᵉ applicationᵉ
ofᵉ theᵉ 3-for-2ᵉ propertyᵉ ofᵉ equivalences.ᵉ

Unfortunately,ᵉ theᵉ aboveᵉ proofᵉ requiresᵉ usᵉ to import `surjective-maps`,ᵉ whichᵉ
causesᵉ aᵉ cyclicᵉ module dependency.ᵉ Weᵉ thereforeᵉ giveᵉ aᵉ secondᵉ proof,ᵉ whichᵉ
avoidsᵉ theᵉ factᵉ thatᵉ mapsᵉ thatᵉ areᵉ bothᵉ surjectiveᵉ andᵉ anᵉ embeddingᵉ areᵉ
equivalences.ᵉ

**Secondᵉ proof:**ᵉ Byᵉ reasoningᵉ similarᵉ to thatᵉ in theᵉ firstᵉ proof,ᵉ itᵉ sufficesᵉ
to showᵉ thatᵉ theᵉ diagonalᵉ fillerᵉ `h`ᵉ isᵉ anᵉ equivalence.ᵉ Theᵉ mapᵉ `fᵉ ∘ᵉ i⁻¹`ᵉ isᵉ aᵉ
sectionᵉ ofᵉ `h`,ᵉ sinceᵉ weᵉ haveᵉ `(hᵉ ∘ᵉ fᵉ ~ᵉ iᵉ) → (hᵉ ∘ᵉ fᵉ ∘ᵉ i⁻¹ᵉ ~ᵉ id)`ᵉ byᵉ transposingᵉ
alongᵉ equivalences.ᵉ Similarly,ᵉ theᵉ mapᵉ `j⁻¹ᵉ ∘ᵉ g`ᵉ isᵉ aᵉ retractionᵉ ofᵉ `h`,ᵉ sinceᵉ
weᵉ haveᵉ `(gᵉ ∘ᵉ hᵉ ~ᵉ jᵉ) → (j⁻¹ᵉ ∘ᵉ gᵉ ∘ᵉ hᵉ ~ᵉ id)`ᵉ byᵉ transposingᵉ alongᵉ equivalences.ᵉ
Sinceᵉ `h`ᵉ thereforeᵉ hasᵉ aᵉ sectionᵉ andᵉ aᵉ retraction,ᵉ itᵉ isᵉ anᵉ equivalence.ᵉ

Inᵉ fact,ᵉ theᵉ aboveᵉ argumentᵉ showsᵉ thatᵉ ifᵉ theᵉ topᵉ mapᵉ `i`ᵉ hasᵉ aᵉ sectionᵉ andᵉ theᵉ
bottomᵉ mapᵉ `j`ᵉ hasᵉ aᵉ retraction,ᵉ thenᵉ theᵉ diagonalᵉ filler,ᵉ andᵉ henceᵉ allᵉ otherᵉ
mapsᵉ areᵉ equivalences.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) {iᵉ : Aᵉ → Xᵉ} {jᵉ : Bᵉ → Yᵉ} (hᵉ : Bᵉ → Xᵉ)
  (uᵉ : coherence-triangle-mapsᵉ iᵉ hᵉ fᵉ) (vᵉ : coherence-triangle-mapsᵉ jᵉ gᵉ hᵉ)
  where

  section-diagonal-filler-section-top-squareᵉ :
    sectionᵉ iᵉ → sectionᵉ hᵉ
  section-diagonal-filler-section-top-squareᵉ =
    section-right-map-triangleᵉ iᵉ hᵉ fᵉ uᵉ

  section-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ :
    is-equivᵉ iᵉ → sectionᵉ hᵉ
  section-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ =
    section-diagonal-filler-section-top-squareᵉ (section-is-equivᵉ Hᵉ)

  map-section-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ :
    is-equivᵉ iᵉ → Xᵉ → Bᵉ
  map-section-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ =
    map-sectionᵉ hᵉ
      ( section-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ)

  is-section-section-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ :
    (Hᵉ : is-equivᵉ iᵉ) →
    is-sectionᵉ hᵉ
      ( map-section-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ)
  is-section-section-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ =
    is-section-map-sectionᵉ hᵉ
      ( section-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ)

  retraction-diagonal-filler-retraction-bottom-squareᵉ :
    retractionᵉ jᵉ → retractionᵉ hᵉ
  retraction-diagonal-filler-retraction-bottom-squareᵉ =
    retraction-top-map-triangleᵉ jᵉ gᵉ hᵉ vᵉ

  retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ :
    is-equivᵉ jᵉ → retractionᵉ hᵉ
  retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Kᵉ =
    retraction-diagonal-filler-retraction-bottom-squareᵉ (retraction-is-equivᵉ Kᵉ)

  map-retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ :
    is-equivᵉ jᵉ → Xᵉ → Bᵉ
  map-retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Kᵉ =
    map-retractionᵉ hᵉ
      ( retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Kᵉ)

  is-retraction-retraction-diagonal-fller-is-equiv-top-is-equiv-bottom-squareᵉ :
    (Kᵉ : is-equivᵉ jᵉ) →
    is-retractionᵉ hᵉ
      ( map-retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Kᵉ)
  is-retraction-retraction-diagonal-fller-is-equiv-top-is-equiv-bottom-squareᵉ
    Kᵉ =
    is-retraction-map-retractionᵉ hᵉ
      ( retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Kᵉ)

  is-equiv-diagonal-filler-section-top-retraction-bottom-squareᵉ :
    sectionᵉ iᵉ → retractionᵉ jᵉ → is-equivᵉ hᵉ
  pr1ᵉ (is-equiv-diagonal-filler-section-top-retraction-bottom-squareᵉ Hᵉ Kᵉ) =
    section-diagonal-filler-section-top-squareᵉ Hᵉ
  pr2ᵉ (is-equiv-diagonal-filler-section-top-retraction-bottom-squareᵉ Hᵉ Kᵉ) =
    retraction-diagonal-filler-retraction-bottom-squareᵉ Kᵉ

  is-equiv-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ :
    is-equivᵉ iᵉ → is-equivᵉ jᵉ → is-equivᵉ hᵉ
  is-equiv-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ Kᵉ =
    is-equiv-diagonal-filler-section-top-retraction-bottom-squareᵉ
      ( section-is-equivᵉ Hᵉ)
      ( retraction-is-equivᵉ Kᵉ)

  is-equiv-left-is-equiv-top-is-equiv-bottom-squareᵉ :
    is-equivᵉ iᵉ → is-equivᵉ jᵉ → is-equivᵉ fᵉ
  is-equiv-left-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ Kᵉ =
    is-equiv-top-map-triangleᵉ iᵉ hᵉ fᵉ uᵉ
      ( is-equiv-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ Kᵉ)
      ( Hᵉ)

  is-equiv-right-is-equiv-top-is-equiv-bottom-squareᵉ :
    is-equivᵉ iᵉ → is-equivᵉ jᵉ → is-equivᵉ gᵉ
  is-equiv-right-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ Kᵉ =
    is-equiv-right-map-triangleᵉ jᵉ gᵉ hᵉ vᵉ Kᵉ
      ( is-equiv-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ Kᵉ)

  is-equiv-triple-compᵉ :
    is-equivᵉ iᵉ → is-equivᵉ jᵉ → is-equivᵉ (gᵉ ∘ᵉ hᵉ ∘ᵉ fᵉ)
  is-equiv-triple-compᵉ Hᵉ Kᵉ =
    is-equiv-compᵉ gᵉ
      ( hᵉ ∘ᵉ fᵉ)
      ( is-equiv-compᵉ hᵉ fᵉ
        ( is-equiv-left-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ Kᵉ)
        ( is-equiv-diagonal-filler-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ Kᵉ))
      ( is-equiv-right-is-equiv-top-is-equiv-bottom-squareᵉ Hᵉ Kᵉ)
```

### Being an equivalence is closed under homotopies

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  equiv-is-equiv-htpyᵉ :
    { fᵉ gᵉ : Aᵉ → Bᵉ} → (fᵉ ~ᵉ gᵉ) →
    is-equivᵉ fᵉ ≃ᵉ is-equivᵉ gᵉ
  equiv-is-equiv-htpyᵉ {fᵉ} {gᵉ} Hᵉ =
    equiv-iff-is-propᵉ
      ( is-property-is-equivᵉ fᵉ)
      ( is-property-is-equivᵉ gᵉ)
      ( is-equiv-htpyᵉ fᵉ (inv-htpyᵉ Hᵉ))
      ( is-equiv-htpyᵉ gᵉ Hᵉ)
```

### The groupoid laws for equivalences

#### Composition of equivalences is associative

```agda
associative-comp-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ} →
  (eᵉ : Aᵉ ≃ᵉ Bᵉ) (fᵉ : Bᵉ ≃ᵉ Cᵉ) (gᵉ : Cᵉ ≃ᵉ Dᵉ) →
  ((gᵉ ∘eᵉ fᵉ) ∘eᵉ eᵉ) ＝ᵉ (gᵉ ∘eᵉ (fᵉ ∘eᵉ eᵉ))
associative-comp-equivᵉ eᵉ fᵉ gᵉ = eq-equiv-eq-map-equivᵉ reflᵉ
```

#### Unit laws for composition of equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  left-unit-law-equivᵉ : (eᵉ : Xᵉ ≃ᵉ Yᵉ) → (id-equivᵉ ∘eᵉ eᵉ) ＝ᵉ eᵉ
  left-unit-law-equivᵉ eᵉ = eq-equiv-eq-map-equivᵉ reflᵉ

  right-unit-law-equivᵉ : (eᵉ : Xᵉ ≃ᵉ Yᵉ) → (eᵉ ∘eᵉ id-equivᵉ) ＝ᵉ eᵉ
  right-unit-law-equivᵉ eᵉ = eq-equiv-eq-map-equivᵉ reflᵉ
```

#### A coherence law for the unit laws for composition of equivalences

```agda
coh-unit-laws-equivᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} →
  left-unit-law-equivᵉ (id-equivᵉ {Aᵉ = Xᵉ}) ＝ᵉ
  right-unit-law-equivᵉ (id-equivᵉ {Aᵉ = Xᵉ})
coh-unit-laws-equivᵉ = apᵉ eq-equiv-eq-map-equivᵉ reflᵉ
```

#### Inverse laws for composition of equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  left-inverse-law-equivᵉ : (eᵉ : Xᵉ ≃ᵉ Yᵉ) → ((inv-equivᵉ eᵉ) ∘eᵉ eᵉ) ＝ᵉ id-equivᵉ
  left-inverse-law-equivᵉ eᵉ =
    eq-htpy-equivᵉ (is-retraction-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ))

  right-inverse-law-equivᵉ : (eᵉ : Xᵉ ≃ᵉ Yᵉ) → (eᵉ ∘eᵉ (inv-equivᵉ eᵉ)) ＝ᵉ id-equivᵉ
  right-inverse-law-equivᵉ eᵉ =
    eq-htpy-equivᵉ (is-section-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ))
```

#### `inv-equiv` is a fibered involution on equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  inv-inv-equivᵉ : (eᵉ : Xᵉ ≃ᵉ Yᵉ) → (inv-equivᵉ (inv-equivᵉ eᵉ)) ＝ᵉ eᵉ
  inv-inv-equivᵉ eᵉ = eq-equiv-eq-map-equivᵉ reflᵉ

  inv-inv-equiv'ᵉ : (eᵉ : Yᵉ ≃ᵉ Xᵉ) → (inv-equivᵉ (inv-equivᵉ eᵉ)) ＝ᵉ eᵉ
  inv-inv-equiv'ᵉ eᵉ = eq-equiv-eq-map-equivᵉ reflᵉ

  is-equiv-inv-equivᵉ : is-equivᵉ (inv-equivᵉ {Aᵉ = Xᵉ} {Bᵉ = Yᵉ})
  is-equiv-inv-equivᵉ =
    is-equiv-is-invertibleᵉ
      ( inv-equivᵉ)
      ( inv-inv-equiv'ᵉ)
      ( inv-inv-equivᵉ)

  equiv-inv-equivᵉ : (Xᵉ ≃ᵉ Yᵉ) ≃ᵉ (Yᵉ ≃ᵉ Xᵉ)
  pr1ᵉ equiv-inv-equivᵉ = inv-equivᵉ
  pr2ᵉ equiv-inv-equivᵉ = is-equiv-inv-equivᵉ
```

#### Taking the inverse equivalence distributes over composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Zᵉ : UUᵉ l3ᵉ}
  where

  distributive-inv-comp-equivᵉ :
    (eᵉ : Xᵉ ≃ᵉ Yᵉ) (fᵉ : Yᵉ ≃ᵉ Zᵉ) →
    (inv-equivᵉ (fᵉ ∘eᵉ eᵉ)) ＝ᵉ ((inv-equivᵉ eᵉ) ∘eᵉ (inv-equivᵉ fᵉ))
  distributive-inv-comp-equivᵉ eᵉ fᵉ =
    eq-htpy-equivᵉ
      ( λ xᵉ →
        map-eq-transpose-equiv-invᵉ
          ( fᵉ ∘eᵉ eᵉ)
          ( ( apᵉ (λ gᵉ → map-equivᵉ gᵉ xᵉ) (invᵉ (right-inverse-law-equivᵉ fᵉ))) ∙ᵉ
            ( apᵉ
              ( λ gᵉ → map-equivᵉ (fᵉ ∘eᵉ (gᵉ ∘eᵉ (inv-equivᵉ fᵉ))) xᵉ)
              ( invᵉ (right-inverse-law-equivᵉ eᵉ)))))

  distributive-map-inv-comp-equivᵉ :
    (eᵉ : Xᵉ ≃ᵉ Yᵉ) (fᵉ : Yᵉ ≃ᵉ Zᵉ) →
    map-inv-equivᵉ (fᵉ ∘eᵉ eᵉ) ＝ᵉ map-inv-equivᵉ eᵉ ∘ᵉ map-inv-equivᵉ fᵉ
  distributive-map-inv-comp-equivᵉ eᵉ fᵉ =
    apᵉ map-equivᵉ (distributive-inv-comp-equivᵉ eᵉ fᵉ)
```

### Postcomposition of equivalences by an equivalence is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  is-retraction-postcomp-equiv-inv-equivᵉ :
    (fᵉ : Bᵉ ≃ᵉ Cᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ) → inv-equivᵉ fᵉ ∘eᵉ (fᵉ ∘eᵉ eᵉ) ＝ᵉ eᵉ
  is-retraction-postcomp-equiv-inv-equivᵉ fᵉ eᵉ =
    eq-htpy-equivᵉ (λ xᵉ → is-retraction-map-inv-equivᵉ fᵉ (map-equivᵉ eᵉ xᵉ))

  is-section-postcomp-equiv-inv-equivᵉ :
    (fᵉ : Bᵉ ≃ᵉ Cᵉ) (eᵉ : Aᵉ ≃ᵉ Cᵉ) → fᵉ ∘eᵉ (inv-equivᵉ fᵉ ∘eᵉ eᵉ) ＝ᵉ eᵉ
  is-section-postcomp-equiv-inv-equivᵉ fᵉ eᵉ =
    eq-htpy-equivᵉ (λ xᵉ → is-section-map-inv-equivᵉ fᵉ (map-equivᵉ eᵉ xᵉ))

  is-equiv-postcomp-equiv-equivᵉ :
    (fᵉ : Bᵉ ≃ᵉ Cᵉ) → is-equivᵉ (λ (eᵉ : Aᵉ ≃ᵉ Bᵉ) → fᵉ ∘eᵉ eᵉ)
  is-equiv-postcomp-equiv-equivᵉ fᵉ =
    is-equiv-is-invertibleᵉ
      ( inv-equivᵉ fᵉ ∘eᵉ_)
      ( is-section-postcomp-equiv-inv-equivᵉ fᵉ)
      ( is-retraction-postcomp-equiv-inv-equivᵉ fᵉ)

equiv-postcomp-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} →
  (fᵉ : Bᵉ ≃ᵉ Cᵉ) → (Aᵉ : UUᵉ l1ᵉ) → (Aᵉ ≃ᵉ Bᵉ) ≃ᵉ (Aᵉ ≃ᵉ Cᵉ)
pr1ᵉ (equiv-postcomp-equivᵉ fᵉ Aᵉ) = fᵉ ∘eᵉ_
pr2ᵉ (equiv-postcomp-equivᵉ fᵉ Aᵉ) = is-equiv-postcomp-equiv-equivᵉ fᵉ
```

### Precomposition of equivalences by an equivalence is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  is-retraction-precomp-equiv-inv-equivᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) (fᵉ : Bᵉ ≃ᵉ Cᵉ) → (fᵉ ∘eᵉ eᵉ) ∘eᵉ inv-equivᵉ eᵉ ＝ᵉ fᵉ
  is-retraction-precomp-equiv-inv-equivᵉ eᵉ fᵉ =
    eq-htpy-equivᵉ (λ xᵉ → apᵉ (map-equivᵉ fᵉ) (is-section-map-inv-equivᵉ eᵉ xᵉ))

  is-section-precomp-equiv-inv-equivᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) (fᵉ : Aᵉ ≃ᵉ Cᵉ) → (fᵉ ∘eᵉ inv-equivᵉ eᵉ) ∘eᵉ eᵉ ＝ᵉ fᵉ
  is-section-precomp-equiv-inv-equivᵉ eᵉ fᵉ =
    eq-htpy-equivᵉ (λ xᵉ → apᵉ (map-equivᵉ fᵉ) (is-retraction-map-inv-equivᵉ eᵉ xᵉ))

  is-equiv-precomp-equiv-equivᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) → is-equivᵉ (λ (fᵉ : Bᵉ ≃ᵉ Cᵉ) → fᵉ ∘eᵉ eᵉ)
  is-equiv-precomp-equiv-equivᵉ eᵉ =
    is-equiv-is-invertibleᵉ
      ( _∘eᵉ inv-equivᵉ eᵉ)
      ( is-section-precomp-equiv-inv-equivᵉ eᵉ)
      ( is-retraction-precomp-equiv-inv-equivᵉ eᵉ)

equiv-precomp-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Aᵉ ≃ᵉ Bᵉ) → (Cᵉ : UUᵉ l3ᵉ) → (Bᵉ ≃ᵉ Cᵉ) ≃ᵉ (Aᵉ ≃ᵉ Cᵉ)
pr1ᵉ (equiv-precomp-equivᵉ eᵉ Cᵉ) = _∘eᵉ eᵉ
pr2ᵉ (equiv-precomp-equivᵉ eᵉ Cᵉ) = is-equiv-precomp-equiv-equivᵉ eᵉ
```

### Computing transport in the type of equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  tr-equiv-typeᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (eᵉ : Bᵉ xᵉ ≃ᵉ Cᵉ xᵉ) →
    trᵉ (λ xᵉ → Bᵉ xᵉ ≃ᵉ Cᵉ xᵉ) pᵉ eᵉ ＝ᵉ equiv-trᵉ Cᵉ pᵉ ∘eᵉ eᵉ ∘eᵉ equiv-trᵉ Bᵉ (invᵉ pᵉ)
  tr-equiv-typeᵉ reflᵉ eᵉ = eq-htpy-equivᵉ refl-htpyᵉ
```

### A cospan in which one of the legs is an equivalence is a pullback if and only if the corresponding map on the cone is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  abstract
    is-equiv-vertical-map-is-pullbackᵉ :
      is-equivᵉ gᵉ → is-pullbackᵉ fᵉ gᵉ cᵉ → is-equivᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ)
    is-equiv-vertical-map-is-pullbackᵉ is-equiv-gᵉ pbᵉ =
      is-equiv-is-contr-mapᵉ
        ( is-trunc-vertical-map-is-pullbackᵉ neg-two-𝕋ᵉ fᵉ gᵉ cᵉ pbᵉ
          ( is-contr-map-is-equivᵉ is-equiv-gᵉ))

  abstract
    is-pullback-is-equiv-vertical-mapsᵉ :
      is-equivᵉ gᵉ → is-equivᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ) → is-pullbackᵉ fᵉ gᵉ cᵉ
    is-pullback-is-equiv-vertical-mapsᵉ is-equiv-gᵉ is-equiv-pᵉ =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ
        ( λ aᵉ →
          is-equiv-is-contrᵉ
            ( map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ aᵉ)
            ( is-contr-map-is-equivᵉ is-equiv-pᵉ aᵉ)
            ( is-contr-map-is-equivᵉ is-equiv-gᵉ (fᵉ aᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  abstract
    is-equiv-horizontal-map-is-pullbackᵉ :
      is-equivᵉ fᵉ → is-pullbackᵉ fᵉ gᵉ cᵉ → is-equivᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
    is-equiv-horizontal-map-is-pullbackᵉ is-equiv-fᵉ pbᵉ =
      is-equiv-is-contr-mapᵉ
        ( is-trunc-horizontal-map-is-pullbackᵉ neg-two-𝕋ᵉ fᵉ gᵉ cᵉ pbᵉ
          ( is-contr-map-is-equivᵉ is-equiv-fᵉ))

  abstract
    is-pullback-is-equiv-horizontal-mapsᵉ :
      is-equivᵉ fᵉ → is-equivᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) → is-pullbackᵉ fᵉ gᵉ cᵉ
    is-pullback-is-equiv-horizontal-mapsᵉ is-equiv-fᵉ is-equiv-qᵉ =
      is-pullback-swap-cone'ᵉ fᵉ gᵉ cᵉ
        ( is-pullback-is-equiv-vertical-mapsᵉ gᵉ fᵉ
          ( swap-coneᵉ fᵉ gᵉ cᵉ)
          ( is-equiv-fᵉ)
          ( is-equiv-qᵉ))
```

## See also

-ᵉ Forᵉ theᵉ notionᵉ ofᵉ coherentlyᵉ invertibleᵉ maps,ᵉ alsoᵉ knownᵉ asᵉ half-adjointᵉ
  equivalences,ᵉ seeᵉ
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ mapsᵉ with contractibleᵉ fibersᵉ seeᵉ
  [`foundation.contractible-maps`](foundation.contractible-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ path-splitᵉ mapsᵉ seeᵉ
  [`foundation.path-split-maps`](foundation.path-split-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ finitelyᵉ coherentᵉ equivalence,ᵉ seeᵉ
  [`foundation.finitely-coherent-equivalence`)(foundation.finitely-coherent-equivalence.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ finitelyᵉ coherentlyᵉ invertibleᵉ map,ᵉ seeᵉ
  [`foundation.finitely-coherently-invertible-map`)(foundation.finitely-coherently-invertible-map.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ infinitelyᵉ coherentᵉ equivalence,ᵉ seeᵉ
  [`foundation.infinitely-coherent-equivalences`](foundation.infinitely-coherent-equivalences.md).ᵉ

### Table of files about function types, composition, and equivalences

{{#includeᵉ tables/composition.mdᵉ}}

## External links

-ᵉ Theᵉ
  [2-out-of-6ᵉ property](https://ncatlab.org/nlab/show/two-out-of-six+propertyᵉ)
  atᵉ $n$Labᵉ