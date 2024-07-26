# The descent property of the circle

```agda
module synthetic-homotopy-theory.descent-circleᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphismsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import structured-types.equivalences-types-equipped-with-automorphismsᵉ
open import structured-types.types-equipped-with-automorphismsᵉ

open import synthetic-homotopy-theory.free-loopsᵉ
open import synthetic-homotopy-theory.universal-property-circleᵉ
```

</details>

## Idea

Theᵉ **descentᵉ property**ᵉ ofᵉ theᵉ [circle](synthetic-homotopy-theory.circle.mdᵉ)
uniquelyᵉ characterizesᵉ typeᵉ familiesᵉ overᵉ theᵉ circle.ᵉ

## Definitions

### Descent data for the circle

Byᵉ theᵉ
[universalᵉ propertyᵉ ofᵉ theᵉ circle](synthetic-homotopy-theory.universal-property-circle.mdᵉ)
andᵉ [univalence](foundation.univalence.md),ᵉ aᵉ typeᵉ familyᵉ `Aᵉ : 𝕊¹ᵉ → U`ᵉ overᵉ theᵉ
[circle](synthetic-homotopy-theory.circle.mdᵉ) isᵉ equivalentᵉ to aᵉ typeᵉ `Xᵉ : U`ᵉ
equippedᵉ with anᵉ [automorphism](foundation.automorphisms.mdᵉ) `eᵉ : Xᵉ ≃ᵉ X`,ᵉ in aᵉ
wayᵉ madeᵉ preciseᵉ in furtherᵉ sectionsᵉ ofᵉ thisᵉ file.ᵉ Theᵉ pairᵉ `(X,ᵉ e)`ᵉ isᵉ calledᵉ
**descentᵉ data**ᵉ forᵉ theᵉ circle.ᵉ

```agda
descent-data-circleᵉ :
  ( l1ᵉ : Level) → UUᵉ (lsuc l1ᵉ)
descent-data-circleᵉ = Type-With-Automorphismᵉ

module _
  { l1ᵉ : Level} (Pᵉ : descent-data-circleᵉ l1ᵉ)
  where

  type-descent-data-circleᵉ : UUᵉ l1ᵉ
  type-descent-data-circleᵉ = type-Type-With-Automorphismᵉ Pᵉ

  aut-descent-data-circleᵉ : Autᵉ type-descent-data-circleᵉ
  aut-descent-data-circleᵉ = automorphism-Type-With-Automorphismᵉ Pᵉ

  map-descent-data-circleᵉ : type-descent-data-circleᵉ → type-descent-data-circleᵉ
  map-descent-data-circleᵉ = map-Type-With-Automorphismᵉ Pᵉ
```

### Canonical descent data for a family over the circle

Aᵉ typeᵉ familyᵉ overᵉ theᵉ circleᵉ givesᵉ riseᵉ to itsᵉ canonicalᵉ descentᵉ data,ᵉ obtainedᵉ
byᵉ evaluationᵉ atᵉ `base`ᵉ andᵉ
[transporting](foundation-core.transport-along-identifications.mdᵉ) alongᵉ `loop`.ᵉ

```agda
descent-data-family-circleᵉ :
  { l1ᵉ l2ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ) →
  ( Sᵉ → UUᵉ l2ᵉ) → descent-data-circleᵉ l2ᵉ
pr1ᵉ (descent-data-family-circleᵉ lᵉ Aᵉ) = Aᵉ (base-free-loopᵉ lᵉ)
pr2ᵉ (descent-data-family-circleᵉ lᵉ Aᵉ) = equiv-trᵉ Aᵉ (loop-free-loopᵉ lᵉ)
```

### The identity type of descent data for the circle

Anᵉ [equivalence](foundation.equivalences.mdᵉ) betweenᵉ `(X,ᵉ e)`ᵉ andᵉ `(Y,ᵉ f)`ᵉ isᵉ anᵉ
equivalenceᵉ betweenᵉ `X`ᵉ andᵉ `Y`ᵉ whichᵉ commutesᵉ with theᵉ automorphisms.ᵉ

```agda
equiv-descent-data-circleᵉ :
  { l1ᵉ l2ᵉ : Level} → descent-data-circleᵉ l1ᵉ → descent-data-circleᵉ l2ᵉ →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
equiv-descent-data-circleᵉ = equiv-Type-With-Automorphismᵉ

module _
  { l1ᵉ l2ᵉ : Level} (Pᵉ : descent-data-circleᵉ l1ᵉ) (Qᵉ : descent-data-circleᵉ l2ᵉ)
  ( αᵉ : equiv-descent-data-circleᵉ Pᵉ Qᵉ)
  where

  equiv-equiv-descent-data-circleᵉ :
    type-descent-data-circleᵉ Pᵉ ≃ᵉ type-descent-data-circleᵉ Qᵉ
  equiv-equiv-descent-data-circleᵉ =
    equiv-equiv-Type-With-Automorphismᵉ Pᵉ Qᵉ αᵉ

  map-equiv-descent-data-circleᵉ :
    type-descent-data-circleᵉ Pᵉ → type-descent-data-circleᵉ Qᵉ
  map-equiv-descent-data-circleᵉ =
    map-equiv-Type-With-Automorphismᵉ Pᵉ Qᵉ αᵉ

  coherence-square-equiv-descent-data-circleᵉ :
    coherence-square-mapsᵉ
      ( map-equiv-descent-data-circleᵉ)
      ( map-descent-data-circleᵉ Pᵉ)
      ( map-descent-data-circleᵉ Qᵉ)
      ( map-equiv-descent-data-circleᵉ)
  coherence-square-equiv-descent-data-circleᵉ =
    coherence-square-equiv-Type-With-Automorphismᵉ Pᵉ Qᵉ αᵉ
```

### A family over the circle equipped with corresponding descent data

Aᵉ **familyᵉ forᵉ descentᵉ data**ᵉ `(X,ᵉ e)`ᵉ isᵉ aᵉ familyᵉ overᵉ theᵉ circle,ᵉ alongᵉ with aᵉ
proofᵉ thatᵉ `(X,ᵉ e)`ᵉ isᵉ equivalentᵉ to theᵉ canonicalᵉ descentᵉ data ofᵉ theᵉ family.ᵉ

**Descentᵉ data forᵉ aᵉ family**ᵉ `Aᵉ : 𝕊¹ᵉ → U`ᵉ isᵉ descentᵉ data with aᵉ proofᵉ thatᵉ
it'sᵉ equivalentᵉ to theᵉ canonicalᵉ descentᵉ data ofᵉ `A`.ᵉ

Aᵉ **familyᵉ with descentᵉ data**ᵉ isᵉ aᵉ familyᵉ `Aᵉ : 𝕊¹ᵉ → U`ᵉ overᵉ theᵉ circle,ᵉ
equippedᵉ with descentᵉ data `(X,ᵉ e)`,ᵉ andᵉ aᵉ proofᵉ ofᵉ theirᵉ equivalence.ᵉ Thisᵉ canᵉ
beᵉ describedᵉ asᵉ aᵉ diagramᵉ

```text
      αᵉ
  Xᵉ ----->ᵉ Aᵉ baseᵉ
  |         |
 e|ᵉ         | trᵉ Aᵉ loopᵉ
  ∨ᵉ         ∨ᵉ
  Xᵉ ----->ᵉ Aᵉ baseᵉ
      αᵉ
```

Ideally,ᵉ everyᵉ sectionᵉ characterizingᵉ descentᵉ data ofᵉ aᵉ particularᵉ typeᵉ familyᵉ
shouldᵉ includeᵉ anᵉ elementᵉ ofᵉ typeᵉ `family-with-descent-data-circle`,ᵉ whoseᵉ typeᵉ
familyᵉ isᵉ theᵉ oneᵉ beingᵉ described.ᵉ

Noteᵉ onᵉ namingᵉ: aᵉ `-for-`ᵉ in aᵉ nameᵉ indicatesᵉ thatᵉ theᵉ particularᵉ entryᵉ containsᵉ
aᵉ proofᵉ thatᵉ it'sᵉ somehowᵉ equivalentᵉ to theᵉ structureᵉ it'sᵉ "for".ᵉ

```agda
module _
  { l1ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  where

  family-for-descent-data-circleᵉ :
    { l2ᵉ : Level} → descent-data-circleᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  family-for-descent-data-circleᵉ {l2ᵉ} Pᵉ =
    Σᵉ ( Sᵉ → UUᵉ l2ᵉ)
      ( λ Aᵉ →
        equiv-descent-data-circleᵉ
          ( Pᵉ)
          ( descent-data-family-circleᵉ lᵉ Aᵉ))

  descent-data-circle-for-familyᵉ :
    { l2ᵉ : Level} → (Sᵉ → UUᵉ l2ᵉ) → UUᵉ (lsuc l2ᵉ)
  descent-data-circle-for-familyᵉ {l2ᵉ} Aᵉ =
    Σᵉ ( descent-data-circleᵉ l2ᵉ)
      ( λ Pᵉ →
        equiv-descent-data-circleᵉ
          ( Pᵉ)
          ( descent-data-family-circleᵉ lᵉ Aᵉ))

  family-with-descent-data-circleᵉ :
    ( l2ᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  family-with-descent-data-circleᵉ l2ᵉ =
    Σᵉ ( Sᵉ → UUᵉ l2ᵉ) descent-data-circle-for-familyᵉ

module _
  { l1ᵉ l2ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {lᵉ : free-loopᵉ Sᵉ}
  ( Aᵉ : family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  where

  family-family-with-descent-data-circleᵉ : Sᵉ → UUᵉ l2ᵉ
  family-family-with-descent-data-circleᵉ = pr1ᵉ Aᵉ

  descent-data-for-family-with-descent-data-circleᵉ :
    descent-data-circle-for-familyᵉ lᵉ
      family-family-with-descent-data-circleᵉ
  descent-data-for-family-with-descent-data-circleᵉ = pr2ᵉ Aᵉ

  descent-data-family-with-descent-data-circleᵉ : descent-data-circleᵉ l2ᵉ
  descent-data-family-with-descent-data-circleᵉ =
    pr1ᵉ descent-data-for-family-with-descent-data-circleᵉ

  type-family-with-descent-data-circleᵉ : UUᵉ l2ᵉ
  type-family-with-descent-data-circleᵉ =
    type-descent-data-circleᵉ descent-data-family-with-descent-data-circleᵉ

  aut-family-with-descent-data-circleᵉ : Autᵉ type-family-with-descent-data-circleᵉ
  aut-family-with-descent-data-circleᵉ =
    aut-descent-data-circleᵉ descent-data-family-with-descent-data-circleᵉ

  map-aut-family-with-descent-data-circleᵉ :
    type-family-with-descent-data-circleᵉ → type-family-with-descent-data-circleᵉ
  map-aut-family-with-descent-data-circleᵉ =
    map-descent-data-circleᵉ descent-data-family-with-descent-data-circleᵉ

  eq-family-with-descent-data-circleᵉ :
    equiv-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ)
      ( descent-data-family-circleᵉ lᵉ family-family-with-descent-data-circleᵉ)
  eq-family-with-descent-data-circleᵉ =
    pr2ᵉ descent-data-for-family-with-descent-data-circleᵉ

  equiv-family-with-descent-data-circleᵉ :
    type-family-with-descent-data-circleᵉ ≃ᵉ
    family-family-with-descent-data-circleᵉ (base-free-loopᵉ lᵉ)
  equiv-family-with-descent-data-circleᵉ =
    equiv-equiv-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ)
      ( descent-data-family-circleᵉ lᵉ family-family-with-descent-data-circleᵉ)
      ( eq-family-with-descent-data-circleᵉ)

  map-equiv-family-with-descent-data-circleᵉ :
    type-family-with-descent-data-circleᵉ →
    family-family-with-descent-data-circleᵉ (base-free-loopᵉ lᵉ)
  map-equiv-family-with-descent-data-circleᵉ =
    map-equivᵉ equiv-family-with-descent-data-circleᵉ

  coherence-square-family-with-descent-data-circleᵉ :
    coherence-square-mapsᵉ
      ( map-equiv-family-with-descent-data-circleᵉ)
      ( map-aut-family-with-descent-data-circleᵉ)
      ( trᵉ family-family-with-descent-data-circleᵉ (loop-free-loopᵉ lᵉ))
      ( map-equiv-family-with-descent-data-circleᵉ)
  coherence-square-family-with-descent-data-circleᵉ =
    coherence-square-equiv-descent-data-circleᵉ
      ( descent-data-family-with-descent-data-circleᵉ)
      ( descent-data-family-circleᵉ lᵉ family-family-with-descent-data-circleᵉ)
      ( eq-family-with-descent-data-circleᵉ)

  family-for-family-with-descent-data-circleᵉ :
    family-for-descent-data-circleᵉ lᵉ
      descent-data-family-with-descent-data-circleᵉ
  pr1ᵉ family-for-family-with-descent-data-circleᵉ =
    family-family-with-descent-data-circleᵉ
  pr2ᵉ family-for-family-with-descent-data-circleᵉ =
    eq-family-with-descent-data-circleᵉ
```

## Properties

### Characterization of the identity type of descent data for the circle

```agda
id-equiv-descent-data-circleᵉ :
  { l1ᵉ : Level} (Pᵉ : descent-data-circleᵉ l1ᵉ) →
  equiv-descent-data-circleᵉ Pᵉ Pᵉ
id-equiv-descent-data-circleᵉ =
  id-equiv-Type-With-Automorphismᵉ

equiv-eq-descent-data-circleᵉ :
  { l1ᵉ : Level} (Pᵉ Qᵉ : descent-data-circleᵉ l1ᵉ) →
  Pᵉ ＝ᵉ Qᵉ → equiv-descent-data-circleᵉ Pᵉ Qᵉ
equiv-eq-descent-data-circleᵉ =
  equiv-eq-Type-With-Automorphismᵉ

is-torsorial-equiv-descent-data-circleᵉ :
  { l1ᵉ : Level} (Pᵉ : descent-data-circleᵉ l1ᵉ) →
  is-torsorialᵉ (equiv-descent-data-circleᵉ Pᵉ)
is-torsorial-equiv-descent-data-circleᵉ =
  is-torsorial-equiv-Type-With-Automorphismᵉ

is-equiv-equiv-eq-descent-data-circleᵉ :
  { l1ᵉ : Level} (Pᵉ Qᵉ : descent-data-circleᵉ l1ᵉ) →
  is-equivᵉ (equiv-eq-descent-data-circleᵉ Pᵉ Qᵉ)
is-equiv-equiv-eq-descent-data-circleᵉ =
  is-equiv-equiv-eq-Type-With-Automorphismᵉ

eq-equiv-descent-data-circleᵉ :
  { l1ᵉ : Level} (Pᵉ Qᵉ : descent-data-circleᵉ l1ᵉ) →
  equiv-descent-data-circleᵉ Pᵉ Qᵉ → Pᵉ ＝ᵉ Qᵉ
eq-equiv-descent-data-circleᵉ =
  eq-equiv-Type-With-Automorphismᵉ
```

### Alternative definition of equality of descent data as homomorphisms which are equivalences

```agda
module _
  { l1ᵉ l2ᵉ : Level}
  ( Pᵉ : descent-data-circleᵉ l1ᵉ)
  ( Qᵉ : descent-data-circleᵉ l2ᵉ)
  where

  equiv-descent-data-circle'ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-descent-data-circle'ᵉ = equiv-Type-With-Automorphism'ᵉ Pᵉ Qᵉ

  compute-equiv-descent-data-circleᵉ :
    equiv-descent-data-circle'ᵉ ≃ᵉ equiv-descent-data-circleᵉ Pᵉ Qᵉ
  compute-equiv-descent-data-circleᵉ = compute-equiv-Type-With-Automorphismᵉ Pᵉ Qᵉ
```

### Uniqueness of descent data characterizing a type family over the circle

Givenᵉ aᵉ typeᵉ `X`ᵉ andᵉ anᵉ automorphismᵉ `eᵉ : Xᵉ ≃ᵉ X`,ᵉ thereᵉ isᵉ aᵉ uniqueᵉ typeᵉ familyᵉ
`𝓓(X,ᵉ eᵉ) : 𝕊¹ᵉ → U`ᵉ forᵉ whichᵉ `(X,ᵉ e)`ᵉ isᵉ descentᵉ data.ᵉ

```agda
comparison-descent-data-circleᵉ :
  ( l1ᵉ : Level) → free-loopᵉ (UUᵉ l1ᵉ) → descent-data-circleᵉ l1ᵉ
comparison-descent-data-circleᵉ l1ᵉ = totᵉ (λ Yᵉ → equiv-eqᵉ)

is-equiv-comparison-descent-data-circleᵉ :
  ( l1ᵉ : Level) → is-equivᵉ (comparison-descent-data-circleᵉ l1ᵉ)
is-equiv-comparison-descent-data-circleᵉ l1ᵉ =
  is-equiv-tot-is-fiberwise-equivᵉ (λ Yᵉ → univalenceᵉ Yᵉ Yᵉ)

module _
  { l1ᵉ l2ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  where

  triangle-comparison-descent-data-circleᵉ :
    coherence-triangle-mapsᵉ
      ( descent-data-family-circleᵉ lᵉ)
      ( comparison-descent-data-circleᵉ l2ᵉ)
      ( ev-free-loopᵉ lᵉ (UUᵉ l2ᵉ))
  triangle-comparison-descent-data-circleᵉ Aᵉ =
    eq-equiv-descent-data-circleᵉ
      ( descent-data-family-circleᵉ lᵉ Aᵉ)
      ( comparison-descent-data-circleᵉ l2ᵉ (ev-free-loopᵉ lᵉ (UUᵉ l2ᵉ) Aᵉ))
      ( id-equivᵉ ,ᵉ (htpy-eqᵉ (invᵉ (compute-map-eq-apᵉ (loop-free-loopᵉ lᵉ)))))

  is-equiv-descent-data-family-circle-universal-property-circleᵉ :
    ( up-circleᵉ : universal-property-circleᵉ lᵉ) →
    is-equivᵉ (descent-data-family-circleᵉ lᵉ)
  is-equiv-descent-data-family-circle-universal-property-circleᵉ up-circleᵉ =
    is-equiv-left-map-triangleᵉ
      ( descent-data-family-circleᵉ lᵉ)
      ( comparison-descent-data-circleᵉ l2ᵉ)
      ( ev-free-loopᵉ lᵉ (UUᵉ l2ᵉ))
      ( triangle-comparison-descent-data-circleᵉ)
      ( up-circleᵉ (UUᵉ l2ᵉ))
      ( is-equiv-comparison-descent-data-circleᵉ l2ᵉ)

unique-family-property-circleᵉ :
  { l1ᵉ : Level} (l2ᵉ : Level) {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ) →
  UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
unique-family-property-circleᵉ l2ᵉ {Sᵉ} lᵉ =
  ( Qᵉ : descent-data-circleᵉ l2ᵉ) → is-contrᵉ (family-for-descent-data-circleᵉ lᵉ Qᵉ)

module _
  { l1ᵉ l2ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( up-circleᵉ : universal-property-circleᵉ lᵉ)
  where

  unique-family-property-universal-property-circleᵉ :
    unique-family-property-circleᵉ l2ᵉ lᵉ
  unique-family-property-universal-property-circleᵉ Qᵉ =
    is-contr-is-equiv'ᵉ
      ( fiberᵉ (descent-data-family-circleᵉ lᵉ) Qᵉ)
      ( totᵉ
        ( λ Pᵉ →
          equiv-eq-descent-data-circleᵉ Qᵉ (descent-data-family-circleᵉ lᵉ Pᵉ) ∘ᵉ
          invᵉ))
      ( is-equiv-tot-is-fiberwise-equivᵉ
        ( λ Pᵉ →
          is-equiv-compᵉ _ _
            ( is-equiv-invᵉ _ _)
            ( is-equiv-equiv-eq-descent-data-circleᵉ
              ( Qᵉ)
              ( descent-data-family-circleᵉ lᵉ Pᵉ))))
      ( is-contr-map-is-equivᵉ
        ( is-equiv-descent-data-family-circle-universal-property-circleᵉ
          ( lᵉ)
          ( up-circleᵉ))
        ( Qᵉ))

  family-for-descent-data-circle-descent-dataᵉ :
    ( Pᵉ : descent-data-circleᵉ l2ᵉ) →
    family-for-descent-data-circleᵉ lᵉ Pᵉ
  family-for-descent-data-circle-descent-dataᵉ Pᵉ =
    centerᵉ (unique-family-property-universal-property-circleᵉ Pᵉ)

  family-with-descent-data-circle-descent-dataᵉ :
    ( Pᵉ : descent-data-circleᵉ l2ᵉ) →
    ( family-with-descent-data-circleᵉ lᵉ l2ᵉ)
  pr1ᵉ (family-with-descent-data-circle-descent-dataᵉ Pᵉ) =
    pr1ᵉ (family-for-descent-data-circle-descent-dataᵉ Pᵉ)
  pr1ᵉ (pr2ᵉ (family-with-descent-data-circle-descent-dataᵉ Pᵉ)) = Pᵉ
  pr2ᵉ (pr2ᵉ (family-with-descent-data-circle-descent-dataᵉ Pᵉ)) =
    pr2ᵉ (family-for-descent-data-circle-descent-dataᵉ Pᵉ)
```