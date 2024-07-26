# Subtypes

```agda
module foundation-core.subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.transport-along-identificationsᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Aᵉ **subtype**ᵉ ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ familyᵉ ofᵉ
[propositions](foundation-core.propositions.mdᵉ) overᵉ `A`.ᵉ Theᵉ underlyingᵉ typeᵉ ofᵉ
aᵉ subtypeᵉ `P`ᵉ ofᵉ `A`ᵉ isᵉ theᵉ [totalᵉ space](foundation.dependent-pair-types.mdᵉ)
`Σᵉ Aᵉ B`.ᵉ

## Definitions

### Subtypes

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  is-subtypeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-subtypeᵉ = (xᵉ : Aᵉ) → is-propᵉ (Bᵉ xᵉ)

  is-propertyᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-propertyᵉ = is-subtypeᵉ

subtypeᵉ : {l1ᵉ : Level} (lᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
subtypeᵉ lᵉ Aᵉ = Aᵉ → Propᵉ lᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ)
  where

  is-in-subtypeᵉ : Aᵉ → UUᵉ l2ᵉ
  is-in-subtypeᵉ xᵉ = type-Propᵉ (Pᵉ xᵉ)

  is-prop-is-in-subtypeᵉ : (xᵉ : Aᵉ) → is-propᵉ (is-in-subtypeᵉ xᵉ)
  is-prop-is-in-subtypeᵉ xᵉ = is-prop-type-Propᵉ (Pᵉ xᵉ)

  type-subtypeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-subtypeᵉ = Σᵉ Aᵉ is-in-subtypeᵉ

  inclusion-subtypeᵉ : type-subtypeᵉ → Aᵉ
  inclusion-subtypeᵉ = pr1ᵉ

  ap-inclusion-subtypeᵉ :
    (xᵉ yᵉ : type-subtypeᵉ) →
    xᵉ ＝ᵉ yᵉ → (inclusion-subtypeᵉ xᵉ ＝ᵉ inclusion-subtypeᵉ yᵉ)
  ap-inclusion-subtypeᵉ xᵉ yᵉ pᵉ = apᵉ inclusion-subtypeᵉ pᵉ

  is-in-subtype-inclusion-subtypeᵉ :
    (xᵉ : type-subtypeᵉ) → is-in-subtypeᵉ (inclusion-subtypeᵉ xᵉ)
  is-in-subtype-inclusion-subtypeᵉ = pr2ᵉ

  eq-is-in-subtypeᵉ :
    {xᵉ : Aᵉ} {pᵉ qᵉ : is-in-subtypeᵉ xᵉ} → pᵉ ＝ᵉ qᵉ
  eq-is-in-subtypeᵉ {xᵉ} = eq-is-propᵉ (is-prop-is-in-subtypeᵉ xᵉ)

  is-closed-under-eq-subtypeᵉ :
    {xᵉ yᵉ : Aᵉ} → is-in-subtypeᵉ xᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-subtypeᵉ yᵉ
  is-closed-under-eq-subtypeᵉ pᵉ reflᵉ = pᵉ

  is-closed-under-eq-subtype'ᵉ :
    {xᵉ yᵉ : Aᵉ} → is-in-subtypeᵉ yᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-subtypeᵉ xᵉ
  is-closed-under-eq-subtype'ᵉ pᵉ reflᵉ = pᵉ
```

### The containment relation on subtypes

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  leq-prop-subtypeᵉ :
    {l2ᵉ l3ᵉ : Level} → subtypeᵉ l2ᵉ Aᵉ → subtypeᵉ l3ᵉ Aᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  leq-prop-subtypeᵉ Pᵉ Qᵉ =
    Π-Propᵉ Aᵉ (λ xᵉ → hom-Propᵉ (Pᵉ xᵉ) (Qᵉ xᵉ))

  infix 5 _⊆ᵉ_
  _⊆ᵉ_ :
    {l2ᵉ l3ᵉ : Level} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) (Qᵉ : subtypeᵉ l3ᵉ Aᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  Pᵉ ⊆ᵉ Qᵉ = type-Propᵉ (leq-prop-subtypeᵉ Pᵉ Qᵉ)

  is-prop-leq-subtypeᵉ :
    {l2ᵉ l3ᵉ : Level} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) (Qᵉ : subtypeᵉ l3ᵉ Aᵉ) → is-propᵉ (Pᵉ ⊆ᵉ Qᵉ)
  is-prop-leq-subtypeᵉ Pᵉ Qᵉ =
    is-prop-type-Propᵉ (leq-prop-subtypeᵉ Pᵉ Qᵉ)
```

## Properties

### The containment relation on subtypes is a preordering

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  refl-leq-subtypeᵉ : {l2ᵉ : Level} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) → Pᵉ ⊆ᵉ Pᵉ
  refl-leq-subtypeᵉ Pᵉ xᵉ = idᵉ

  transitive-leq-subtypeᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) (Qᵉ : subtypeᵉ l3ᵉ Aᵉ) (Rᵉ : subtypeᵉ l4ᵉ Aᵉ) →
    Qᵉ ⊆ᵉ Rᵉ → Pᵉ ⊆ᵉ Qᵉ → Pᵉ ⊆ᵉ Rᵉ
  transitive-leq-subtypeᵉ Pᵉ Qᵉ Rᵉ Hᵉ Kᵉ xᵉ = Hᵉ xᵉ ∘ᵉ Kᵉ xᵉ
```

### Equality in subtypes

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ)
  where

  Eq-type-subtypeᵉ : (xᵉ yᵉ : type-subtypeᵉ Pᵉ) → UUᵉ l1ᵉ
  Eq-type-subtypeᵉ xᵉ yᵉ = (pr1ᵉ xᵉ ＝ᵉ pr1ᵉ yᵉ)

  extensionality-type-subtype'ᵉ :
    (aᵉ bᵉ : type-subtypeᵉ Pᵉ) → (aᵉ ＝ᵉ bᵉ) ≃ᵉ (pr1ᵉ aᵉ ＝ᵉ pr1ᵉ bᵉ)
  extensionality-type-subtype'ᵉ (aᵉ ,ᵉ pᵉ) =
    extensionality-type-subtypeᵉ Pᵉ pᵉ reflᵉ (λ xᵉ → id-equivᵉ)

  eq-type-subtypeᵉ :
    {aᵉ bᵉ : type-subtypeᵉ Pᵉ} → (pr1ᵉ aᵉ ＝ᵉ pr1ᵉ bᵉ) → aᵉ ＝ᵉ bᵉ
  eq-type-subtypeᵉ {aᵉ} {bᵉ} = map-inv-equivᵉ (extensionality-type-subtype'ᵉ aᵉ bᵉ)
```

### If `B` is a subtype of `A`, then the projection map `Σ A B → A` is a propositional map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : subtypeᵉ l2ᵉ Aᵉ)
  where

  abstract
    is-prop-map-inclusion-subtypeᵉ : is-prop-mapᵉ (inclusion-subtypeᵉ Bᵉ)
    is-prop-map-inclusion-subtypeᵉ =
      ( λ xᵉ →
        is-prop-equivᵉ
          ( equiv-fiber-pr1ᵉ (is-in-subtypeᵉ Bᵉ) xᵉ)
          ( is-prop-is-in-subtypeᵉ Bᵉ xᵉ))

  prop-map-subtypeᵉ : prop-mapᵉ (type-subtypeᵉ Bᵉ) Aᵉ
  pr1ᵉ prop-map-subtypeᵉ = inclusion-subtypeᵉ Bᵉ
  pr2ᵉ prop-map-subtypeᵉ = is-prop-map-inclusion-subtypeᵉ
```

### If `B` is a subtype of `A`, then the projection map `Σ A B → A` is an embedding

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : subtypeᵉ l2ᵉ Aᵉ)
  where

  abstract
    is-emb-inclusion-subtypeᵉ : is-embᵉ (inclusion-subtypeᵉ Bᵉ)
    is-emb-inclusion-subtypeᵉ =
      is-emb-is-prop-mapᵉ
        ( is-prop-map-inclusion-subtypeᵉ Bᵉ)

  emb-subtypeᵉ : type-subtypeᵉ Bᵉ ↪ᵉ Aᵉ
  pr1ᵉ emb-subtypeᵉ = inclusion-subtypeᵉ Bᵉ
  pr2ᵉ emb-subtypeᵉ = is-emb-inclusion-subtypeᵉ

  equiv-ap-inclusion-subtypeᵉ :
    {sᵉ tᵉ : type-subtypeᵉ Bᵉ} →
    (sᵉ ＝ᵉ tᵉ) ≃ᵉ (inclusion-subtypeᵉ Bᵉ sᵉ ＝ᵉ inclusion-subtypeᵉ Bᵉ tᵉ)
  pr1ᵉ (equiv-ap-inclusion-subtypeᵉ {sᵉ} {tᵉ}) = ap-inclusion-subtypeᵉ Bᵉ sᵉ tᵉ
  pr2ᵉ (equiv-ap-inclusion-subtypeᵉ {sᵉ} {tᵉ}) = is-emb-inclusion-subtypeᵉ sᵉ tᵉ
```

### Restriction of a `k`-truncated map to a `k`-truncated map into a subtype

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : subtypeᵉ l2ᵉ Aᵉ) {Xᵉ : UUᵉ l3ᵉ}
  where

  abstract
    is-trunc-map-into-subtypeᵉ :
      {fᵉ : Xᵉ → Aᵉ} → is-trunc-mapᵉ kᵉ fᵉ →
      (pᵉ : (xᵉ : Xᵉ) → is-in-subtypeᵉ Bᵉ (fᵉ xᵉ)) →
      is-trunc-mapᵉ kᵉ {Bᵉ = type-subtypeᵉ Bᵉ} (λ xᵉ → (fᵉ xᵉ ,ᵉ pᵉ xᵉ))
    is-trunc-map-into-subtypeᵉ Hᵉ pᵉ (aᵉ ,ᵉ bᵉ) =
      is-trunc-equivᵉ kᵉ _
        ( equiv-totᵉ (λ xᵉ → extensionality-type-subtype'ᵉ Bᵉ _ _))
        ( Hᵉ aᵉ)

  trunc-map-into-subtypeᵉ :
    (fᵉ : trunc-mapᵉ kᵉ Xᵉ Aᵉ) → ((xᵉ : Xᵉ) → is-in-subtypeᵉ Bᵉ (map-trunc-mapᵉ fᵉ xᵉ)) →
    trunc-mapᵉ kᵉ Xᵉ (type-subtypeᵉ Bᵉ)
  pr1ᵉ (trunc-map-into-subtypeᵉ fᵉ pᵉ) xᵉ = (map-trunc-mapᵉ fᵉ xᵉ ,ᵉ pᵉ xᵉ)
  pr2ᵉ (trunc-map-into-subtypeᵉ fᵉ pᵉ) =
    is-trunc-map-into-subtypeᵉ
      ( is-trunc-map-map-trunc-mapᵉ fᵉ)
      ( pᵉ)
```

### Restriction of an embedding to an embedding into a subtype

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : subtypeᵉ l2ᵉ Aᵉ) {Xᵉ : UUᵉ l3ᵉ} (fᵉ : Xᵉ ↪ᵉ Aᵉ)
  (pᵉ : (xᵉ : Xᵉ) → is-in-subtypeᵉ Bᵉ (map-embᵉ fᵉ xᵉ))
  where

  map-emb-into-subtypeᵉ : Xᵉ → type-subtypeᵉ Bᵉ
  pr1ᵉ (map-emb-into-subtypeᵉ xᵉ) = map-embᵉ fᵉ xᵉ
  pr2ᵉ (map-emb-into-subtypeᵉ xᵉ) = pᵉ xᵉ

  abstract
    is-emb-map-emb-into-subtypeᵉ : is-embᵉ map-emb-into-subtypeᵉ
    is-emb-map-emb-into-subtypeᵉ =
      is-emb-is-prop-mapᵉ
        ( is-trunc-map-into-subtypeᵉ
          ( neg-one-𝕋ᵉ)
          ( Bᵉ)
          ( is-prop-map-is-embᵉ (is-emb-map-embᵉ fᵉ))
          ( pᵉ))

  emb-into-subtypeᵉ : Xᵉ ↪ᵉ type-subtypeᵉ Bᵉ
  pr1ᵉ emb-into-subtypeᵉ = map-emb-into-subtypeᵉ
  pr2ᵉ emb-into-subtypeᵉ = is-emb-map-emb-into-subtypeᵉ
```

### If the projection map of a type family is an embedding, then the type family is a subtype

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  abstract
    is-subtype-is-emb-pr1ᵉ : is-embᵉ (pr1ᵉ {Bᵉ = Bᵉ}) → is-subtypeᵉ Bᵉ
    is-subtype-is-emb-pr1ᵉ Hᵉ xᵉ =
      is-prop-equiv'ᵉ (equiv-fiber-pr1ᵉ Bᵉ xᵉ) (is-prop-map-is-embᵉ Hᵉ xᵉ)
```

### A subtype of a `k+1`-truncated type is `k+1`-truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ)
  where

  abstract
    is-trunc-type-subtypeᵉ :
      is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) (type-subtypeᵉ Pᵉ)
    is-trunc-type-subtypeᵉ =
      is-trunc-is-embᵉ kᵉ
        ( inclusion-subtypeᵉ Pᵉ)
        ( is-emb-inclusion-subtypeᵉ Pᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ)
  where

  abstract
    is-prop-type-subtypeᵉ : is-propᵉ Aᵉ → is-propᵉ (type-subtypeᵉ Pᵉ)
    is-prop-type-subtypeᵉ = is-trunc-type-subtypeᵉ neg-two-𝕋ᵉ Pᵉ

  abstract
    is-set-type-subtypeᵉ : is-setᵉ Aᵉ → is-setᵉ (type-subtypeᵉ Pᵉ)
    is-set-type-subtypeᵉ = is-trunc-type-subtypeᵉ neg-one-𝕋ᵉ Pᵉ

prop-subpropᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Propᵉ l1ᵉ) (Pᵉ : subtypeᵉ l2ᵉ (type-Propᵉ Aᵉ)) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (prop-subpropᵉ Aᵉ Pᵉ) = type-subtypeᵉ Pᵉ
pr2ᵉ (prop-subpropᵉ Aᵉ Pᵉ) = is-prop-type-subtypeᵉ Pᵉ (is-prop-type-Propᵉ Aᵉ)

set-subsetᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) (Pᵉ : subtypeᵉ l2ᵉ (type-Setᵉ Aᵉ)) → Setᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (set-subsetᵉ Aᵉ Pᵉ) = type-subtypeᵉ Pᵉ
pr2ᵉ (set-subsetᵉ Aᵉ Pᵉ) = is-set-type-subtypeᵉ Pᵉ (is-set-type-Setᵉ Aᵉ)
```

### Logically equivalent subtypes induce equivalences on the underlying type of a subtype

```agda
equiv-type-subtypeᵉ :
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Pᵉ : Aᵉ → UUᵉ l2ᵉ} {Qᵉ : Aᵉ → UUᵉ l3ᵉ} →
  ( is-subtype-Pᵉ : is-subtypeᵉ Pᵉ) (is-subtype-Qᵉ : is-subtypeᵉ Qᵉ) →
  ( fᵉ : (xᵉ : Aᵉ) → Pᵉ xᵉ → Qᵉ xᵉ) →
  ( gᵉ : (xᵉ : Aᵉ) → Qᵉ xᵉ → Pᵉ xᵉ) →
  ( Σᵉ Aᵉ Pᵉ) ≃ᵉ (Σᵉ Aᵉ Qᵉ)
pr1ᵉ (equiv-type-subtypeᵉ is-subtype-Pᵉ is-subtype-Qᵉ fᵉ gᵉ) = totᵉ fᵉ
pr2ᵉ (equiv-type-subtypeᵉ is-subtype-Pᵉ is-subtype-Qᵉ fᵉ gᵉ) =
  is-equiv-tot-is-fiberwise-equivᵉ {fᵉ = fᵉ}
    ( λ xᵉ →
      is-equiv-has-converse-is-propᵉ
        ( is-subtype-Pᵉ xᵉ)
        ( is-subtype-Qᵉ xᵉ)
        ( gᵉ xᵉ))
```

### Equivalences of subtypes

```agda
equiv-subtype-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  (Cᵉ : Aᵉ → Propᵉ l3ᵉ) (Dᵉ : Bᵉ → Propᵉ l4ᵉ) →
  ((xᵉ : Aᵉ) → type-Propᵉ (Cᵉ xᵉ) ↔ᵉ type-Propᵉ (Dᵉ (map-equivᵉ eᵉ xᵉ))) →
  type-subtypeᵉ Cᵉ ≃ᵉ type-subtypeᵉ Dᵉ
equiv-subtype-equivᵉ eᵉ Cᵉ Dᵉ Hᵉ =
  equiv-Σᵉ (type-Propᵉ ∘ᵉ Dᵉ) eᵉ (λ xᵉ → equiv-iff'ᵉ (Cᵉ xᵉ) (Dᵉ (map-equivᵉ eᵉ xᵉ)) (Hᵉ xᵉ))
```

```agda
abstract
  is-equiv-subtype-is-equivᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
    {Pᵉ : Aᵉ → UUᵉ l3ᵉ} {Qᵉ : Bᵉ → UUᵉ l4ᵉ}
    (is-subtype-Pᵉ : is-subtypeᵉ Pᵉ) (is-subtype-Qᵉ : is-subtypeᵉ Qᵉ)
    (fᵉ : Aᵉ → Bᵉ) (gᵉ : (xᵉ : Aᵉ) → Pᵉ xᵉ → Qᵉ (fᵉ xᵉ)) →
    is-equivᵉ fᵉ → ((xᵉ : Aᵉ) → (Qᵉ (fᵉ xᵉ)) → Pᵉ xᵉ) → is-equivᵉ (map-Σᵉ Qᵉ fᵉ gᵉ)
  is-equiv-subtype-is-equivᵉ {Qᵉ = Qᵉ} is-subtype-Pᵉ is-subtype-Qᵉ fᵉ gᵉ is-equiv-fᵉ hᵉ =
    is-equiv-map-Σᵉ Qᵉ is-equiv-fᵉ
      ( λ xᵉ →
        is-equiv-has-converse-is-propᵉ
          ( is-subtype-Pᵉ xᵉ)
          ( is-subtype-Qᵉ (fᵉ xᵉ))
          ( hᵉ xᵉ))

abstract
  is-equiv-subtype-is-equiv'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
    {Pᵉ : Aᵉ → UUᵉ l3ᵉ} {Qᵉ : Bᵉ → UUᵉ l4ᵉ}
    (is-subtype-Pᵉ : is-subtypeᵉ Pᵉ) (is-subtype-Qᵉ : is-subtypeᵉ Qᵉ)
    (fᵉ : Aᵉ → Bᵉ) (gᵉ : (xᵉ : Aᵉ) → Pᵉ xᵉ → Qᵉ (fᵉ xᵉ)) →
    (is-equiv-fᵉ : is-equivᵉ fᵉ) →
    ((yᵉ : Bᵉ) → (Qᵉ yᵉ) → Pᵉ (map-inv-is-equivᵉ is-equiv-fᵉ yᵉ)) →
    is-equivᵉ (map-Σᵉ Qᵉ fᵉ gᵉ)
  is-equiv-subtype-is-equiv'ᵉ {Pᵉ = Pᵉ} {Qᵉ}
    is-subtype-Pᵉ is-subtype-Qᵉ fᵉ gᵉ is-equiv-fᵉ hᵉ =
    is-equiv-map-Σᵉ Qᵉ is-equiv-fᵉ
      ( λ xᵉ →
        is-equiv-has-converse-is-propᵉ
          ( is-subtype-Pᵉ xᵉ)
          ( is-subtype-Qᵉ (fᵉ xᵉ))
          ( (trᵉ Pᵉ (is-retraction-map-inv-is-equivᵉ is-equiv-fᵉ xᵉ)) ∘ᵉ (hᵉ (fᵉ xᵉ))))
```