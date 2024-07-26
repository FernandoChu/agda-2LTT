# The image of a map

```agda
module foundation.imagesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.sliceᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.1-typesᵉ
open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Theᵉ **image**ᵉ ofᵉ aᵉ mapᵉ isᵉ aᵉ typeᵉ thatᵉ satisfiesᵉ theᵉ
[universalᵉ propertyᵉ ofᵉ theᵉ image](foundation.universal-property-image.mdᵉ) ofᵉ aᵉ
map.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ)
  where

  subtype-imᵉ : subtypeᵉ (l1ᵉ ⊔ l2ᵉ) Xᵉ
  subtype-imᵉ xᵉ = trunc-Propᵉ (fiberᵉ fᵉ xᵉ)

  is-in-subtype-imᵉ : Xᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-in-subtype-imᵉ = is-in-subtypeᵉ subtype-imᵉ

  imᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  imᵉ = type-subtypeᵉ subtype-imᵉ

  inclusion-imᵉ : imᵉ → Xᵉ
  inclusion-imᵉ = inclusion-subtypeᵉ subtype-imᵉ

  map-unit-imᵉ : Aᵉ → imᵉ
  pr1ᵉ (map-unit-imᵉ aᵉ) = fᵉ aᵉ
  pr2ᵉ (map-unit-imᵉ aᵉ) = unit-trunc-Propᵉ (aᵉ ,ᵉ reflᵉ)

  triangle-unit-imᵉ : coherence-triangle-mapsᵉ fᵉ inclusion-imᵉ map-unit-imᵉ
  triangle-unit-imᵉ aᵉ = reflᵉ

  unit-imᵉ : hom-sliceᵉ fᵉ inclusion-imᵉ
  pr1ᵉ unit-imᵉ = map-unit-imᵉ
  pr2ᵉ unit-imᵉ = triangle-unit-imᵉ
```

## Properties

### We characterize the identity type of im f

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ)
  where

  Eq-imᵉ : imᵉ fᵉ → imᵉ fᵉ → UUᵉ l1ᵉ
  Eq-imᵉ xᵉ yᵉ = (pr1ᵉ xᵉ ＝ᵉ pr1ᵉ yᵉ)

  refl-Eq-imᵉ : (xᵉ : imᵉ fᵉ) → Eq-imᵉ xᵉ xᵉ
  refl-Eq-imᵉ xᵉ = reflᵉ

  Eq-eq-imᵉ : (xᵉ yᵉ : imᵉ fᵉ) → xᵉ ＝ᵉ yᵉ → Eq-imᵉ xᵉ yᵉ
  Eq-eq-imᵉ xᵉ .xᵉ reflᵉ = refl-Eq-imᵉ xᵉ

  abstract
    is-torsorial-Eq-imᵉ :
      (xᵉ : imᵉ fᵉ) → is-torsorialᵉ (Eq-imᵉ xᵉ)
    is-torsorial-Eq-imᵉ xᵉ =
      is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-Idᵉ (pr1ᵉ xᵉ))
        ( λ xᵉ → is-prop-type-trunc-Propᵉ)
        ( pr1ᵉ xᵉ)
        ( reflᵉ)
        ( pr2ᵉ xᵉ)

  abstract
    is-equiv-Eq-eq-imᵉ : (xᵉ yᵉ : imᵉ fᵉ) → is-equivᵉ (Eq-eq-imᵉ xᵉ yᵉ)
    is-equiv-Eq-eq-imᵉ xᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-Eq-imᵉ xᵉ)
        ( Eq-eq-imᵉ xᵉ)

  equiv-Eq-eq-imᵉ : (xᵉ yᵉ : imᵉ fᵉ) → (xᵉ ＝ᵉ yᵉ) ≃ᵉ Eq-imᵉ xᵉ yᵉ
  pr1ᵉ (equiv-Eq-eq-imᵉ xᵉ yᵉ) = Eq-eq-imᵉ xᵉ yᵉ
  pr2ᵉ (equiv-Eq-eq-imᵉ xᵉ yᵉ) = is-equiv-Eq-eq-imᵉ xᵉ yᵉ

  eq-Eq-imᵉ : (xᵉ yᵉ : imᵉ fᵉ) → Eq-imᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-Eq-imᵉ xᵉ yᵉ = map-inv-is-equivᵉ (is-equiv-Eq-eq-imᵉ xᵉ yᵉ)
```

### The image inclusion is an embedding

```agda
abstract
  is-emb-inclusion-imᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ) →
    is-embᵉ (inclusion-imᵉ fᵉ)
  is-emb-inclusion-imᵉ fᵉ = is-emb-inclusion-subtypeᵉ (trunc-Propᵉ ∘ᵉ fiberᵉ fᵉ)

emb-imᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ) → imᵉ fᵉ ↪ᵉ Xᵉ
pr1ᵉ (emb-imᵉ fᵉ) = inclusion-imᵉ fᵉ
pr2ᵉ (emb-imᵉ fᵉ) = is-emb-inclusion-imᵉ fᵉ
```

### The image inclusion is injective

```agda
abstract
  is-injective-inclusion-imᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ) →
    is-injectiveᵉ (inclusion-imᵉ fᵉ)
  is-injective-inclusion-imᵉ fᵉ = is-injective-is-embᵉ (is-emb-inclusion-imᵉ fᵉ)
```

### The unit map of the image is surjective

```agda
abstract
  is-surjective-map-unit-imᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-surjectiveᵉ (map-unit-imᵉ fᵉ)
  is-surjective-map-unit-imᵉ fᵉ (yᵉ ,ᵉ zᵉ) =
    apply-universal-property-trunc-Propᵉ zᵉ
      ( trunc-Propᵉ (fiberᵉ (map-unit-imᵉ fᵉ) (yᵉ ,ᵉ zᵉ)))
      ( αᵉ)
    where
    αᵉ : fiberᵉ fᵉ yᵉ → type-Propᵉ (trunc-Propᵉ (fiberᵉ (map-unit-imᵉ fᵉ) (yᵉ ,ᵉ zᵉ)))
    αᵉ (xᵉ ,ᵉ pᵉ) = unit-trunc-Propᵉ (xᵉ ,ᵉ eq-type-subtypeᵉ (trunc-Propᵉ ∘ᵉ fiberᵉ fᵉ) pᵉ)
```

### The image of a map into a truncated type is truncated

```agda
abstract
  is-trunc-imᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ) →
    is-truncᵉ (succ-𝕋ᵉ kᵉ) Xᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) (imᵉ fᵉ)
  is-trunc-imᵉ kᵉ fᵉ = is-trunc-embᵉ kᵉ (emb-imᵉ fᵉ)

im-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) (Xᵉ : Truncated-Typeᵉ l1ᵉ (succ-𝕋ᵉ kᵉ)) {Aᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → type-Truncated-Typeᵉ Xᵉ) → Truncated-Typeᵉ (l1ᵉ ⊔ l2ᵉ) (succ-𝕋ᵉ kᵉ)
pr1ᵉ (im-Truncated-Typeᵉ kᵉ Xᵉ fᵉ) = imᵉ fᵉ
pr2ᵉ (im-Truncated-Typeᵉ kᵉ Xᵉ fᵉ) = is-trunc-imᵉ kᵉ fᵉ (is-trunc-type-Truncated-Typeᵉ Xᵉ)
```

### The image of a map into a proposition is a proposition

```agda
abstract
  is-prop-imᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ) →
    is-propᵉ Xᵉ → is-propᵉ (imᵉ fᵉ)
  is-prop-imᵉ = is-trunc-imᵉ neg-two-𝕋ᵉ

im-Propᵉ :
    {l1ᵉ l2ᵉ : Level} (Xᵉ : Propᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ}
    (fᵉ : Aᵉ → type-Propᵉ Xᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
im-Propᵉ Xᵉ fᵉ = im-Truncated-Typeᵉ neg-two-𝕋ᵉ Xᵉ fᵉ
```

### The image of a map into a set is a set

```agda
abstract
  is-set-imᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ) →
    is-setᵉ Xᵉ → is-setᵉ (imᵉ fᵉ)
  is-set-imᵉ = is-trunc-imᵉ neg-one-𝕋ᵉ

im-Setᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Setᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → type-Setᵉ Xᵉ) → Setᵉ (l1ᵉ ⊔ l2ᵉ)
im-Setᵉ Xᵉ fᵉ = im-Truncated-Typeᵉ (neg-one-𝕋ᵉ) Xᵉ fᵉ
```

### The image of a map into a 1-type is a 1-type

```agda
abstract
  is-1-type-imᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ) →
    is-1-typeᵉ Xᵉ → is-1-typeᵉ (imᵉ fᵉ)
  is-1-type-imᵉ = is-trunc-imᵉ zero-𝕋ᵉ

im-1-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 1-Typeᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → type-1-Typeᵉ Xᵉ) → 1-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
im-1-Typeᵉ Xᵉ fᵉ = im-Truncated-Typeᵉ zero-𝕋ᵉ Xᵉ fᵉ
```