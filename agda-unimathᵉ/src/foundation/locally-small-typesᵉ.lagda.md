# Locally small types

```agda
module foundation.locally-small-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.inhabited-subtypesᵉ
open import foundation.subuniversesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.small-typesᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.transport-along-identificationsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ saidᵉ to beᵉ **locallyᵉ small**ᵉ with respectᵉ to aᵉ universeᵉ `UUᵉ l`ᵉ ifᵉ itsᵉ
[identityᵉ types](foundation-core.identity-types.mdᵉ) areᵉ
[small](foundation-core.small-types.mdᵉ) with respectᵉ to thatᵉ universe.ᵉ

## Definition

### Locally small types

```agda
is-locally-smallᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
is-locally-smallᵉ lᵉ Aᵉ = (xᵉ yᵉ : Aᵉ) → is-smallᵉ lᵉ (xᵉ ＝ᵉ yᵉ)

module _
  {lᵉ l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Hᵉ : is-locally-smallᵉ lᵉ Aᵉ) (xᵉ yᵉ : Aᵉ)
  where

  type-is-locally-smallᵉ : UUᵉ lᵉ
  type-is-locally-smallᵉ = pr1ᵉ (Hᵉ xᵉ yᵉ)

  equiv-is-locally-smallᵉ : (xᵉ ＝ᵉ yᵉ) ≃ᵉ type-is-locally-smallᵉ
  equiv-is-locally-smallᵉ = pr2ᵉ (Hᵉ xᵉ yᵉ)

  inv-equiv-is-locally-smallᵉ : type-is-locally-smallᵉ ≃ᵉ (xᵉ ＝ᵉ yᵉ)
  inv-equiv-is-locally-smallᵉ = inv-equivᵉ equiv-is-locally-smallᵉ

  map-equiv-is-locally-smallᵉ : (xᵉ ＝ᵉ yᵉ) → type-is-locally-smallᵉ
  map-equiv-is-locally-smallᵉ = map-equivᵉ equiv-is-locally-smallᵉ

  map-inv-equiv-is-locally-smallᵉ : type-is-locally-smallᵉ → (xᵉ ＝ᵉ yᵉ)
  map-inv-equiv-is-locally-smallᵉ = map-inv-equivᵉ equiv-is-locally-smallᵉ
```

### The subuniverse of `UU l1`-locally small types in `UU l2`

```agda
Locally-Small-Typeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Locally-Small-Typeᵉ l1ᵉ l2ᵉ = Σᵉ (UUᵉ l2ᵉ) (is-locally-smallᵉ l1ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Locally-Small-Typeᵉ l1ᵉ l2ᵉ)
  where

  type-Locally-Small-Typeᵉ : UUᵉ l2ᵉ
  type-Locally-Small-Typeᵉ = pr1ᵉ Aᵉ

  is-locally-small-type-Locally-Small-Typeᵉ :
    is-locally-smallᵉ l1ᵉ type-Locally-Small-Typeᵉ
  is-locally-small-type-Locally-Small-Typeᵉ = pr2ᵉ Aᵉ

  small-identity-type-Locally-Small-Typeᵉ :
    (xᵉ yᵉ : type-Locally-Small-Typeᵉ) → UUᵉ l1ᵉ
  small-identity-type-Locally-Small-Typeᵉ =
    type-is-locally-smallᵉ is-locally-small-type-Locally-Small-Typeᵉ

  equiv-is-locally-small-type-Locally-Small-Typeᵉ :
    (xᵉ yᵉ : type-Locally-Small-Typeᵉ) →
    (xᵉ ＝ᵉ yᵉ) ≃ᵉ small-identity-type-Locally-Small-Typeᵉ xᵉ yᵉ
  equiv-is-locally-small-type-Locally-Small-Typeᵉ =
    equiv-is-locally-smallᵉ is-locally-small-type-Locally-Small-Typeᵉ
```

## Properties

### Being locally small is a property

```agda
is-prop-is-locally-smallᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → is-propᵉ (is-locally-smallᵉ lᵉ Aᵉ)
is-prop-is-locally-smallᵉ lᵉ Aᵉ =
  is-prop-Πᵉ (λ xᵉ → is-prop-Πᵉ (λ yᵉ → is-prop-is-smallᵉ lᵉ (xᵉ ＝ᵉ yᵉ)))

is-locally-small-Propᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → Propᵉ (lsuc lᵉ ⊔ l1ᵉ)
pr1ᵉ (is-locally-small-Propᵉ lᵉ Aᵉ) = is-locally-smallᵉ lᵉ Aᵉ
pr2ᵉ (is-locally-small-Propᵉ lᵉ Aᵉ) = is-prop-is-locally-smallᵉ lᵉ Aᵉ
```

### Any type in `UU l` is `l`-locally small

```agda
is-locally-small'ᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-locally-smallᵉ lᵉ Aᵉ
is-locally-small'ᵉ xᵉ yᵉ = is-small'ᵉ
```

### Any small type is locally small

```agda
is-locally-small-is-smallᵉ :
  {lᵉ l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-smallᵉ lᵉ Aᵉ → is-locally-smallᵉ lᵉ Aᵉ
pr1ᵉ (is-locally-small-is-smallᵉ (Xᵉ ,ᵉ eᵉ) xᵉ yᵉ) =
  map-equivᵉ eᵉ xᵉ ＝ᵉ map-equivᵉ eᵉ yᵉ
pr2ᵉ (is-locally-small-is-smallᵉ (Xᵉ ,ᵉ eᵉ) xᵉ yᵉ) = equiv-apᵉ eᵉ xᵉ yᵉ
```

### Any proposition is locally small

```agda
is-locally-small-is-propᵉ :
  (lᵉ : Level) {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-propᵉ Aᵉ → is-locally-smallᵉ lᵉ Aᵉ
is-locally-small-is-propᵉ lᵉ Hᵉ xᵉ yᵉ = is-small-is-contrᵉ lᵉ (Hᵉ xᵉ yᵉ)
```

### Any univalent universe is locally small

```agda
is-locally-small-UUᵉ :
  {lᵉ : Level} → is-locally-smallᵉ lᵉ (UUᵉ lᵉ)
pr1ᵉ (is-locally-small-UUᵉ Xᵉ Yᵉ) = Xᵉ ≃ᵉ Yᵉ
pr2ᵉ (is-locally-small-UUᵉ Xᵉ Yᵉ) = equiv-univalenceᵉ
```

### Any Σ-type of locally small types is locally small

```agda
is-locally-small-Σᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  is-locally-smallᵉ l3ᵉ Aᵉ → ((xᵉ : Aᵉ) → is-locally-smallᵉ l4ᵉ (Bᵉ xᵉ)) →
  is-locally-smallᵉ (l3ᵉ ⊔ l4ᵉ) (Σᵉ Aᵉ Bᵉ)
is-locally-small-Σᵉ {Bᵉ = Bᵉ} Hᵉ Kᵉ xᵉ yᵉ =
  is-small-equivᵉ
    ( Eq-Σᵉ xᵉ yᵉ)
    ( equiv-pair-eq-Σᵉ xᵉ yᵉ)
    ( is-small-Σᵉ
      ( Hᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ))
      ( λ pᵉ → Kᵉ (pr1ᵉ yᵉ) (trᵉ Bᵉ pᵉ (pr2ᵉ xᵉ)) (pr2ᵉ yᵉ)))

Σ-Locally-Small-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Locally-Small-Typeᵉ l1ᵉ l2ᵉ) →
  (type-Locally-Small-Typeᵉ Aᵉ → Locally-Small-Typeᵉ l3ᵉ l4ᵉ) →
  Locally-Small-Typeᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
pr1ᵉ (Σ-Locally-Small-Typeᵉ Aᵉ Bᵉ) =
  Σᵉ (type-Locally-Small-Typeᵉ Aᵉ) (type-Locally-Small-Typeᵉ ∘ᵉ Bᵉ)
pr2ᵉ (Σ-Locally-Small-Typeᵉ Aᵉ Bᵉ) =
  is-locally-small-Σᵉ
    ( is-locally-small-type-Locally-Small-Typeᵉ Aᵉ)
    ( is-locally-small-type-Locally-Small-Typeᵉ ∘ᵉ Bᵉ)
```

### The underlying type of a subtype of a locally small type is locally small

```agda
is-locally-small-type-subtypeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) →
  is-locally-smallᵉ l3ᵉ Aᵉ → is-locally-smallᵉ l3ᵉ (type-subtypeᵉ Pᵉ)
is-locally-small-type-subtypeᵉ {l3ᵉ = l3ᵉ} Pᵉ Hᵉ =
  is-locally-small-Σᵉ Hᵉ
    ( λ aᵉ → is-locally-small-is-propᵉ l3ᵉ (is-prop-is-in-subtypeᵉ Pᵉ aᵉ))

type-subtype-Locally-Small-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Locally-Small-Typeᵉ l1ᵉ l2ᵉ) →
  subtypeᵉ l3ᵉ (type-Locally-Small-Typeᵉ Aᵉ) → Locally-Small-Typeᵉ l1ᵉ (l2ᵉ ⊔ l3ᵉ)
pr1ᵉ (type-subtype-Locally-Small-Typeᵉ Aᵉ Pᵉ) = type-subtypeᵉ Pᵉ
pr2ᵉ (type-subtype-Locally-Small-Typeᵉ Aᵉ Pᵉ) =
  is-locally-small-type-subtypeᵉ Pᵉ (is-locally-small-type-Locally-Small-Typeᵉ Aᵉ)
```

### Any product of locally small types indexed by a small type is small

```agda
is-locally-small-Πᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  is-smallᵉ l3ᵉ Aᵉ → ((xᵉ : Aᵉ) → is-locally-smallᵉ l4ᵉ (Bᵉ xᵉ)) →
  is-locally-smallᵉ (l3ᵉ ⊔ l4ᵉ) ((xᵉ : Aᵉ) → Bᵉ xᵉ)
is-locally-small-Πᵉ Hᵉ Kᵉ fᵉ gᵉ =
  is-small-equivᵉ
    ( fᵉ ~ᵉ gᵉ)
    ( equiv-funextᵉ)
    ( is-small-Πᵉ Hᵉ (λ xᵉ → Kᵉ xᵉ (fᵉ xᵉ) (gᵉ xᵉ)))

Π-Locally-Small-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Small-Typeᵉ l1ᵉ l2ᵉ) →
  (type-Small-Typeᵉ Aᵉ → Locally-Small-Typeᵉ l3ᵉ l4ᵉ) →
  Locally-Small-Typeᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
pr1ᵉ (Π-Locally-Small-Typeᵉ Aᵉ Bᵉ) =
  (aᵉ : type-Small-Typeᵉ Aᵉ) → type-Locally-Small-Typeᵉ (Bᵉ aᵉ)
pr2ᵉ (Π-Locally-Small-Typeᵉ Aᵉ Bᵉ) =
  is-locally-small-Πᵉ
    ( is-small-type-Small-Typeᵉ Aᵉ)
    ( is-locally-small-type-Locally-Small-Typeᵉ ∘ᵉ Bᵉ)
```

### The type of types in any given subuniverse is locally small

```agda
is-locally-small-type-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) →
  is-locally-smallᵉ l1ᵉ (type-subuniverseᵉ Pᵉ)
is-locally-small-type-subuniverseᵉ Pᵉ =
  is-locally-small-type-subtypeᵉ Pᵉ is-locally-small-UUᵉ
```

### The type of locally small types is locally small

```agda
is-locally-small-Locally-Small-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} → is-locally-smallᵉ l2ᵉ (Locally-Small-Typeᵉ l1ᵉ l2ᵉ)
is-locally-small-Locally-Small-Typeᵉ {l1ᵉ} =
  is-locally-small-type-subuniverseᵉ (is-locally-small-Propᵉ l1ᵉ)
```

### The type of truncated types is locally small

```agda
is-locally-small-Truncated-Typeᵉ :
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) → is-locally-smallᵉ lᵉ (Truncated-Typeᵉ lᵉ kᵉ)
is-locally-small-Truncated-Typeᵉ kᵉ =
  is-locally-small-type-subuniverseᵉ (is-trunc-Propᵉ kᵉ)
```

### The type of propositions is locally small

```agda
is-locally-small-type-Propᵉ :
  {lᵉ : Level} → is-locally-smallᵉ lᵉ (Propᵉ lᵉ)
is-locally-small-type-Propᵉ = is-locally-small-Truncated-Typeᵉ neg-one-𝕋ᵉ
```

### The type of subtypes of a small type is locally small

```agda
is-locally-small-subtypeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  is-smallᵉ l2ᵉ Aᵉ → is-locally-smallᵉ (l2ᵉ ⊔ l3ᵉ) (subtypeᵉ l3ᵉ Aᵉ)
is-locally-small-subtypeᵉ Hᵉ =
  is-locally-small-Πᵉ Hᵉ (λ _ → is-locally-small-type-Propᵉ)
```

### The type of inhabited subtypes of a small type is locally small

```agda
is-locally-small-inhabited-subtypeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  is-smallᵉ l2ᵉ Aᵉ → is-locally-smallᵉ (l2ᵉ ⊔ l3ᵉ) (inhabited-subtypeᵉ l3ᵉ Aᵉ)
is-locally-small-inhabited-subtypeᵉ Hᵉ =
  is-locally-small-type-subtypeᵉ
    ( is-inhabited-subtype-Propᵉ)
    ( is-locally-small-subtypeᵉ Hᵉ)
```

## See also

-ᵉ [Theᵉ replacementᵉ axiom](foundation.replacement.mdᵉ)

## References

-ᵉ Theoremᵉ 4.6ᵉ in {{#citeᵉ Rij17}}.ᵉ
-ᵉ Sectionᵉ 2.19ᵉ in {{#citeᵉ SymmetryBook}}.ᵉ

{{#bibliographyᵉ}}