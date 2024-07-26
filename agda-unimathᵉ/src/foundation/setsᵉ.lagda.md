# Sets

```agda
module foundation.setsᵉ where

open import foundation-core.setsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.subuniversesᵉ
open import foundation.truncated-typesᵉ
open import foundation.univalent-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.1-typesᵉ
open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Properties

### The type of all sets in a universe is a 1-type

```agda
is-1-type-Setᵉ : {lᵉ : Level} → is-1-typeᵉ (Setᵉ lᵉ)
is-1-type-Setᵉ = is-trunc-Truncated-Typeᵉ zero-𝕋ᵉ

Set-1-Typeᵉ : (lᵉ : Level) → 1-Typeᵉ (lsuc lᵉ)
pr1ᵉ (Set-1-Typeᵉ lᵉ) = Setᵉ lᵉ
pr2ᵉ (Set-1-Typeᵉ lᵉ) = is-1-type-Setᵉ
```

### Any contractible type is a set

```agda
abstract
  is-set-is-contrᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-contrᵉ Aᵉ → is-setᵉ Aᵉ
  is-set-is-contrᵉ = is-trunc-is-contrᵉ zero-𝕋ᵉ
```

### Sets are closed under dependent pair types

```agda
abstract
  is-set-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-setᵉ Aᵉ → ((xᵉ : Aᵉ) → is-setᵉ (Bᵉ xᵉ)) → is-setᵉ (Σᵉ Aᵉ Bᵉ)
  is-set-Σᵉ = is-trunc-Σᵉ {kᵉ = zero-𝕋ᵉ}

Σ-Setᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) (Bᵉ : pr1ᵉ Aᵉ → Setᵉ l2ᵉ) → Setᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (Σ-Setᵉ Aᵉ Bᵉ) = Σᵉ (type-Setᵉ Aᵉ) (λ xᵉ → (type-Setᵉ (Bᵉ xᵉ)))
pr2ᵉ (Σ-Setᵉ Aᵉ Bᵉ) = is-set-Σᵉ (is-set-type-Setᵉ Aᵉ) (λ xᵉ → is-set-type-Setᵉ (Bᵉ xᵉ))
```

### Sets are closed under cartesian product types

```agda
abstract
  is-set-productᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-setᵉ Aᵉ → is-setᵉ Bᵉ → is-setᵉ (Aᵉ ×ᵉ Bᵉ)
  is-set-productᵉ = is-trunc-productᵉ zero-𝕋ᵉ

product-Setᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) (Bᵉ : Setᵉ l2ᵉ) → Setᵉ (l1ᵉ ⊔ l2ᵉ)
product-Setᵉ Aᵉ Bᵉ = Σ-Setᵉ Aᵉ (λ xᵉ → Bᵉ)
```

### Being a set is a property

```agda
abstract
  is-prop-is-setᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-propᵉ (is-setᵉ Aᵉ)
  is-prop-is-setᵉ = is-prop-is-truncᵉ zero-𝕋ᵉ

is-set-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
pr1ᵉ (is-set-Propᵉ Aᵉ) = is-setᵉ Aᵉ
pr2ᵉ (is-set-Propᵉ Aᵉ) = is-prop-is-setᵉ Aᵉ
```

### The inclusion of sets into the universe is an embedding

```agda
emb-type-Setᵉ : (lᵉ : Level) → Setᵉ lᵉ ↪ᵉ UUᵉ lᵉ
emb-type-Setᵉ lᵉ = emb-type-Truncated-Typeᵉ lᵉ zero-𝕋ᵉ
```

### Products of families of sets are sets

```agda
abstract
  is-set-Πᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    ((xᵉ : Aᵉ) → is-setᵉ (Bᵉ xᵉ)) → is-setᵉ ((xᵉ : Aᵉ) → (Bᵉ xᵉ))
  is-set-Πᵉ = is-trunc-Πᵉ zero-𝕋ᵉ

type-Π-Set'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → Setᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-Π-Set'ᵉ Aᵉ Bᵉ = (xᵉ : Aᵉ) → type-Setᵉ (Bᵉ xᵉ)

is-set-type-Π-Set'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → Setᵉ l2ᵉ) → is-setᵉ (type-Π-Set'ᵉ Aᵉ Bᵉ)
is-set-type-Π-Set'ᵉ Aᵉ Bᵉ =
  is-set-Πᵉ (λ xᵉ → is-set-type-Setᵉ (Bᵉ xᵉ))

Π-Set'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → Setᵉ l2ᵉ) → Setᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (Π-Set'ᵉ Aᵉ Bᵉ) = type-Π-Set'ᵉ Aᵉ Bᵉ
pr2ᵉ (Π-Set'ᵉ Aᵉ Bᵉ) = is-set-type-Π-Set'ᵉ Aᵉ Bᵉ

function-Setᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Setᵉ l2ᵉ) → Setᵉ (l1ᵉ ⊔ l2ᵉ)
function-Setᵉ Aᵉ Bᵉ = Π-Set'ᵉ Aᵉ (λ xᵉ → Bᵉ)

type-Π-Setᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) (Bᵉ : type-Setᵉ Aᵉ → Setᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-Π-Setᵉ Aᵉ Bᵉ = type-Π-Set'ᵉ (type-Setᵉ Aᵉ) Bᵉ

is-set-type-Π-Setᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) (Bᵉ : type-Setᵉ Aᵉ → Setᵉ l2ᵉ) →
  is-setᵉ (type-Π-Setᵉ Aᵉ Bᵉ)
is-set-type-Π-Setᵉ Aᵉ Bᵉ =
  is-set-type-Π-Set'ᵉ (type-Setᵉ Aᵉ) Bᵉ

Π-Setᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) →
  (type-Setᵉ Aᵉ → Setᵉ l2ᵉ) → Setᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (Π-Setᵉ Aᵉ Bᵉ) = type-Π-Setᵉ Aᵉ Bᵉ
pr2ᵉ (Π-Setᵉ Aᵉ Bᵉ) = is-set-type-Π-Setᵉ Aᵉ Bᵉ
```

### The type of functions into a set is a set

```agda
abstract
  is-set-function-typeᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-setᵉ Bᵉ → is-setᵉ (Aᵉ → Bᵉ)
  is-set-function-typeᵉ = is-trunc-function-typeᵉ zero-𝕋ᵉ

hom-Setᵉ :
  {l1ᵉ l2ᵉ : Level} → Setᵉ l1ᵉ → Setᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
hom-Setᵉ Aᵉ Bᵉ = type-Setᵉ Aᵉ → type-Setᵉ Bᵉ

is-set-hom-Setᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) (Bᵉ : Setᵉ l2ᵉ) →
  is-setᵉ (hom-Setᵉ Aᵉ Bᵉ)
is-set-hom-Setᵉ Aᵉ Bᵉ = is-set-function-typeᵉ (is-set-type-Setᵉ Bᵉ)

hom-set-Setᵉ :
  {l1ᵉ l2ᵉ : Level} → Setᵉ l1ᵉ → Setᵉ l2ᵉ → Setᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (hom-set-Setᵉ Aᵉ Bᵉ) = hom-Setᵉ Aᵉ Bᵉ
pr2ᵉ (hom-set-Setᵉ Aᵉ Bᵉ) = is-set-hom-Setᵉ Aᵉ Bᵉ

precomp-Setᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Cᵉ : Setᵉ l3ᵉ) →
  (Bᵉ → type-Setᵉ Cᵉ) → (Aᵉ → type-Setᵉ Cᵉ)
precomp-Setᵉ fᵉ Cᵉ = precompᵉ fᵉ (type-Setᵉ Cᵉ)
```

### Extensionality of sets

```agda
module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
  where

  equiv-eq-Setᵉ : (Yᵉ : Setᵉ lᵉ) → Xᵉ ＝ᵉ Yᵉ → equiv-Setᵉ Xᵉ Yᵉ
  equiv-eq-Setᵉ = equiv-eq-subuniverseᵉ is-set-Propᵉ Xᵉ

  abstract
    is-torsorial-equiv-Setᵉ : is-torsorialᵉ (λ (Yᵉ : Setᵉ lᵉ) → equiv-Setᵉ Xᵉ Yᵉ)
    is-torsorial-equiv-Setᵉ =
      is-torsorial-equiv-subuniverseᵉ is-set-Propᵉ Xᵉ

  abstract
    is-equiv-equiv-eq-Setᵉ : (Yᵉ : Setᵉ lᵉ) → is-equivᵉ (equiv-eq-Setᵉ Yᵉ)
    is-equiv-equiv-eq-Setᵉ = is-equiv-equiv-eq-subuniverseᵉ is-set-Propᵉ Xᵉ

  eq-equiv-Setᵉ : (Yᵉ : Setᵉ lᵉ) → equiv-Setᵉ Xᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
  eq-equiv-Setᵉ Yᵉ = eq-equiv-subuniverseᵉ is-set-Propᵉ

  extensionality-Setᵉ : (Yᵉ : Setᵉ lᵉ) → (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-Setᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-Setᵉ Yᵉ) = equiv-eq-Setᵉ Yᵉ
  pr2ᵉ (extensionality-Setᵉ Yᵉ) = is-equiv-equiv-eq-Setᵉ Yᵉ
```

### If a type embeds into a set, then it is a set

```agda
abstract
  is-set-is-embᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-embᵉ fᵉ → is-setᵉ Bᵉ → is-setᵉ Aᵉ
  is-set-is-embᵉ = is-trunc-is-embᵉ neg-one-𝕋ᵉ

abstract
  is-set-embᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ ↪ᵉ Bᵉ) → is-setᵉ Bᵉ → is-setᵉ Aᵉ
  is-set-embᵉ = is-trunc-embᵉ neg-one-𝕋ᵉ
```

### Any function from a proposition into a set is an embedding

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-emb-is-prop-is-setᵉ : is-propᵉ Aᵉ → is-setᵉ Bᵉ → {fᵉ : Aᵉ → Bᵉ} → is-embᵉ fᵉ
  is-emb-is-prop-is-setᵉ is-prop-Aᵉ is-set-Bᵉ {fᵉ} =
    is-emb-is-prop-mapᵉ (λ bᵉ → is-prop-Σᵉ is-prop-Aᵉ (λ aᵉ → is-set-Bᵉ (fᵉ aᵉ) bᵉ))
```

### Sets are `k+2`-truncated for any `k`

```agda
is-trunc-is-setᵉ :
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ lᵉ} → is-setᵉ Aᵉ → is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) Aᵉ
is-trunc-is-setᵉ neg-two-𝕋ᵉ is-set-Aᵉ = is-set-Aᵉ
is-trunc-is-setᵉ (succ-𝕋ᵉ kᵉ) is-set-Aᵉ =
  is-trunc-succ-is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) (is-trunc-is-setᵉ kᵉ is-set-Aᵉ)

set-Truncated-Typeᵉ :
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) → Setᵉ lᵉ → Truncated-Typeᵉ lᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ))
pr1ᵉ (set-Truncated-Typeᵉ kᵉ Aᵉ) = type-Setᵉ Aᵉ
pr2ᵉ (set-Truncated-Typeᵉ kᵉ Aᵉ) = is-trunc-is-setᵉ kᵉ (is-set-type-Setᵉ Aᵉ)
```

### The type of equivalences is a set if the domain or codomain is a set

```agda
abstract
  is-set-equiv-is-set-codomainᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → is-setᵉ Bᵉ → is-setᵉ (Aᵉ ≃ᵉ Bᵉ)
  is-set-equiv-is-set-codomainᵉ = is-trunc-equiv-is-trunc-codomainᵉ neg-one-𝕋ᵉ

  is-set-equiv-is-set-domainᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → is-setᵉ Aᵉ → is-setᵉ (Aᵉ ≃ᵉ Bᵉ)
  is-set-equiv-is-set-domainᵉ = is-trunc-equiv-is-trunc-domainᵉ neg-one-𝕋ᵉ
```

### The canonical type family over `Set` is univalent

```agda
is-univalent-type-Setᵉ : {lᵉ : Level} → is-univalentᵉ (type-Setᵉ {lᵉ})
is-univalent-type-Setᵉ = is-univalent-inclusion-subuniverseᵉ is-set-Propᵉ
```