# Propositions

```agda
module foundation-core.propositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ aᵉ {{#conceptᵉ "proposition"ᵉ Agda=is-propᵉ}} ifᵉ itsᵉ
[identityᵉ types](foundation-core.identity-types.mdᵉ) areᵉ
[contractible](foundation-core.contractible-types.md).ᵉ Thisᵉ conditionᵉ isᵉ
[equivalent](foundation-core.equivalences.mdᵉ) to theᵉ conditionᵉ thatᵉ itᵉ hasᵉ upᵉ to
identificationᵉ atᵉ mostᵉ oneᵉ element.ᵉ

## Definitions

### The predicate of being a proposition

```agda
is-propᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → UUᵉ lᵉ
is-propᵉ Aᵉ = (xᵉ yᵉ : Aᵉ) → is-contrᵉ (xᵉ ＝ᵉ yᵉ)
```

### The type of propositions

```agda
Propᵉ :
  (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Propᵉ lᵉ = Σᵉ (UUᵉ lᵉ) is-propᵉ

module _
  {lᵉ : Level}
  where

  type-Propᵉ : Propᵉ lᵉ → UUᵉ lᵉ
  type-Propᵉ Pᵉ = pr1ᵉ Pᵉ

  abstract
    is-prop-type-Propᵉ : (Pᵉ : Propᵉ lᵉ) → is-propᵉ (type-Propᵉ Pᵉ)
    is-prop-type-Propᵉ Pᵉ = pr2ᵉ Pᵉ
```

## Examples

Weᵉ proveᵉ hereᵉ onlyᵉ thatᵉ anyᵉ contractibleᵉ typeᵉ isᵉ aᵉ proposition.ᵉ Theᵉ factᵉ thatᵉ
theᵉ emptyᵉ typeᵉ andᵉ theᵉ unitᵉ typeᵉ areᵉ propositionsᵉ canᵉ beᵉ foundᵉ in

-ᵉ [`foundation.empty-types`](foundation.empty-types.md),ᵉ andᵉ
-ᵉ [`foundation.unit-type`](foundation.unit-type.md).ᵉ

## Properties

### To show that a type is a proposition we may assume it has an element

```agda
abstract
  is-prop-has-elementᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → (Xᵉ → is-propᵉ Xᵉ) → is-propᵉ Xᵉ
  is-prop-has-elementᵉ fᵉ xᵉ yᵉ = fᵉ xᵉ xᵉ yᵉ
```

### Equivalent characterizations of propositions

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  all-elements-equalᵉ : UUᵉ lᵉ
  all-elements-equalᵉ = (xᵉ yᵉ : Aᵉ) → xᵉ ＝ᵉ yᵉ

  is-proof-irrelevantᵉ : UUᵉ lᵉ
  is-proof-irrelevantᵉ = Aᵉ → is-contrᵉ Aᵉ

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  abstract
    is-prop-all-elements-equalᵉ : all-elements-equalᵉ Aᵉ → is-propᵉ Aᵉ
    pr1ᵉ (is-prop-all-elements-equalᵉ Hᵉ xᵉ yᵉ) = (invᵉ (Hᵉ xᵉ xᵉ)) ∙ᵉ (Hᵉ xᵉ yᵉ)
    pr2ᵉ (is-prop-all-elements-equalᵉ Hᵉ xᵉ .xᵉ) reflᵉ = left-invᵉ (Hᵉ xᵉ xᵉ)

  abstract
    eq-is-prop'ᵉ : is-propᵉ Aᵉ → all-elements-equalᵉ Aᵉ
    eq-is-prop'ᵉ Hᵉ xᵉ yᵉ = pr1ᵉ (Hᵉ xᵉ yᵉ)

  abstract
    eq-is-propᵉ : is-propᵉ Aᵉ → {xᵉ yᵉ : Aᵉ} → xᵉ ＝ᵉ yᵉ
    eq-is-propᵉ Hᵉ {xᵉ} {yᵉ} = eq-is-prop'ᵉ Hᵉ xᵉ yᵉ

  abstract
    is-proof-irrelevant-all-elements-equalᵉ :
      all-elements-equalᵉ Aᵉ → is-proof-irrelevantᵉ Aᵉ
    pr1ᵉ (is-proof-irrelevant-all-elements-equalᵉ Hᵉ aᵉ) = aᵉ
    pr2ᵉ (is-proof-irrelevant-all-elements-equalᵉ Hᵉ aᵉ) = Hᵉ aᵉ

  abstract
    is-proof-irrelevant-is-propᵉ : is-propᵉ Aᵉ → is-proof-irrelevantᵉ Aᵉ
    is-proof-irrelevant-is-propᵉ =
      is-proof-irrelevant-all-elements-equalᵉ ∘ᵉ eq-is-prop'ᵉ

  abstract
    is-prop-is-proof-irrelevantᵉ : is-proof-irrelevantᵉ Aᵉ → is-propᵉ Aᵉ
    is-prop-is-proof-irrelevantᵉ Hᵉ xᵉ yᵉ = is-prop-is-contrᵉ (Hᵉ xᵉ) xᵉ yᵉ

  abstract
    eq-is-proof-irrelevantᵉ : is-proof-irrelevantᵉ Aᵉ → all-elements-equalᵉ Aᵉ
    eq-is-proof-irrelevantᵉ = eq-is-prop'ᵉ ∘ᵉ is-prop-is-proof-irrelevantᵉ
```

### Propositions are closed under equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-prop-is-equivᵉ : {fᵉ : Aᵉ → Bᵉ} → is-equivᵉ fᵉ → is-propᵉ Bᵉ → is-propᵉ Aᵉ
    is-prop-is-equivᵉ {fᵉ} Eᵉ Hᵉ =
      is-prop-is-proof-irrelevantᵉ
        ( λ aᵉ → is-contr-is-equivᵉ Bᵉ fᵉ Eᵉ (is-proof-irrelevant-is-propᵉ Hᵉ (fᵉ aᵉ)))

  abstract
    is-prop-equivᵉ : Aᵉ ≃ᵉ Bᵉ → is-propᵉ Bᵉ → is-propᵉ Aᵉ
    is-prop-equivᵉ (fᵉ ,ᵉ is-equiv-fᵉ) = is-prop-is-equivᵉ is-equiv-fᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-prop-is-equiv'ᵉ : {fᵉ : Aᵉ → Bᵉ} → is-equivᵉ fᵉ → is-propᵉ Aᵉ → is-propᵉ Bᵉ
    is-prop-is-equiv'ᵉ Eᵉ Hᵉ =
      is-prop-is-equivᵉ (is-equiv-map-inv-is-equivᵉ Eᵉ) Hᵉ

  abstract
    is-prop-equiv'ᵉ : Aᵉ ≃ᵉ Bᵉ → is-propᵉ Aᵉ → is-propᵉ Bᵉ
    is-prop-equiv'ᵉ (fᵉ ,ᵉ is-equiv-fᵉ) = is-prop-is-equiv'ᵉ is-equiv-fᵉ
```

### Propositions are closed under dependent pair types

```agda
abstract
  is-prop-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-propᵉ Aᵉ → ((xᵉ : Aᵉ) → is-propᵉ (Bᵉ xᵉ)) → is-propᵉ (Σᵉ Aᵉ Bᵉ)
  is-prop-Σᵉ Hᵉ Kᵉ xᵉ yᵉ =
    is-contr-equiv'ᵉ
      ( Eq-Σᵉ xᵉ yᵉ)
      ( equiv-eq-pair-Σᵉ xᵉ yᵉ)
      ( is-contr-Σ'ᵉ
        ( Hᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ))
        ( λ pᵉ → Kᵉ (pr1ᵉ yᵉ) (trᵉ _ pᵉ (pr2ᵉ xᵉ)) (pr2ᵉ yᵉ)))

Σ-Propᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : type-Propᵉ Pᵉ → Propᵉ l2ᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (Σ-Propᵉ Pᵉ Qᵉ) = Σᵉ (type-Propᵉ Pᵉ) (λ pᵉ → type-Propᵉ (Qᵉ pᵉ))
pr2ᵉ (Σ-Propᵉ Pᵉ Qᵉ) =
  is-prop-Σᵉ
    ( is-prop-type-Propᵉ Pᵉ)
    ( λ pᵉ → is-prop-type-Propᵉ (Qᵉ pᵉ))
```

### Propositions are closed under cartesian product types

```agda
abstract
  is-prop-productᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-propᵉ Aᵉ → is-propᵉ Bᵉ → is-propᵉ (Aᵉ ×ᵉ Bᵉ)
  is-prop-productᵉ Hᵉ Kᵉ = is-prop-Σᵉ Hᵉ (λ xᵉ → Kᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
  where

  type-product-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-product-Propᵉ = type-Propᵉ Pᵉ ×ᵉ type-Propᵉ Qᵉ

  is-prop-product-Propᵉ : is-propᵉ type-product-Propᵉ
  is-prop-product-Propᵉ =
    is-prop-productᵉ (is-prop-type-Propᵉ Pᵉ) (is-prop-type-Propᵉ Qᵉ)

  product-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  product-Propᵉ = (type-product-Propᵉ ,ᵉ is-prop-product-Propᵉ)
```

### Products of families of propositions are propositions

```agda
abstract
  is-prop-Πᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    ((xᵉ : Aᵉ) → is-propᵉ (Bᵉ xᵉ)) → is-propᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
  is-prop-Πᵉ Hᵉ =
    is-prop-is-proof-irrelevantᵉ
      ( λ fᵉ → is-contr-Πᵉ (λ xᵉ → is-proof-irrelevant-is-propᵉ (Hᵉ xᵉ) (fᵉ xᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Pᵉ : Aᵉ → Propᵉ l2ᵉ)
  where

  type-Π-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-Propᵉ = (xᵉ : Aᵉ) → type-Propᵉ (Pᵉ xᵉ)

  is-prop-Π-Propᵉ : is-propᵉ type-Π-Propᵉ
  is-prop-Π-Propᵉ = is-prop-Πᵉ (λ xᵉ → is-prop-type-Propᵉ (Pᵉ xᵉ))

  Π-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ Π-Propᵉ = type-Π-Propᵉ
  pr2ᵉ Π-Propᵉ = is-prop-Π-Propᵉ
```

Weᵉ nowᵉ repeatᵉ theᵉ aboveᵉ forᵉ implicitᵉ Π-types.ᵉ

```agda
abstract
  is-prop-implicit-Πᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    ((xᵉ : Aᵉ) → is-propᵉ (Bᵉ xᵉ)) → is-propᵉ ({xᵉ : Aᵉ} → Bᵉ xᵉ)
  is-prop-implicit-Πᵉ {Aᵉ = Aᵉ} {Bᵉ} Hᵉ =
    is-prop-equivᵉ
      ( helper ,ᵉ
        ( is-equiv-is-invertibleᵉ helper' (refl-htpyᵉ) (refl-htpyᵉ)))
      ( is-prop-Πᵉ Hᵉ)
    where
      helper : ({xᵉ : Aᵉ} → Bᵉ xᵉ) → ((xᵉ : Aᵉ) → Bᵉ xᵉ)
      helper f x = f {x}
      helper' : ((xᵉ : Aᵉ) → Bᵉ xᵉ) → ({xᵉ : Aᵉ} → Bᵉ xᵉ)
      helper' f {x} = f x

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Pᵉ : Aᵉ → Propᵉ l2ᵉ)
  where

  type-implicit-Π-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-implicit-Π-Propᵉ = {xᵉ : Aᵉ} → type-Propᵉ (Pᵉ xᵉ)

  is-prop-implicit-Π-Propᵉ : is-propᵉ type-implicit-Π-Propᵉ
  is-prop-implicit-Π-Propᵉ =
    is-prop-implicit-Πᵉ (λ xᵉ → is-prop-type-Propᵉ (Pᵉ xᵉ))

  implicit-Π-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ implicit-Π-Propᵉ = type-implicit-Π-Propᵉ
  pr2ᵉ implicit-Π-Propᵉ = is-prop-implicit-Π-Propᵉ
```

### The type of functions into a proposition is a proposition

```agda
abstract
  is-prop-function-typeᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-propᵉ Bᵉ → is-propᵉ (Aᵉ → Bᵉ)
  is-prop-function-typeᵉ Hᵉ = is-prop-Πᵉ (λ _ → Hᵉ)

type-function-Propᵉ :
  {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → Propᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-function-Propᵉ Aᵉ Pᵉ = Aᵉ → type-Propᵉ Pᵉ

is-prop-function-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) →
  is-propᵉ (type-function-Propᵉ Aᵉ Pᵉ)
is-prop-function-Propᵉ Pᵉ =
  is-prop-function-typeᵉ (is-prop-type-Propᵉ Pᵉ)

function-Propᵉ :
  {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → Propᵉ l2ᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (function-Propᵉ Aᵉ Pᵉ) = type-function-Propᵉ Aᵉ Pᵉ
pr2ᵉ (function-Propᵉ Aᵉ Pᵉ) = is-prop-function-Propᵉ Pᵉ

type-hom-Propᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-hom-Propᵉ Pᵉ = type-function-Propᵉ (type-Propᵉ Pᵉ)

is-prop-hom-Propᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ) →
  is-propᵉ (type-hom-Propᵉ Pᵉ Qᵉ)
is-prop-hom-Propᵉ Pᵉ = is-prop-function-Propᵉ

hom-Propᵉ :
  {l1ᵉ l2ᵉ : Level} → Propᵉ l1ᵉ → Propᵉ l2ᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (hom-Propᵉ Pᵉ Qᵉ) = type-hom-Propᵉ Pᵉ Qᵉ
pr2ᵉ (hom-Propᵉ Pᵉ Qᵉ) = is-prop-hom-Propᵉ Pᵉ Qᵉ

infixr 5 _⇒ᵉ_
_⇒ᵉ_ = hom-Propᵉ
```

### The type of equivalences between two propositions is a proposition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-prop-equiv-is-propᵉ : is-propᵉ Aᵉ → is-propᵉ Bᵉ → is-propᵉ (Aᵉ ≃ᵉ Bᵉ)
  is-prop-equiv-is-propᵉ Hᵉ Kᵉ =
    is-prop-Σᵉ
      ( is-prop-function-typeᵉ Kᵉ)
      ( λ fᵉ →
        is-prop-productᵉ
          ( is-prop-Σᵉ
            ( is-prop-function-typeᵉ Hᵉ)
            ( λ gᵉ → is-prop-is-contrᵉ (is-contr-Πᵉ (λ yᵉ → Kᵉ (fᵉ (gᵉ yᵉ)) yᵉ))))
          ( is-prop-Σᵉ
            ( is-prop-function-typeᵉ Hᵉ)
            ( λ hᵉ → is-prop-is-contrᵉ (is-contr-Πᵉ (λ xᵉ → Hᵉ (hᵉ (fᵉ xᵉ)) xᵉ)))))

type-equiv-Propᵉ :
  { l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-equiv-Propᵉ Pᵉ Qᵉ = (type-Propᵉ Pᵉ) ≃ᵉ (type-Propᵉ Qᵉ)

abstract
  is-prop-type-equiv-Propᵉ :
    {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ) →
    is-propᵉ (type-equiv-Propᵉ Pᵉ Qᵉ)
  is-prop-type-equiv-Propᵉ Pᵉ Qᵉ =
    is-prop-equiv-is-propᵉ (is-prop-type-Propᵉ Pᵉ) (is-prop-type-Propᵉ Qᵉ)

equiv-Propᵉ :
  { l1ᵉ l2ᵉ : Level} → Propᵉ l1ᵉ → Propᵉ l2ᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (equiv-Propᵉ Pᵉ Qᵉ) = type-equiv-Propᵉ Pᵉ Qᵉ
pr2ᵉ (equiv-Propᵉ Pᵉ Qᵉ) = is-prop-type-equiv-Propᵉ Pᵉ Qᵉ
```

### A type is a proposition if and only if the type of its endomaps is contractible

```agda
abstract
  is-prop-is-contr-endomapsᵉ :
    {lᵉ : Level} (Pᵉ : UUᵉ lᵉ) → is-contrᵉ (Pᵉ → Pᵉ) → is-propᵉ Pᵉ
  is-prop-is-contr-endomapsᵉ Pᵉ Hᵉ =
    is-prop-all-elements-equalᵉ (λ xᵉ → htpy-eqᵉ (eq-is-contrᵉ Hᵉ))

abstract
  is-contr-endomaps-is-propᵉ :
    {lᵉ : Level} (Pᵉ : UUᵉ lᵉ) → is-propᵉ Pᵉ → is-contrᵉ (Pᵉ → Pᵉ)
  is-contr-endomaps-is-propᵉ Pᵉ is-prop-Pᵉ =
    is-proof-irrelevant-is-propᵉ (is-prop-function-typeᵉ is-prop-Pᵉ) idᵉ
```

### Being a proposition is a proposition

```agda
abstract
  is-prop-is-propᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-propᵉ (is-propᵉ Aᵉ)
  is-prop-is-propᵉ Aᵉ = is-prop-Πᵉ (λ xᵉ → is-prop-Πᵉ (λ yᵉ → is-property-is-contrᵉ))

is-prop-Propᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → Propᵉ lᵉ
pr1ᵉ (is-prop-Propᵉ Aᵉ) = is-propᵉ Aᵉ
pr2ᵉ (is-prop-Propᵉ Aᵉ) = is-prop-is-propᵉ Aᵉ
```

## See also

### Operations on propositions

Thereᵉ isᵉ aᵉ wideᵉ rangeᵉ ofᵉ operationsᵉ onᵉ propositionsᵉ dueᵉ to theᵉ richᵉ structureᵉ ofᵉ
intuitionisticᵉ logic.ᵉ Belowᵉ weᵉ giveᵉ aᵉ structuredᵉ overviewᵉ ofᵉ aᵉ notableᵉ selectionᵉ
ofᵉ suchᵉ operationsᵉ andᵉ theirᵉ notationᵉ in theᵉ library.ᵉ

Theᵉ listᵉ isᵉ splitᵉ intoᵉ twoᵉ sections,ᵉ theᵉ firstᵉ consistsᵉ ofᵉ operationsᵉ thatᵉ
generalizeᵉ to arbitraryᵉ typesᵉ andᵉ evenᵉ sufficientlyᵉ niceᵉ
[subuniverses](foundation.subuniverses.md),ᵉ suchᵉ asᵉ
$n$-[types](foundation-core.truncated-types.md).ᵉ

| Nameᵉ                                                        | Operatorᵉ onᵉ typesᵉ | Operatorᵉ onᵉ propositions/subtypesᵉ |
| -----------------------------------------------------------ᵉ | -----------------ᵉ | ---------------------------------ᵉ |
| [Dependentᵉ sum](foundation.dependent-pair-types.mdᵉ)         | `Σ`ᵉ               | `Σ-Prop`ᵉ                          |
| [Dependentᵉ product](foundation.dependent-function-types.mdᵉ) | `Π`ᵉ               | `Π-Prop`ᵉ                          |
| [Functions](foundation-core.function-types.mdᵉ)              | `→`ᵉ               | `⇒`ᵉ                               |
| [Logicalᵉ equivalence](foundation.logical-equivalences.mdᵉ)   | `↔`ᵉ               | `⇔`ᵉ                               |
| [Product](foundation-core.cartesian-product-types.mdᵉ)       | `×`ᵉ               | `product-Prop`ᵉ                    |
| [Join](synthetic-homotopy-theory.joins-of-types.mdᵉ)         | `*`ᵉ               | `join-Prop`ᵉ                       |
| [Exclusiveᵉ sum](foundation.exclusive-sum.mdᵉ)                | `exclusive-sum`ᵉ   | `exclusive-sum-Prop`ᵉ              |
| [Coproduct](foundation-core.coproduct-types.mdᵉ)             | `+`ᵉ               | _N/Aᵉ_                             |

Noteᵉ thatᵉ forᵉ manyᵉ operationsᵉ in theᵉ secondᵉ section,ᵉ thereᵉ isᵉ anᵉ equivalentᵉ
operationᵉ onᵉ propositionsᵉ in theᵉ first.ᵉ

| Nameᵉ                                                                         | Operatorᵉ onᵉ typesᵉ           | Operatorᵉ onᵉ propositions/subtypesᵉ        |
| ----------------------------------------------------------------------------ᵉ | ---------------------------ᵉ | ----------------------------------------ᵉ |
| [Initialᵉ object](foundation-core.empty-types.mdᵉ)                             | `empty`ᵉ                     | `empty-Prop`ᵉ                             |
| [Terminalᵉ object](foundation.unit-type.mdᵉ)                                   | `unit`ᵉ                      | `unit-Prop`ᵉ                              |
| [Existentialᵉ quantification](foundation.existential-quantification.mdᵉ)       | `exists-structure`ᵉ          | `∃`ᵉ                                      |
| [Uniqueᵉ existentialᵉ quantification](foundation.uniqueness-quantification.mdᵉ) | `uniquely-exists-structure`ᵉ | `∃!`ᵉ                                     |
| [Universalᵉ quantification](foundation.universal-quantification.mdᵉ)           |                             | `∀'`ᵉ (equivalentᵉ to `Π-Prop`ᵉ)            |
| [Conjunction](foundation.conjunction.mdᵉ)                                     |                             | `∧`ᵉ (equivalentᵉ to `product-Prop`ᵉ)       |
| [Disjunction](foundation.disjunction.mdᵉ)                                     | `disjunction-type`ᵉ          | `∨`ᵉ (equivalentᵉ to `join-Prop`ᵉ)          |
| [Exclusiveᵉ disjunction](foundation.exclusive-disjunction.mdᵉ)                 | `xor-type`ᵉ                  | `⊻`ᵉ (equivalentᵉ to `exclusive-sum-Prop`ᵉ) |
| [Negation](foundation.negation.mdᵉ)                                           | `¬`ᵉ                         | `¬'`ᵉ                                     |
| [Doubleᵉ negation](foundation.double-negation.mdᵉ)                             | `¬¬`ᵉ                        | `¬¬'`ᵉ                                    |

Weᵉ canᵉ alsoᵉ organizeᵉ theseᵉ operationsᵉ byᵉ indexedᵉ andᵉ binaryᵉ variants,ᵉ givingᵉ usᵉ
theᵉ followingᵉ tableᵉ:

| Nameᵉ                   | Binaryᵉ | Indexedᵉ |
| ----------------------ᵉ | ------ᵉ | -------ᵉ |
| Productᵉ                | `×`ᵉ    | `Π`ᵉ     |
| Conjunctionᵉ            | `∧`ᵉ    | `∀'`ᵉ    |
| Constructiveᵉ existenceᵉ | `+`ᵉ    | `Σ`ᵉ     |
| Existenceᵉ              | `∨`ᵉ    | `∃`ᵉ     |
| Uniqueᵉ existenceᵉ       | `⊻`ᵉ    | `∃!`ᵉ    |

### Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}
