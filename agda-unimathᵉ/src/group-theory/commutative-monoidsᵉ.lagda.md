# Commutative monoids

```agda
module group-theory.commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.interchange-lawᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "commutativeᵉ monoid"ᵉ Agda=Commutative-Monoidᵉ}} isᵉ aᵉ
[monoid](group-theory.monoids.mdᵉ) `M`ᵉ in whichᵉ `xyᵉ = yx`ᵉ holdsᵉ forᵉ allᵉ
`xᵉ yᵉ : M`.ᵉ

## Definitions

### The predicate on monoids of being commutative

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  is-commutative-Monoidᵉ : UUᵉ lᵉ
  is-commutative-Monoidᵉ =
    (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → mul-Monoidᵉ Mᵉ xᵉ yᵉ ＝ᵉ mul-Monoidᵉ Mᵉ yᵉ xᵉ

  is-prop-is-commutative-Monoidᵉ : is-propᵉ is-commutative-Monoidᵉ
  is-prop-is-commutative-Monoidᵉ =
    is-prop-iterated-Πᵉ 2
      ( λ xᵉ yᵉ → is-set-type-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ) (mul-Monoidᵉ Mᵉ yᵉ xᵉ))

  is-commutative-prop-Monoidᵉ : Propᵉ lᵉ
  is-commutative-prop-Monoidᵉ =
    ( is-commutative-Monoidᵉ ,ᵉ is-prop-is-commutative-Monoidᵉ)
```

### Commutative monoids

```agda
Commutative-Monoidᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Commutative-Monoidᵉ lᵉ = Σᵉ (Monoidᵉ lᵉ) is-commutative-Monoidᵉ

module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  where

  monoid-Commutative-Monoidᵉ : Monoidᵉ lᵉ
  monoid-Commutative-Monoidᵉ = pr1ᵉ Mᵉ

  semigroup-Commutative-Monoidᵉ : Semigroupᵉ lᵉ
  semigroup-Commutative-Monoidᵉ = semigroup-Monoidᵉ monoid-Commutative-Monoidᵉ

  set-Commutative-Monoidᵉ : Setᵉ lᵉ
  set-Commutative-Monoidᵉ = set-Monoidᵉ monoid-Commutative-Monoidᵉ

  type-Commutative-Monoidᵉ : UUᵉ lᵉ
  type-Commutative-Monoidᵉ = type-Monoidᵉ monoid-Commutative-Monoidᵉ

  is-set-type-Commutative-Monoidᵉ : is-setᵉ type-Commutative-Monoidᵉ
  is-set-type-Commutative-Monoidᵉ = is-set-type-Monoidᵉ monoid-Commutative-Monoidᵉ
```

### The multiplicative operation of a commutative monoid

```agda
  has-associative-mul-Commutative-Monoidᵉ :
    has-associative-mul-Setᵉ set-Commutative-Monoidᵉ
  has-associative-mul-Commutative-Monoidᵉ =
    has-associative-mul-Semigroupᵉ semigroup-Commutative-Monoidᵉ

  mul-Commutative-Monoidᵉ :
    (xᵉ yᵉ : type-Commutative-Monoidᵉ) → type-Commutative-Monoidᵉ
  mul-Commutative-Monoidᵉ = mul-Monoidᵉ monoid-Commutative-Monoidᵉ

  mul-Commutative-Monoid'ᵉ :
    (xᵉ yᵉ : type-Commutative-Monoidᵉ) → type-Commutative-Monoidᵉ
  mul-Commutative-Monoid'ᵉ =
    mul-Monoid'ᵉ monoid-Commutative-Monoidᵉ

  ap-mul-Commutative-Monoidᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Commutative-Monoidᵉ} →
    xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ →
    mul-Commutative-Monoidᵉ xᵉ yᵉ ＝ᵉ mul-Commutative-Monoidᵉ x'ᵉ y'ᵉ
  ap-mul-Commutative-Monoidᵉ =
    ap-mul-Monoidᵉ monoid-Commutative-Monoidᵉ

  associative-mul-Commutative-Monoidᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Monoidᵉ) →
    ( mul-Commutative-Monoidᵉ (mul-Commutative-Monoidᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( mul-Commutative-Monoidᵉ xᵉ (mul-Commutative-Monoidᵉ yᵉ zᵉ))
  associative-mul-Commutative-Monoidᵉ =
    associative-mul-Monoidᵉ monoid-Commutative-Monoidᵉ

  commutative-mul-Commutative-Monoidᵉ :
    (xᵉ yᵉ : type-Commutative-Monoidᵉ) →
    mul-Commutative-Monoidᵉ xᵉ yᵉ ＝ᵉ mul-Commutative-Monoidᵉ yᵉ xᵉ
  commutative-mul-Commutative-Monoidᵉ = pr2ᵉ Mᵉ

  interchange-mul-mul-Commutative-Monoidᵉ :
    (xᵉ yᵉ x'ᵉ y'ᵉ : type-Commutative-Monoidᵉ) →
    ( mul-Commutative-Monoidᵉ
      ( mul-Commutative-Monoidᵉ xᵉ yᵉ)
      ( mul-Commutative-Monoidᵉ x'ᵉ y'ᵉ)) ＝ᵉ
    ( mul-Commutative-Monoidᵉ
      ( mul-Commutative-Monoidᵉ xᵉ x'ᵉ)
      ( mul-Commutative-Monoidᵉ yᵉ y'ᵉ))
  interchange-mul-mul-Commutative-Monoidᵉ =
    interchange-law-commutative-and-associativeᵉ
      mul-Commutative-Monoidᵉ
      commutative-mul-Commutative-Monoidᵉ
      associative-mul-Commutative-Monoidᵉ

  right-swap-mul-Commutative-Monoidᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Monoidᵉ) →
    mul-Commutative-Monoidᵉ (mul-Commutative-Monoidᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Commutative-Monoidᵉ (mul-Commutative-Monoidᵉ xᵉ zᵉ) yᵉ
  right-swap-mul-Commutative-Monoidᵉ xᵉ yᵉ zᵉ =
    ( associative-mul-Commutative-Monoidᵉ xᵉ yᵉ zᵉ) ∙ᵉ
    ( apᵉ
      ( mul-Commutative-Monoidᵉ xᵉ)
      ( commutative-mul-Commutative-Monoidᵉ yᵉ zᵉ)) ∙ᵉ
    ( invᵉ (associative-mul-Commutative-Monoidᵉ xᵉ zᵉ yᵉ))

  left-swap-mul-Commutative-Monoidᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Monoidᵉ) →
    mul-Commutative-Monoidᵉ xᵉ (mul-Commutative-Monoidᵉ yᵉ zᵉ) ＝ᵉ
    mul-Commutative-Monoidᵉ yᵉ (mul-Commutative-Monoidᵉ xᵉ zᵉ)
  left-swap-mul-Commutative-Monoidᵉ xᵉ yᵉ zᵉ =
    ( invᵉ (associative-mul-Commutative-Monoidᵉ xᵉ yᵉ zᵉ)) ∙ᵉ
    ( apᵉ
      ( mul-Commutative-Monoid'ᵉ zᵉ)
      ( commutative-mul-Commutative-Monoidᵉ xᵉ yᵉ)) ∙ᵉ
    ( associative-mul-Commutative-Monoidᵉ yᵉ xᵉ zᵉ)
```

### The unit element of a commutative monoid

```agda
module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  where

  has-unit-Commutative-Monoidᵉ : is-unitalᵉ (mul-Commutative-Monoidᵉ Mᵉ)
  has-unit-Commutative-Monoidᵉ =
    has-unit-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

  unit-Commutative-Monoidᵉ : type-Commutative-Monoidᵉ Mᵉ
  unit-Commutative-Monoidᵉ = unit-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

  left-unit-law-mul-Commutative-Monoidᵉ :
    (xᵉ : type-Commutative-Monoidᵉ Mᵉ) →
    mul-Commutative-Monoidᵉ Mᵉ unit-Commutative-Monoidᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Commutative-Monoidᵉ =
    left-unit-law-mul-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

  right-unit-law-mul-Commutative-Monoidᵉ :
    (xᵉ : type-Commutative-Monoidᵉ Mᵉ) →
    mul-Commutative-Monoidᵉ Mᵉ xᵉ unit-Commutative-Monoidᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Commutative-Monoidᵉ =
    right-unit-law-mul-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

  is-unit-Commutative-Monoidᵉ : type-Commutative-Monoidᵉ Mᵉ → UUᵉ lᵉ
  is-unit-Commutative-Monoidᵉ xᵉ = Idᵉ xᵉ unit-Commutative-Monoidᵉ

  is-unit-prop-Commutative-Monoidᵉ : type-Commutative-Monoidᵉ Mᵉ → Propᵉ lᵉ
  is-unit-prop-Commutative-Monoidᵉ xᵉ =
    Id-Propᵉ (set-Commutative-Monoidᵉ Mᵉ) xᵉ unit-Commutative-Monoidᵉ
```