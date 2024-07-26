# Rings

```agda
module ring-theory.ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-embeddingsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.involutionsᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.commutative-monoidsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import lists.concatenation-listsᵉ
open import lists.listsᵉ

open import ring-theory.semiringsᵉ
```

</details>

## Idea

Theᵉ conceptᵉ ofᵉ ringᵉ vastlyᵉ generalizesᵉ theᵉ arithmeticalᵉ structureᵉ onᵉ theᵉ
integers.ᵉ Aᵉ ringᵉ consistsᵉ ofᵉ aᵉ setᵉ equippedᵉ with additionᵉ andᵉ multiplication,ᵉ
where theᵉ additionᵉ operationᵉ givesᵉ theᵉ ringᵉ theᵉ structureᵉ ofᵉ anᵉ abelianᵉ group,ᵉ
andᵉ theᵉ multiplicationᵉ isᵉ associative,ᵉ unital,ᵉ andᵉ distributiveᵉ overᵉ addition.ᵉ

## Definitions

### Rings

```agda
has-mul-Abᵉ : {l1ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) → UUᵉ l1ᵉ
has-mul-Abᵉ Aᵉ =
  Σᵉ ( has-associative-mul-Setᵉ (set-Abᵉ Aᵉ))
    ( λ μᵉ →
      ( is-unitalᵉ (pr1ᵉ μᵉ)) ×ᵉ
      ( ( (aᵉ bᵉ cᵉ : type-Abᵉ Aᵉ) →
          Idᵉ (pr1ᵉ μᵉ aᵉ (add-Abᵉ Aᵉ bᵉ cᵉ)) (add-Abᵉ Aᵉ (pr1ᵉ μᵉ aᵉ bᵉ) (pr1ᵉ μᵉ aᵉ cᵉ))) ×ᵉ
        ( (aᵉ bᵉ cᵉ : type-Abᵉ Aᵉ) →
          Idᵉ (pr1ᵉ μᵉ (add-Abᵉ Aᵉ aᵉ bᵉ) cᵉ) (add-Abᵉ Aᵉ (pr1ᵉ μᵉ aᵉ cᵉ) (pr1ᵉ μᵉ bᵉ cᵉ)))))

Ringᵉ : (l1ᵉ : Level) → UUᵉ (lsuc l1ᵉ)
Ringᵉ l1ᵉ = Σᵉ (Abᵉ l1ᵉ) has-mul-Abᵉ

module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  ab-Ringᵉ : Abᵉ lᵉ
  ab-Ringᵉ = pr1ᵉ Rᵉ

  group-Ringᵉ : Groupᵉ lᵉ
  group-Ringᵉ = group-Abᵉ ab-Ringᵉ

  additive-commutative-monoid-Ringᵉ : Commutative-Monoidᵉ lᵉ
  additive-commutative-monoid-Ringᵉ = commutative-monoid-Abᵉ ab-Ringᵉ

  additive-monoid-Ringᵉ : Monoidᵉ lᵉ
  additive-monoid-Ringᵉ = monoid-Abᵉ ab-Ringᵉ

  additive-semigroup-Ringᵉ : Semigroupᵉ lᵉ
  additive-semigroup-Ringᵉ = semigroup-Abᵉ ab-Ringᵉ

  set-Ringᵉ : Setᵉ lᵉ
  set-Ringᵉ = set-Abᵉ ab-Ringᵉ

  type-Ringᵉ : UUᵉ lᵉ
  type-Ringᵉ = type-Abᵉ ab-Ringᵉ

  is-set-type-Ringᵉ : is-setᵉ type-Ringᵉ
  is-set-type-Ringᵉ = is-set-type-Abᵉ ab-Ringᵉ
```

### Addition in a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  has-associative-add-Ringᵉ : has-associative-mul-Setᵉ (set-Ringᵉ Rᵉ)
  has-associative-add-Ringᵉ = has-associative-add-Abᵉ (ab-Ringᵉ Rᵉ)

  add-Ringᵉ : type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
  add-Ringᵉ = add-Abᵉ (ab-Ringᵉ Rᵉ)

  add-Ring'ᵉ : type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
  add-Ring'ᵉ = add-Ab'ᵉ (ab-Ringᵉ Rᵉ)

  ap-add-Ringᵉ :
    {xᵉ yᵉ x'ᵉ y'ᵉ : type-Ringᵉ Rᵉ} →
    Idᵉ xᵉ x'ᵉ → Idᵉ yᵉ y'ᵉ → Idᵉ (add-Ringᵉ xᵉ yᵉ) (add-Ringᵉ x'ᵉ y'ᵉ)
  ap-add-Ringᵉ = ap-add-Abᵉ (ab-Ringᵉ Rᵉ)

  associative-add-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) →
    Idᵉ (add-Ringᵉ (add-Ringᵉ xᵉ yᵉ) zᵉ) (add-Ringᵉ xᵉ (add-Ringᵉ yᵉ zᵉ))
  associative-add-Ringᵉ = associative-add-Abᵉ (ab-Ringᵉ Rᵉ)

  is-group-additive-semigroup-Ringᵉ :
    is-group-Semigroupᵉ (additive-semigroup-Ringᵉ Rᵉ)
  is-group-additive-semigroup-Ringᵉ = is-group-Abᵉ (ab-Ringᵉ Rᵉ)

  commutative-add-Ringᵉ : (xᵉ yᵉ : type-Ringᵉ Rᵉ) → Idᵉ (add-Ringᵉ xᵉ yᵉ) (add-Ringᵉ yᵉ xᵉ)
  commutative-add-Ringᵉ = commutative-add-Abᵉ (ab-Ringᵉ Rᵉ)

  interchange-add-add-Ringᵉ :
    (xᵉ yᵉ x'ᵉ y'ᵉ : type-Ringᵉ Rᵉ) →
    ( add-Ringᵉ (add-Ringᵉ xᵉ yᵉ) (add-Ringᵉ x'ᵉ y'ᵉ)) ＝ᵉ
    ( add-Ringᵉ (add-Ringᵉ xᵉ x'ᵉ) (add-Ringᵉ yᵉ y'ᵉ))
  interchange-add-add-Ringᵉ =
    interchange-add-add-Abᵉ (ab-Ringᵉ Rᵉ)

  right-swap-add-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) →
    add-Ringᵉ (add-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ add-Ringᵉ (add-Ringᵉ xᵉ zᵉ) yᵉ
  right-swap-add-Ringᵉ = right-swap-add-Abᵉ (ab-Ringᵉ Rᵉ)

  left-swap-add-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) →
    add-Ringᵉ xᵉ (add-Ringᵉ yᵉ zᵉ) ＝ᵉ add-Ringᵉ yᵉ (add-Ringᵉ xᵉ zᵉ)
  left-swap-add-Ringᵉ = left-swap-add-Abᵉ (ab-Ringᵉ Rᵉ)
```

### Addition in a ring is a binary equivalence

#### Addition on the left is an equivalence

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  left-subtraction-Ringᵉ : type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
  left-subtraction-Ringᵉ = left-subtraction-Abᵉ (ab-Ringᵉ Rᵉ)

  ap-left-subtraction-Ringᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Ringᵉ Rᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ →
    left-subtraction-Ringᵉ xᵉ yᵉ ＝ᵉ left-subtraction-Ringᵉ x'ᵉ y'ᵉ
  ap-left-subtraction-Ringᵉ =
    ap-left-subtraction-Abᵉ (ab-Ringᵉ Rᵉ)

  is-section-left-subtraction-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → (add-Ringᵉ Rᵉ xᵉ ∘ᵉ left-subtraction-Ringᵉ xᵉ) ~ᵉ idᵉ
  is-section-left-subtraction-Ringᵉ =
    is-section-left-subtraction-Abᵉ (ab-Ringᵉ Rᵉ)

  is-retraction-left-subtraction-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → (left-subtraction-Ringᵉ xᵉ ∘ᵉ add-Ringᵉ Rᵉ xᵉ) ~ᵉ idᵉ
  is-retraction-left-subtraction-Ringᵉ =
    is-retraction-left-subtraction-Abᵉ (ab-Ringᵉ Rᵉ)

  is-equiv-add-Ringᵉ : (xᵉ : type-Ringᵉ Rᵉ) → is-equivᵉ (add-Ringᵉ Rᵉ xᵉ)
  is-equiv-add-Ringᵉ = is-equiv-add-Abᵉ (ab-Ringᵉ Rᵉ)

  equiv-add-Ringᵉ : type-Ringᵉ Rᵉ → (type-Ringᵉ Rᵉ ≃ᵉ type-Ringᵉ Rᵉ)
  equiv-add-Ringᵉ = equiv-add-Abᵉ (ab-Ringᵉ Rᵉ)
```

#### Addition on the right is an equivalence

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  right-subtraction-Ringᵉ : type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
  right-subtraction-Ringᵉ = right-subtraction-Abᵉ (ab-Ringᵉ Rᵉ)

  ap-right-subtraction-Ringᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Ringᵉ Rᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ →
    right-subtraction-Ringᵉ xᵉ yᵉ ＝ᵉ right-subtraction-Ringᵉ x'ᵉ y'ᵉ
  ap-right-subtraction-Ringᵉ = ap-right-subtraction-Abᵉ (ab-Ringᵉ Rᵉ)

  is-section-right-subtraction-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) →
    (add-Ring'ᵉ Rᵉ xᵉ ∘ᵉ (λ yᵉ → right-subtraction-Ringᵉ yᵉ xᵉ)) ~ᵉ idᵉ
  is-section-right-subtraction-Ringᵉ =
    is-section-right-subtraction-Abᵉ (ab-Ringᵉ Rᵉ)

  is-retraction-right-subtraction-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) →
    ((λ yᵉ → right-subtraction-Ringᵉ yᵉ xᵉ) ∘ᵉ add-Ring'ᵉ Rᵉ xᵉ) ~ᵉ idᵉ
  is-retraction-right-subtraction-Ringᵉ =
    is-retraction-right-subtraction-Abᵉ (ab-Ringᵉ Rᵉ)

  is-equiv-add-Ring'ᵉ : (xᵉ : type-Ringᵉ Rᵉ) → is-equivᵉ (add-Ring'ᵉ Rᵉ xᵉ)
  is-equiv-add-Ring'ᵉ = is-equiv-add-Ab'ᵉ (ab-Ringᵉ Rᵉ)

  equiv-add-Ring'ᵉ : type-Ringᵉ Rᵉ → (type-Ringᵉ Rᵉ ≃ᵉ type-Ringᵉ Rᵉ)
  equiv-add-Ring'ᵉ = equiv-add-Ab'ᵉ (ab-Ringᵉ Rᵉ)
```

#### Addition in a ring is a binary equivalence

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-binary-equiv-add-Ringᵉ : is-binary-equivᵉ (add-Ringᵉ Rᵉ)
  is-binary-equiv-add-Ringᵉ = is-binary-equiv-add-Abᵉ (ab-Ringᵉ Rᵉ)
```

#### Addition in a ring is a binary embedding

```agda
  is-binary-emb-add-Ringᵉ : is-binary-embᵉ (add-Ringᵉ Rᵉ)
  is-binary-emb-add-Ringᵉ = is-binary-emb-add-Abᵉ (ab-Ringᵉ Rᵉ)

  is-emb-add-Ringᵉ : (xᵉ : type-Ringᵉ Rᵉ) → is-embᵉ (add-Ringᵉ Rᵉ xᵉ)
  is-emb-add-Ringᵉ = is-emb-add-Abᵉ (ab-Ringᵉ Rᵉ)

  is-emb-add-Ring'ᵉ : (xᵉ : type-Ringᵉ Rᵉ) → is-embᵉ (add-Ring'ᵉ Rᵉ xᵉ)
  is-emb-add-Ring'ᵉ = is-emb-add-Ab'ᵉ (ab-Ringᵉ Rᵉ)
```

#### Addition in a ring is pointwise injective from both sides

```agda
  is-injective-add-Ringᵉ : (xᵉ : type-Ringᵉ Rᵉ) → is-injectiveᵉ (add-Ringᵉ Rᵉ xᵉ)
  is-injective-add-Ringᵉ = is-injective-add-Abᵉ (ab-Ringᵉ Rᵉ)

  is-injective-add-Ring'ᵉ : (xᵉ : type-Ringᵉ Rᵉ) → is-injectiveᵉ (add-Ring'ᵉ Rᵉ xᵉ)
  is-injective-add-Ring'ᵉ = is-injective-add-Ab'ᵉ (ab-Ringᵉ Rᵉ)
```

### The zero element of a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  has-zero-Ringᵉ : is-unitalᵉ (add-Ringᵉ Rᵉ)
  has-zero-Ringᵉ = has-zero-Abᵉ (ab-Ringᵉ Rᵉ)

  zero-Ringᵉ : type-Ringᵉ Rᵉ
  zero-Ringᵉ = zero-Abᵉ (ab-Ringᵉ Rᵉ)

  is-zero-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ lᵉ
  is-zero-Ringᵉ xᵉ = Idᵉ xᵉ zero-Ringᵉ

  is-nonzero-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ lᵉ
  is-nonzero-Ringᵉ xᵉ = ¬ᵉ (is-zero-Ringᵉ xᵉ)

  is-zero-ring-Propᵉ : type-Ringᵉ Rᵉ → Propᵉ lᵉ
  is-zero-ring-Propᵉ xᵉ = Id-Propᵉ (set-Ringᵉ Rᵉ) xᵉ zero-Ringᵉ

  is-nonzero-ring-Propᵉ : type-Ringᵉ Rᵉ → Propᵉ lᵉ
  is-nonzero-ring-Propᵉ xᵉ = neg-Propᵉ (is-zero-ring-Propᵉ xᵉ)

  left-unit-law-add-Ringᵉ : (xᵉ : type-Ringᵉ Rᵉ) → Idᵉ (add-Ringᵉ Rᵉ zero-Ringᵉ xᵉ) xᵉ
  left-unit-law-add-Ringᵉ = left-unit-law-add-Abᵉ (ab-Ringᵉ Rᵉ)

  right-unit-law-add-Ringᵉ : (xᵉ : type-Ringᵉ Rᵉ) → Idᵉ (add-Ringᵉ Rᵉ xᵉ zero-Ringᵉ) xᵉ
  right-unit-law-add-Ringᵉ = right-unit-law-add-Abᵉ (ab-Ringᵉ Rᵉ)
```

### Additive inverses in a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  has-negatives-Ringᵉ :
    is-group-is-unital-Semigroupᵉ (additive-semigroup-Ringᵉ Rᵉ) (has-zero-Ringᵉ Rᵉ)
  has-negatives-Ringᵉ = has-negatives-Abᵉ (ab-Ringᵉ Rᵉ)

  neg-Ringᵉ : type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
  neg-Ringᵉ = neg-Abᵉ (ab-Ringᵉ Rᵉ)

  left-inverse-law-add-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → Idᵉ (add-Ringᵉ Rᵉ (neg-Ringᵉ xᵉ) xᵉ) (zero-Ringᵉ Rᵉ)
  left-inverse-law-add-Ringᵉ = left-inverse-law-add-Abᵉ (ab-Ringᵉ Rᵉ)

  right-inverse-law-add-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → Idᵉ (add-Ringᵉ Rᵉ xᵉ (neg-Ringᵉ xᵉ)) (zero-Ringᵉ Rᵉ)
  right-inverse-law-add-Ringᵉ = right-inverse-law-add-Abᵉ (ab-Ringᵉ Rᵉ)

  neg-neg-Ringᵉ : (xᵉ : type-Ringᵉ Rᵉ) → neg-Ringᵉ (neg-Ringᵉ xᵉ) ＝ᵉ xᵉ
  neg-neg-Ringᵉ = neg-neg-Abᵉ (ab-Ringᵉ Rᵉ)

  distributive-neg-add-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    neg-Ringᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ add-Ringᵉ Rᵉ (neg-Ringᵉ xᵉ) (neg-Ringᵉ yᵉ)
  distributive-neg-add-Ringᵉ = distributive-neg-add-Abᵉ (ab-Ringᵉ Rᵉ)

  neg-zero-Ringᵉ : neg-Ringᵉ (zero-Ringᵉ Rᵉ) ＝ᵉ (zero-Ringᵉ Rᵉ)
  neg-zero-Ringᵉ = neg-zero-Abᵉ (ab-Ringᵉ Rᵉ)

  add-and-subtract-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) →
    add-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ) (add-Ringᵉ Rᵉ (neg-Ringᵉ yᵉ) zᵉ) ＝ᵉ add-Ringᵉ Rᵉ xᵉ zᵉ
  add-and-subtract-Ringᵉ xᵉ yᵉ zᵉ =
    equational-reasoningᵉ
      add-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ) (add-Ringᵉ Rᵉ (neg-Ringᵉ yᵉ) zᵉ)
      ＝ᵉ add-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ yᵉ xᵉ) (add-Ringᵉ Rᵉ (neg-Ringᵉ yᵉ) zᵉ)
        byᵉ
        ( apᵉ
          ( add-Ring'ᵉ Rᵉ (add-Ringᵉ Rᵉ (neg-Ringᵉ yᵉ) zᵉ))
          ( commutative-add-Ringᵉ Rᵉ xᵉ yᵉ))
      ＝ᵉ add-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ yᵉ (neg-Ringᵉ yᵉ)) (add-Ringᵉ Rᵉ xᵉ zᵉ)
        byᵉ interchange-add-add-Ringᵉ Rᵉ yᵉ xᵉ (neg-Ringᵉ yᵉ) zᵉ
      ＝ᵉ add-Ringᵉ Rᵉ (zero-Ringᵉ Rᵉ) (add-Ringᵉ Rᵉ xᵉ zᵉ)
        byᵉ
        ( apᵉ
          ( add-Ring'ᵉ Rᵉ (add-Ringᵉ Rᵉ xᵉ zᵉ))
          ( right-inverse-law-add-Ringᵉ yᵉ))
      ＝ᵉ add-Ringᵉ Rᵉ xᵉ zᵉ
        byᵉ left-unit-law-add-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ xᵉ zᵉ)

  eq-is-unit-left-div-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} →
    (is-zero-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ (neg-Ringᵉ xᵉ) yᵉ)) → xᵉ ＝ᵉ yᵉ
  eq-is-unit-left-div-Ringᵉ {xᵉ} {yᵉ} Hᵉ =
    eq-is-unit-left-div-Groupᵉ (group-Ringᵉ Rᵉ) Hᵉ

  is-unit-left-div-eq-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} →
    xᵉ ＝ᵉ yᵉ → (is-zero-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ (neg-Ringᵉ xᵉ) yᵉ))
  is-unit-left-div-eq-Ringᵉ {xᵉ} {yᵉ} Hᵉ =
    is-unit-left-div-eq-Groupᵉ (group-Ringᵉ Rᵉ) Hᵉ
```

### Multiplication in a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  has-associative-mul-Ringᵉ : has-associative-mul-Setᵉ (set-Ringᵉ Rᵉ)
  has-associative-mul-Ringᵉ = pr1ᵉ (pr2ᵉ Rᵉ)

  mul-Ringᵉ : type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
  mul-Ringᵉ = pr1ᵉ has-associative-mul-Ringᵉ

  mul-Ring'ᵉ : type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
  mul-Ring'ᵉ xᵉ yᵉ = mul-Ringᵉ yᵉ xᵉ

  ap-mul-Ringᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Ringᵉ Rᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ) (qᵉ : Idᵉ yᵉ y'ᵉ) →
    Idᵉ (mul-Ringᵉ xᵉ yᵉ) (mul-Ringᵉ x'ᵉ y'ᵉ)
  ap-mul-Ringᵉ pᵉ qᵉ = ap-binaryᵉ mul-Ringᵉ pᵉ qᵉ

  associative-mul-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) →
    Idᵉ (mul-Ringᵉ (mul-Ringᵉ xᵉ yᵉ) zᵉ) (mul-Ringᵉ xᵉ (mul-Ringᵉ yᵉ zᵉ))
  associative-mul-Ringᵉ = pr2ᵉ has-associative-mul-Ringᵉ

  multiplicative-semigroup-Ringᵉ : Semigroupᵉ lᵉ
  pr1ᵉ multiplicative-semigroup-Ringᵉ = set-Ringᵉ Rᵉ
  pr2ᵉ multiplicative-semigroup-Ringᵉ = has-associative-mul-Ringᵉ

  left-distributive-mul-add-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ xᵉ (add-Ringᵉ Rᵉ yᵉ zᵉ) ＝ᵉ add-Ringᵉ Rᵉ (mul-Ringᵉ xᵉ yᵉ) (mul-Ringᵉ xᵉ zᵉ)
  left-distributive-mul-add-Ringᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Rᵉ)))

  right-distributive-mul-add-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ) zᵉ ＝ᵉ add-Ringᵉ Rᵉ (mul-Ringᵉ xᵉ zᵉ) (mul-Ringᵉ yᵉ zᵉ)
  right-distributive-mul-add-Ringᵉ =
    pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Rᵉ)))
```

### Multiplicative units in a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-unital-Ringᵉ : is-unitalᵉ (mul-Ringᵉ Rᵉ)
  is-unital-Ringᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Rᵉ))

  multiplicative-monoid-Ringᵉ : Monoidᵉ lᵉ
  pr1ᵉ multiplicative-monoid-Ringᵉ = multiplicative-semigroup-Ringᵉ Rᵉ
  pr2ᵉ multiplicative-monoid-Ringᵉ = is-unital-Ringᵉ

  one-Ringᵉ : type-Ringᵉ Rᵉ
  one-Ringᵉ = unit-Monoidᵉ multiplicative-monoid-Ringᵉ

  left-unit-law-mul-Ringᵉ : (xᵉ : type-Ringᵉ Rᵉ) → Idᵉ (mul-Ringᵉ Rᵉ one-Ringᵉ xᵉ) xᵉ
  left-unit-law-mul-Ringᵉ = left-unit-law-mul-Monoidᵉ multiplicative-monoid-Ringᵉ

  right-unit-law-mul-Ringᵉ : (xᵉ : type-Ringᵉ Rᵉ) → Idᵉ (mul-Ringᵉ Rᵉ xᵉ one-Ringᵉ) xᵉ
  right-unit-law-mul-Ringᵉ = right-unit-law-mul-Monoidᵉ multiplicative-monoid-Ringᵉ
```

### The zero laws for multiplication of a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  left-zero-law-mul-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → Idᵉ (mul-Ringᵉ Rᵉ (zero-Ringᵉ Rᵉ) xᵉ) (zero-Ringᵉ Rᵉ)
  left-zero-law-mul-Ringᵉ xᵉ =
    is-zero-is-idempotent-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( ( invᵉ
          ( right-distributive-mul-add-Ringᵉ Rᵉ (zero-Ringᵉ Rᵉ) (zero-Ringᵉ Rᵉ) xᵉ)) ∙ᵉ
        ( apᵉ (mul-Ring'ᵉ Rᵉ xᵉ) (left-unit-law-add-Ringᵉ Rᵉ (zero-Ringᵉ Rᵉ))))

  right-zero-law-mul-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → Idᵉ (mul-Ringᵉ Rᵉ xᵉ (zero-Ringᵉ Rᵉ)) (zero-Ringᵉ Rᵉ)
  right-zero-law-mul-Ringᵉ xᵉ =
    is-zero-is-idempotent-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( ( invᵉ
          ( left-distributive-mul-add-Ringᵉ Rᵉ xᵉ (zero-Ringᵉ Rᵉ) (zero-Ringᵉ Rᵉ))) ∙ᵉ
        ( apᵉ (mul-Ringᵉ Rᵉ xᵉ) (left-unit-law-add-Ringᵉ Rᵉ (zero-Ringᵉ Rᵉ))))
```

### Rings are semirings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  has-mul-Ringᵉ :
    has-mul-Commutative-Monoidᵉ (additive-commutative-monoid-Ringᵉ Rᵉ)
  pr1ᵉ has-mul-Ringᵉ = has-associative-mul-Ringᵉ Rᵉ
  pr1ᵉ (pr2ᵉ has-mul-Ringᵉ) = is-unital-Ringᵉ Rᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ has-mul-Ringᵉ)) = left-distributive-mul-add-Ringᵉ Rᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ has-mul-Ringᵉ)) = right-distributive-mul-add-Ringᵉ Rᵉ

  zero-laws-mul-Ringᵉ :
    zero-laws-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Ringᵉ Rᵉ)
      ( has-mul-Ringᵉ)
  pr1ᵉ zero-laws-mul-Ringᵉ = left-zero-law-mul-Ringᵉ Rᵉ
  pr2ᵉ zero-laws-mul-Ringᵉ = right-zero-law-mul-Ringᵉ Rᵉ

  semiring-Ringᵉ : Semiringᵉ lᵉ
  pr1ᵉ semiring-Ringᵉ = additive-commutative-monoid-Ringᵉ Rᵉ
  pr1ᵉ (pr2ᵉ semiring-Ringᵉ) = has-mul-Ringᵉ
  pr2ᵉ (pr2ᵉ semiring-Ringᵉ) = zero-laws-mul-Ringᵉ
```

### Computing multiplication with minus one in a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  neg-one-Ringᵉ : type-Ringᵉ Rᵉ
  neg-one-Ringᵉ = neg-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ)

  mul-neg-one-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → mul-Ringᵉ Rᵉ neg-one-Ringᵉ xᵉ ＝ᵉ neg-Ringᵉ Rᵉ xᵉ
  mul-neg-one-Ringᵉ xᵉ =
    is-injective-add-Ringᵉ Rᵉ xᵉ
      ( ( ( apᵉ
            ( add-Ring'ᵉ Rᵉ (mul-Ringᵉ Rᵉ neg-one-Ringᵉ xᵉ))
            ( invᵉ (left-unit-law-mul-Ringᵉ Rᵉ xᵉ))) ∙ᵉ
          ( ( invᵉ
              ( right-distributive-mul-add-Ringᵉ Rᵉ
                ( one-Ringᵉ Rᵉ)
                ( neg-one-Ringᵉ)
                ( xᵉ))) ∙ᵉ
            ( ( apᵉ
                ( mul-Ring'ᵉ Rᵉ xᵉ)
                ( right-inverse-law-add-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ))) ∙ᵉ
              ( left-zero-law-mul-Ringᵉ Rᵉ xᵉ)))) ∙ᵉ
        ( invᵉ (right-inverse-law-add-Ringᵉ Rᵉ xᵉ)))

  mul-neg-one-Ring'ᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → mul-Ringᵉ Rᵉ xᵉ neg-one-Ringᵉ ＝ᵉ neg-Ringᵉ Rᵉ xᵉ
  mul-neg-one-Ring'ᵉ xᵉ =
    is-injective-add-Ringᵉ Rᵉ xᵉ
      ( ( apᵉ
          ( add-Ring'ᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ neg-one-Ringᵉ))
          ( invᵉ (right-unit-law-mul-Ringᵉ Rᵉ xᵉ))) ∙ᵉ
        ( ( invᵉ
            ( left-distributive-mul-add-Ringᵉ Rᵉ xᵉ (one-Ringᵉ Rᵉ) neg-one-Ringᵉ)) ∙ᵉ
          ( ( apᵉ (mul-Ringᵉ Rᵉ xᵉ) (right-inverse-law-add-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ))) ∙ᵉ
            ( ( right-zero-law-mul-Ringᵉ Rᵉ xᵉ) ∙ᵉ
              ( invᵉ (right-inverse-law-add-Ringᵉ Rᵉ xᵉ))))))

  is-involution-mul-neg-one-Ringᵉ :
    is-involutionᵉ (mul-Ringᵉ Rᵉ neg-one-Ringᵉ)
  is-involution-mul-neg-one-Ringᵉ xᵉ =
    ( mul-neg-one-Ringᵉ (mul-Ringᵉ Rᵉ neg-one-Ringᵉ xᵉ)) ∙ᵉ
    ( ( apᵉ (neg-Ringᵉ Rᵉ) (mul-neg-one-Ringᵉ xᵉ)) ∙ᵉ
      ( neg-neg-Ringᵉ Rᵉ xᵉ))

  is-involution-mul-neg-one-Ring'ᵉ :
    is-involutionᵉ (mul-Ring'ᵉ Rᵉ neg-one-Ringᵉ)
  is-involution-mul-neg-one-Ring'ᵉ xᵉ =
    ( mul-neg-one-Ring'ᵉ (mul-Ringᵉ Rᵉ xᵉ neg-one-Ringᵉ)) ∙ᵉ
    ( ( apᵉ (neg-Ringᵉ Rᵉ) (mul-neg-one-Ring'ᵉ xᵉ)) ∙ᵉ
      ( neg-neg-Ringᵉ Rᵉ xᵉ))
```

### Left and right negative laws for multiplication

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  left-negative-law-mul-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) yᵉ ＝ᵉ neg-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
  left-negative-law-mul-Ringᵉ xᵉ yᵉ =
    ( apᵉ (mul-Ring'ᵉ Rᵉ yᵉ) (invᵉ (mul-neg-one-Ringᵉ Rᵉ xᵉ))) ∙ᵉ
    ( ( associative-mul-Ringᵉ Rᵉ (neg-one-Ringᵉ Rᵉ) xᵉ yᵉ) ∙ᵉ
      ( mul-neg-one-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)))

  right-negative-law-mul-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ xᵉ (neg-Ringᵉ Rᵉ yᵉ) ＝ᵉ neg-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
  right-negative-law-mul-Ringᵉ xᵉ yᵉ =
    ( apᵉ (mul-Ringᵉ Rᵉ xᵉ) (invᵉ (mul-neg-one-Ring'ᵉ Rᵉ yᵉ))) ∙ᵉ
    ( ( invᵉ (associative-mul-Ringᵉ Rᵉ xᵉ yᵉ (neg-one-Ringᵉ Rᵉ))) ∙ᵉ
      ( mul-neg-one-Ring'ᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)))

  mul-neg-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) (neg-Ringᵉ Rᵉ yᵉ) ＝ᵉ mul-Ringᵉ Rᵉ xᵉ yᵉ
  mul-neg-Ringᵉ xᵉ yᵉ =
    ( left-negative-law-mul-Ringᵉ xᵉ (neg-Ringᵉ Rᵉ yᵉ)) ∙ᵉ
    ( ( apᵉ (neg-Ringᵉ Rᵉ) (right-negative-law-mul-Ringᵉ xᵉ yᵉ)) ∙ᵉ
      ( neg-neg-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)))
```

### Distributivity of multiplication over subtraction

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  left-distributive-mul-left-subtraction-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ xᵉ (left-subtraction-Ringᵉ Rᵉ yᵉ zᵉ) ＝ᵉ
    left-subtraction-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ) (mul-Ringᵉ Rᵉ xᵉ zᵉ)
  left-distributive-mul-left-subtraction-Ringᵉ xᵉ yᵉ zᵉ =
    ( left-distributive-mul-add-Ringᵉ Rᵉ xᵉ (neg-Ringᵉ Rᵉ yᵉ) zᵉ) ∙ᵉ
    ( apᵉ (add-Ring'ᵉ Rᵉ _) (right-negative-law-mul-Ringᵉ Rᵉ _ _))

  right-distributive-mul-left-subtraction-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ (left-subtraction-Ringᵉ Rᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    left-subtraction-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ zᵉ) (mul-Ringᵉ Rᵉ yᵉ zᵉ)
  right-distributive-mul-left-subtraction-Ringᵉ xᵉ yᵉ zᵉ =
    ( right-distributive-mul-add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) yᵉ zᵉ) ∙ᵉ
    ( apᵉ (add-Ring'ᵉ Rᵉ _) (left-negative-law-mul-Ringᵉ Rᵉ _ _))

  left-distributive-mul-right-subtraction-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ xᵉ (right-subtraction-Ringᵉ Rᵉ yᵉ zᵉ) ＝ᵉ
    right-subtraction-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ) (mul-Ringᵉ Rᵉ xᵉ zᵉ)
  left-distributive-mul-right-subtraction-Ringᵉ xᵉ yᵉ zᵉ =
    ( left-distributive-mul-add-Ringᵉ Rᵉ xᵉ yᵉ (neg-Ringᵉ Rᵉ zᵉ)) ∙ᵉ
    ( apᵉ (add-Ringᵉ Rᵉ _) (right-negative-law-mul-Ringᵉ Rᵉ _ _))

  right-distributive-mul-right-subtraction-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ (right-subtraction-Ringᵉ Rᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    right-subtraction-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ zᵉ) (mul-Ringᵉ Rᵉ yᵉ zᵉ)
  right-distributive-mul-right-subtraction-Ringᵉ xᵉ yᵉ zᵉ =
    ( right-distributive-mul-add-Ringᵉ Rᵉ xᵉ (neg-Ringᵉ Rᵉ yᵉ) zᵉ) ∙ᵉ
    ( apᵉ (add-Ringᵉ Rᵉ _) (left-negative-law-mul-Ringᵉ Rᵉ _ _))
```

### Bidistributivity of multiplication over addition

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  bidistributive-mul-add-Ringᵉ :
    (uᵉ vᵉ xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ uᵉ vᵉ) (add-Ringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
    add-Ringᵉ Rᵉ
      ( add-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ uᵉ xᵉ) (mul-Ringᵉ Rᵉ uᵉ yᵉ))
      ( add-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ vᵉ xᵉ) (mul-Ringᵉ Rᵉ vᵉ yᵉ))
  bidistributive-mul-add-Ringᵉ =
    bidistributive-mul-add-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### Scalar multiplication of ring elements by a natural number

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  mul-nat-scalar-Ringᵉ : ℕᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
  mul-nat-scalar-Ringᵉ = mul-nat-scalar-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  ap-mul-nat-scalar-Ringᵉ :
    {mᵉ nᵉ : ℕᵉ} {xᵉ yᵉ : type-Ringᵉ Rᵉ} →
    (mᵉ ＝ᵉ nᵉ) → (xᵉ ＝ᵉ yᵉ) → mul-nat-scalar-Ringᵉ mᵉ xᵉ ＝ᵉ mul-nat-scalar-Ringᵉ nᵉ yᵉ
  ap-mul-nat-scalar-Ringᵉ = ap-mul-nat-scalar-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  left-zero-law-mul-nat-scalar-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → mul-nat-scalar-Ringᵉ 0 xᵉ ＝ᵉ zero-Ringᵉ Rᵉ
  left-zero-law-mul-nat-scalar-Ringᵉ =
    left-zero-law-mul-nat-scalar-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  right-zero-law-mul-nat-scalar-Ringᵉ :
    (nᵉ : ℕᵉ) → mul-nat-scalar-Ringᵉ nᵉ (zero-Ringᵉ Rᵉ) ＝ᵉ zero-Ringᵉ Rᵉ
  right-zero-law-mul-nat-scalar-Ringᵉ =
    right-zero-law-mul-nat-scalar-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  left-unit-law-mul-nat-scalar-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → mul-nat-scalar-Ringᵉ 1 xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-nat-scalar-Ringᵉ =
    left-unit-law-mul-nat-scalar-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  left-nat-scalar-law-mul-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ (mul-nat-scalar-Ringᵉ nᵉ xᵉ) yᵉ ＝ᵉ
    mul-nat-scalar-Ringᵉ nᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
  left-nat-scalar-law-mul-Ringᵉ =
    left-nat-scalar-law-mul-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  right-nat-scalar-law-mul-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ xᵉ (mul-nat-scalar-Ringᵉ nᵉ yᵉ) ＝ᵉ
    mul-nat-scalar-Ringᵉ nᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
  right-nat-scalar-law-mul-Ringᵉ =
    right-nat-scalar-law-mul-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  left-distributive-mul-nat-scalar-add-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    mul-nat-scalar-Ringᵉ nᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
    add-Ringᵉ Rᵉ (mul-nat-scalar-Ringᵉ nᵉ xᵉ) (mul-nat-scalar-Ringᵉ nᵉ yᵉ)
  left-distributive-mul-nat-scalar-add-Ringᵉ =
    left-distributive-mul-nat-scalar-add-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  right-distributive-mul-nat-scalar-add-Ringᵉ :
    (mᵉ nᵉ : ℕᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    mul-nat-scalar-Ringᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Ringᵉ Rᵉ (mul-nat-scalar-Ringᵉ mᵉ xᵉ) (mul-nat-scalar-Ringᵉ nᵉ xᵉ)
  right-distributive-mul-nat-scalar-add-Ringᵉ =
    right-distributive-mul-nat-scalar-add-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### Addition of a list of elements in an abelian group

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  add-list-Ringᵉ : listᵉ (type-Ringᵉ Rᵉ) → type-Ringᵉ Rᵉ
  add-list-Ringᵉ = add-list-Abᵉ (ab-Ringᵉ Rᵉ)

  preserves-concat-add-list-Ringᵉ :
    (l1ᵉ l2ᵉ : listᵉ (type-Ringᵉ Rᵉ)) →
    Idᵉ
      ( add-list-Ringᵉ (concat-listᵉ l1ᵉ l2ᵉ))
      ( add-Ringᵉ Rᵉ (add-list-Ringᵉ l1ᵉ) (add-list-Ringᵉ l2ᵉ))
  preserves-concat-add-list-Ringᵉ = preserves-concat-add-list-Abᵉ (ab-Ringᵉ Rᵉ)
```

### Equipping a type with the structure of a ring

```agda
structure-ringᵉ :
  {l1ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l1ᵉ
structure-ringᵉ Xᵉ =
  Σᵉ ( structure-abelian-groupᵉ Xᵉ)
    ( λ pᵉ → has-mul-Abᵉ (abelian-group-structure-abelian-groupᵉ Xᵉ pᵉ))

ring-structure-ringᵉ :
  {l1ᵉ : Level} → (Xᵉ : UUᵉ l1ᵉ) → structure-ringᵉ Xᵉ → Ringᵉ l1ᵉ
pr1ᵉ (ring-structure-ringᵉ Xᵉ (pᵉ ,ᵉ qᵉ)) = abelian-group-structure-abelian-groupᵉ Xᵉ pᵉ
pr2ᵉ (ring-structure-ringᵉ Xᵉ (pᵉ ,ᵉ qᵉ)) = qᵉ
```