# Subsemigroups

```agda
module group-theory.subsemigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.powersetsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.subsets-semigroupsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ subsemigroupᵉ ofᵉ aᵉ semigroupᵉ `G`ᵉ isᵉ aᵉ subtypeᵉ ofᵉ `G`ᵉ closedᵉ underᵉ
multiplication.ᵉ

## Definitions

### Subsemigroups

```agda
is-closed-under-multiplication-prop-subset-Semigroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Pᵉ : subset-Semigroupᵉ l2ᵉ Gᵉ) →
  Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-closed-under-multiplication-prop-subset-Semigroupᵉ Gᵉ Pᵉ =
  implicit-Π-Propᵉ
    ( type-Semigroupᵉ Gᵉ)
    ( λ xᵉ →
      implicit-Π-Propᵉ
        ( type-Semigroupᵉ Gᵉ)
        ( λ yᵉ → hom-Propᵉ (Pᵉ xᵉ) (hom-Propᵉ (Pᵉ yᵉ) (Pᵉ (mul-Semigroupᵉ Gᵉ xᵉ yᵉ)))))

is-closed-under-multiplication-subset-Semigroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Pᵉ : subset-Semigroupᵉ l2ᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-closed-under-multiplication-subset-Semigroupᵉ Gᵉ Pᵉ =
  type-Propᵉ (is-closed-under-multiplication-prop-subset-Semigroupᵉ Gᵉ Pᵉ)

Subsemigroupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Semigroupᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Subsemigroupᵉ l2ᵉ Gᵉ =
  type-subtypeᵉ
    ( is-closed-under-multiplication-prop-subset-Semigroupᵉ {l2ᵉ = l2ᵉ} Gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Pᵉ : Subsemigroupᵉ l2ᵉ Gᵉ)
  where

  subset-Subsemigroupᵉ : subtypeᵉ l2ᵉ (type-Semigroupᵉ Gᵉ)
  subset-Subsemigroupᵉ =
    inclusion-subtypeᵉ (is-closed-under-multiplication-prop-subset-Semigroupᵉ Gᵉ) Pᵉ

  is-closed-under-multiplication-Subsemigroupᵉ :
    is-closed-under-multiplication-subset-Semigroupᵉ Gᵉ subset-Subsemigroupᵉ
  is-closed-under-multiplication-Subsemigroupᵉ = pr2ᵉ Pᵉ

  is-in-Subsemigroupᵉ : type-Semigroupᵉ Gᵉ → UUᵉ l2ᵉ
  is-in-Subsemigroupᵉ = is-in-subtypeᵉ subset-Subsemigroupᵉ

  is-closed-under-eq-Subsemigroupᵉ :
    {xᵉ yᵉ : type-Semigroupᵉ Gᵉ} →
    is-in-Subsemigroupᵉ xᵉ → xᵉ ＝ᵉ yᵉ → is-in-Subsemigroupᵉ yᵉ
  is-closed-under-eq-Subsemigroupᵉ =
    is-closed-under-eq-subset-Semigroupᵉ Gᵉ subset-Subsemigroupᵉ

  is-closed-under-eq-Subsemigroup'ᵉ :
    {xᵉ yᵉ : type-Semigroupᵉ Gᵉ} →
    is-in-Subsemigroupᵉ yᵉ → xᵉ ＝ᵉ yᵉ → is-in-Subsemigroupᵉ xᵉ
  is-closed-under-eq-Subsemigroup'ᵉ =
    is-closed-under-eq-subset-Semigroup'ᵉ Gᵉ subset-Subsemigroupᵉ

  is-prop-is-in-Subsemigroupᵉ :
    (xᵉ : type-Semigroupᵉ Gᵉ) → is-propᵉ (is-in-Subsemigroupᵉ xᵉ)
  is-prop-is-in-Subsemigroupᵉ =
    is-prop-is-in-subtypeᵉ subset-Subsemigroupᵉ

  type-Subsemigroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Subsemigroupᵉ = type-subtypeᵉ subset-Subsemigroupᵉ

  is-set-type-Subsemigroupᵉ : is-setᵉ type-Subsemigroupᵉ
  is-set-type-Subsemigroupᵉ =
    is-set-type-subset-Semigroupᵉ Gᵉ subset-Subsemigroupᵉ

  set-Subsemigroupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Subsemigroupᵉ =
    set-subset-Semigroupᵉ Gᵉ subset-Subsemigroupᵉ

  inclusion-Subsemigroupᵉ :
    type-Subsemigroupᵉ → type-Semigroupᵉ Gᵉ
  inclusion-Subsemigroupᵉ =
    inclusion-subtypeᵉ subset-Subsemigroupᵉ

  ap-inclusion-Subsemigroupᵉ :
    (xᵉ yᵉ : type-Subsemigroupᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-Subsemigroupᵉ xᵉ ＝ᵉ inclusion-Subsemigroupᵉ yᵉ
  ap-inclusion-Subsemigroupᵉ =
    ap-inclusion-subtypeᵉ subset-Subsemigroupᵉ

  is-in-subsemigroup-inclusion-Subsemigroupᵉ :
    (xᵉ : type-Subsemigroupᵉ) →
    is-in-Subsemigroupᵉ (inclusion-Subsemigroupᵉ xᵉ)
  is-in-subsemigroup-inclusion-Subsemigroupᵉ =
    is-in-subtype-inclusion-subtypeᵉ subset-Subsemigroupᵉ

  mul-Subsemigroupᵉ :
    (xᵉ yᵉ : type-Subsemigroupᵉ) → type-Subsemigroupᵉ
  pr1ᵉ (mul-Subsemigroupᵉ xᵉ yᵉ) =
    mul-Semigroupᵉ Gᵉ
      ( inclusion-Subsemigroupᵉ xᵉ)
      ( inclusion-Subsemigroupᵉ yᵉ)
  pr2ᵉ (mul-Subsemigroupᵉ xᵉ yᵉ) =
    is-closed-under-multiplication-Subsemigroupᵉ (pr2ᵉ xᵉ) (pr2ᵉ yᵉ)

  associative-mul-Subsemigroupᵉ :
    (xᵉ yᵉ zᵉ : type-Subsemigroupᵉ) →
    ( mul-Subsemigroupᵉ (mul-Subsemigroupᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    ( mul-Subsemigroupᵉ xᵉ (mul-Subsemigroupᵉ yᵉ zᵉ))
  associative-mul-Subsemigroupᵉ xᵉ yᵉ zᵉ =
    eq-type-subtypeᵉ
      ( subset-Subsemigroupᵉ)
      ( associative-mul-Semigroupᵉ Gᵉ
        ( inclusion-Subsemigroupᵉ xᵉ)
        ( inclusion-Subsemigroupᵉ yᵉ)
        ( inclusion-Subsemigroupᵉ zᵉ))

  semigroup-Subsemigroupᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ semigroup-Subsemigroupᵉ = set-Subsemigroupᵉ
  pr1ᵉ (pr2ᵉ semigroup-Subsemigroupᵉ) = mul-Subsemigroupᵉ
  pr2ᵉ (pr2ᵉ semigroup-Subsemigroupᵉ) = associative-mul-Subsemigroupᵉ

  preserves-mul-inclusion-Subsemigroupᵉ :
    preserves-mul-Semigroupᵉ semigroup-Subsemigroupᵉ Gᵉ inclusion-Subsemigroupᵉ
  preserves-mul-inclusion-Subsemigroupᵉ = reflᵉ

  hom-inclusion-Subsemigroupᵉ :
    hom-Semigroupᵉ semigroup-Subsemigroupᵉ Gᵉ
  pr1ᵉ hom-inclusion-Subsemigroupᵉ = inclusion-Subsemigroupᵉ
  pr2ᵉ hom-inclusion-Subsemigroupᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-Subsemigroupᵉ {xᵉ} {yᵉ}
```

## Properties

### Extensionality of the type of all subsemigroups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Subsemigroupᵉ l2ᵉ Gᵉ)
  where

  has-same-elements-prop-Subsemigroupᵉ :
    {l3ᵉ : Level} → Subsemigroupᵉ l3ᵉ Gᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-prop-Subsemigroupᵉ Kᵉ =
    has-same-elements-subtype-Propᵉ
      ( subset-Subsemigroupᵉ Gᵉ Hᵉ)
      ( subset-Subsemigroupᵉ Gᵉ Kᵉ)

  has-same-elements-Subsemigroupᵉ :
    {l3ᵉ : Level} → Subsemigroupᵉ l3ᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-Subsemigroupᵉ Kᵉ =
    has-same-elements-subtypeᵉ
      ( subset-Subsemigroupᵉ Gᵉ Hᵉ)
      ( subset-Subsemigroupᵉ Gᵉ Kᵉ)

  extensionality-Subsemigroupᵉ :
    (Kᵉ : Subsemigroupᵉ l2ᵉ Gᵉ) → (Hᵉ ＝ᵉ Kᵉ) ≃ᵉ has-same-elements-Subsemigroupᵉ Kᵉ
  extensionality-Subsemigroupᵉ =
    extensionality-type-subtypeᵉ
      ( is-closed-under-multiplication-prop-subset-Semigroupᵉ Gᵉ)
      ( is-closed-under-multiplication-Subsemigroupᵉ Gᵉ Hᵉ)
      ( λ xᵉ → idᵉ ,ᵉ idᵉ)
      ( extensionality-subtypeᵉ (subset-Subsemigroupᵉ Gᵉ Hᵉ))

  refl-has-same-elements-Subsemigroupᵉ : has-same-elements-Subsemigroupᵉ Hᵉ
  refl-has-same-elements-Subsemigroupᵉ =
    refl-has-same-elements-subtypeᵉ (subset-Subsemigroupᵉ Gᵉ Hᵉ)

  has-same-elements-eq-Subsemigroupᵉ :
    (Kᵉ : Subsemigroupᵉ l2ᵉ Gᵉ) → (Hᵉ ＝ᵉ Kᵉ) → has-same-elements-Subsemigroupᵉ Kᵉ
  has-same-elements-eq-Subsemigroupᵉ Kᵉ =
    map-equivᵉ (extensionality-Subsemigroupᵉ Kᵉ)

  eq-has-same-elements-Subsemigroupᵉ :
    (Kᵉ : Subsemigroupᵉ l2ᵉ Gᵉ) → has-same-elements-Subsemigroupᵉ Kᵉ → (Hᵉ ＝ᵉ Kᵉ)
  eq-has-same-elements-Subsemigroupᵉ Kᵉ =
    map-inv-equivᵉ (extensionality-Subsemigroupᵉ Kᵉ)
```

### The containment relation of subsemigroups

```agda
leq-prop-Subsemigroupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) →
  Subsemigroupᵉ l2ᵉ Gᵉ → Subsemigroupᵉ l3ᵉ Gᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
leq-prop-Subsemigroupᵉ Gᵉ Hᵉ Kᵉ =
  leq-prop-subtypeᵉ
    ( subset-Subsemigroupᵉ Gᵉ Hᵉ)
    ( subset-Subsemigroupᵉ Gᵉ Kᵉ)

leq-Subsemigroupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) →
  Subsemigroupᵉ l2ᵉ Gᵉ → Subsemigroupᵉ l3ᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
leq-Subsemigroupᵉ Gᵉ Hᵉ Kᵉ = subset-Subsemigroupᵉ Gᵉ Hᵉ ⊆ᵉ subset-Subsemigroupᵉ Gᵉ Kᵉ

is-prop-leq-Subsemigroupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) →
  (Hᵉ : Subsemigroupᵉ l2ᵉ Gᵉ) (Kᵉ : Subsemigroupᵉ l3ᵉ Gᵉ) →
  is-propᵉ (leq-Subsemigroupᵉ Gᵉ Hᵉ Kᵉ)
is-prop-leq-Subsemigroupᵉ Gᵉ Hᵉ Kᵉ =
  is-prop-leq-subtypeᵉ (subset-Subsemigroupᵉ Gᵉ Hᵉ) (subset-Subsemigroupᵉ Gᵉ Kᵉ)

refl-leq-Subsemigroupᵉ :
  {l1ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) →
  is-reflexive-Large-Relationᵉ (λ lᵉ → Subsemigroupᵉ lᵉ Gᵉ) (leq-Subsemigroupᵉ Gᵉ)
refl-leq-Subsemigroupᵉ Gᵉ Hᵉ = refl-leq-subtypeᵉ (subset-Subsemigroupᵉ Gᵉ Hᵉ)

transitive-leq-Subsemigroupᵉ :
  {l1ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) →
  is-transitive-Large-Relationᵉ (λ lᵉ → Subsemigroupᵉ lᵉ Gᵉ) (leq-Subsemigroupᵉ Gᵉ)
transitive-leq-Subsemigroupᵉ Gᵉ Hᵉ Kᵉ Lᵉ =
  transitive-leq-subtypeᵉ
    ( subset-Subsemigroupᵉ Gᵉ Hᵉ)
    ( subset-Subsemigroupᵉ Gᵉ Kᵉ)
    ( subset-Subsemigroupᵉ Gᵉ Lᵉ)

antisymmetric-leq-Subsemigroupᵉ :
  {l1ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) →
  is-antisymmetric-Large-Relationᵉ (λ lᵉ → Subsemigroupᵉ lᵉ Gᵉ) (leq-Subsemigroupᵉ Gᵉ)
antisymmetric-leq-Subsemigroupᵉ Gᵉ Hᵉ Kᵉ αᵉ βᵉ =
  eq-has-same-elements-Subsemigroupᵉ Gᵉ Hᵉ Kᵉ (λ xᵉ → (αᵉ xᵉ ,ᵉ βᵉ xᵉ))

Subsemigroup-Large-Preorderᵉ :
  {l1ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) →
  Large-Preorderᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
type-Large-Preorderᵉ (Subsemigroup-Large-Preorderᵉ Gᵉ) l2ᵉ = Subsemigroupᵉ l2ᵉ Gᵉ
leq-prop-Large-Preorderᵉ (Subsemigroup-Large-Preorderᵉ Gᵉ) Hᵉ Kᵉ =
  leq-prop-Subsemigroupᵉ Gᵉ Hᵉ Kᵉ
refl-leq-Large-Preorderᵉ (Subsemigroup-Large-Preorderᵉ Gᵉ) =
  refl-leq-Subsemigroupᵉ Gᵉ
transitive-leq-Large-Preorderᵉ (Subsemigroup-Large-Preorderᵉ Gᵉ) =
  transitive-leq-Subsemigroupᵉ Gᵉ

Subsemigroup-Preorderᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Semigroupᵉ l1ᵉ) →
  Preorderᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
Subsemigroup-Preorderᵉ l2ᵉ Gᵉ =
  preorder-Large-Preorderᵉ (Subsemigroup-Large-Preorderᵉ Gᵉ) l2ᵉ

Subsemigroup-Large-Posetᵉ :
  {l1ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) →
  Large-Posetᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
large-preorder-Large-Posetᵉ (Subsemigroup-Large-Posetᵉ Gᵉ) =
  Subsemigroup-Large-Preorderᵉ Gᵉ
antisymmetric-leq-Large-Posetᵉ (Subsemigroup-Large-Posetᵉ Gᵉ) =
  antisymmetric-leq-Subsemigroupᵉ Gᵉ

Subsemigroup-Posetᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Semigroupᵉ l1ᵉ) →
  Posetᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
Subsemigroup-Posetᵉ l2ᵉ Gᵉ = poset-Large-Posetᵉ (Subsemigroup-Large-Posetᵉ Gᵉ) l2ᵉ

preserves-order-subset-Subsemigroupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Subsemigroupᵉ l2ᵉ Gᵉ) (Kᵉ : Subsemigroupᵉ l3ᵉ Gᵉ) →
  leq-Subsemigroupᵉ Gᵉ Hᵉ Kᵉ → (subset-Subsemigroupᵉ Gᵉ Hᵉ ⊆ᵉ subset-Subsemigroupᵉ Gᵉ Kᵉ)
preserves-order-subset-Subsemigroupᵉ Gᵉ Hᵉ Kᵉ = idᵉ

subset-subsemigroup-hom-large-poset-Semigroupᵉ :
  {l1ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) →
  hom-Large-Posetᵉ
    ( λ lᵉ → lᵉ)
    ( Subsemigroup-Large-Posetᵉ Gᵉ)
    ( powerset-Large-Posetᵉ (type-Semigroupᵉ Gᵉ))
map-hom-Large-Preorderᵉ
  ( subset-subsemigroup-hom-large-poset-Semigroupᵉ Gᵉ) =
  subset-Subsemigroupᵉ Gᵉ
preserves-order-hom-Large-Preorderᵉ
  ( subset-subsemigroup-hom-large-poset-Semigroupᵉ Gᵉ) =
  preserves-order-subset-Subsemigroupᵉ Gᵉ
```