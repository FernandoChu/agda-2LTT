# Abstract polytopes

```agda
module polytopes.abstract-polytopesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theoryᵉ

open import foundation.binary-relationsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.disjunctionᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import order-theory.finitely-graded-posetsᵉ
open import order-theory.posetsᵉ

open import univalent-combinatoricsᵉ
```

</details>

## Idea

Weᵉ defineᵉ abstract polytopesᵉ asᵉ finitelyᵉ gradedᵉ posetsᵉ satisfyingᵉ certainᵉ
axioms.ᵉ Inᵉ theᵉ classicalᵉ definition,ᵉ theᵉ gradingᵉ isᵉ aᵉ consequenceᵉ ofᵉ theᵉ axioms.ᵉ
Here,ᵉ weᵉ takeᵉ finitelyᵉ gradedᵉ posetsᵉ asᵉ ourᵉ startingᵉ pointᵉ

Theᵉ firstᵉ axiomᵉ ofᵉ polytopesᵉ assertsᵉ thatᵉ polytopesᵉ haveᵉ aᵉ leastᵉ andᵉ aᵉ largestᵉ
element.ᵉ Thisᵉ isᵉ alreadyᵉ definedᵉ asᵉ

`least-and-largest-element-finitely-graded-poset-Prop`.ᵉ

Next,ᵉ weᵉ assertᵉ theᵉ diamondᵉ conditionᵉ forᵉ abstract polytopes.ᵉ

## Definition

### The diamond condition

```agda
diamond-condition-finitely-graded-poset-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ) →
  Propᵉ (l1ᵉ ⊔ l2ᵉ)
diamond-condition-finitely-graded-poset-Propᵉ {kᵉ = zero-ℕᵉ} Xᵉ = raise-unit-Propᵉ _
diamond-condition-finitely-graded-poset-Propᵉ {kᵉ = succ-ℕᵉ kᵉ} Xᵉ =
  Π-Propᵉ
    ( Finᵉ kᵉ)
    ( λ iᵉ →
      Π-Propᵉ
        ( face-Finitely-Graded-Posetᵉ Xᵉ (inl-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ iᵉ)))
        ( λ xᵉ →
          Π-Propᵉ
            ( face-Finitely-Graded-Posetᵉ Xᵉ
              ( succ-Finᵉ
                ( succ-ℕᵉ (succ-ℕᵉ kᵉ))
                ( succ-Finᵉ
                  ( succ-ℕᵉ (succ-ℕᵉ kᵉ))
                  ( inl-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ iᵉ)))))
            ( λ yᵉ →
              has-cardinality-Propᵉ 2
                ( Σᵉ ( face-Finitely-Graded-Posetᵉ Xᵉ
                      ( succ-Finᵉ
                        ( succ-ℕᵉ (succ-ℕᵉ kᵉ))
                        ( inl-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ iᵉ))))
                    ( λ zᵉ →
                      adjacent-Finitely-Graded-Posetᵉ Xᵉ (inl-Finᵉ kᵉ iᵉ) xᵉ zᵉ ×ᵉ
                      adjacent-Finitely-Graded-Posetᵉ Xᵉ
                        ( succ-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ iᵉ))
                        ( zᵉ)
                        ( yᵉ))))))

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ)
  where

  diamond-condition-Finitely-Graded-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  diamond-condition-Finitely-Graded-Posetᵉ =
    type-Propᵉ (diamond-condition-finitely-graded-poset-Propᵉ Xᵉ)

  is-prop-diamond-condition-Finitely-Graded-Posetᵉ :
    is-propᵉ diamond-condition-Finitely-Graded-Posetᵉ
  is-prop-diamond-condition-Finitely-Graded-Posetᵉ =
    is-prop-type-Propᵉ (diamond-condition-finitely-graded-poset-Propᵉ Xᵉ)
```

### Prepolytopes

Weᵉ introduceᵉ theᵉ notionᵉ ofᵉ prepolytopesᵉ to beᵉ finitelyᵉ gradedᵉ posetsᵉ equippedᵉ
with aᵉ leastᵉ andᵉ aᵉ largestᵉ element,ᵉ andᵉ satisfyingᵉ theᵉ diamondᵉ condition.ᵉ Beforeᵉ
weᵉ stateᵉ theᵉ remainingᵉ conditionsᵉ ofᵉ polytopes,ᵉ weᵉ introduceᵉ someᵉ terminologyᵉ

```agda
Prepolytopeᵉ : (l1ᵉ l2ᵉ : Level) (kᵉ : ℕᵉ) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Prepolytopeᵉ l1ᵉ l2ᵉ kᵉ =
  Σᵉ ( Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ)
    ( λ Xᵉ →
      has-bottom-and-top-element-Finitely-Graded-Posetᵉ Xᵉ ×ᵉ
      diamond-condition-Finitely-Graded-Posetᵉ Xᵉ)
```

## Properties

### Basic structure of prepolytopes

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : Prepolytopeᵉ l1ᵉ l2ᵉ kᵉ)
  where

  finitely-graded-poset-Prepolytopeᵉ : Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ
  finitely-graded-poset-Prepolytopeᵉ = pr1ᵉ Xᵉ

  has-bottom-and-top-element-Prepolytopeᵉ :
    has-bottom-and-top-element-Finitely-Graded-Posetᵉ
      finitely-graded-poset-Prepolytopeᵉ
  has-bottom-and-top-element-Prepolytopeᵉ = pr1ᵉ (pr2ᵉ Xᵉ)

  has-bottom-element-Prepolytopeᵉ :
    has-bottom-element-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ
  has-bottom-element-Prepolytopeᵉ = pr1ᵉ has-bottom-and-top-element-Prepolytopeᵉ

  has-top-element-Prepolytopeᵉ :
    has-top-element-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ
  has-top-element-Prepolytopeᵉ = pr2ᵉ has-bottom-and-top-element-Prepolytopeᵉ

  diamond-condition-Prepolytopeᵉ :
    diamond-condition-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ
  diamond-condition-Prepolytopeᵉ = pr2ᵉ (pr2ᵉ Xᵉ)

  module _
    (iᵉ : Finᵉ (succ-ℕᵉ kᵉ))
    where

    face-prepolytope-Setᵉ : Setᵉ l1ᵉ
    face-prepolytope-Setᵉ =
      face-Finitely-Graded-Poset-Setᵉ finitely-graded-poset-Prepolytopeᵉ iᵉ

    face-Prepolytopeᵉ : UUᵉ l1ᵉ
    face-Prepolytopeᵉ =
      face-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ iᵉ

    is-set-face-Prepolytopeᵉ : is-setᵉ face-Prepolytopeᵉ
    is-set-face-Prepolytopeᵉ =
      is-set-face-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ iᵉ

  module _
    (iᵉ : Finᵉ kᵉ) (yᵉ : face-Prepolytopeᵉ (inl-Finᵉ kᵉ iᵉ))
    (zᵉ : face-Prepolytopeᵉ (succ-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ iᵉ)))
    where

    adjancent-prepolytope-Propᵉ : Propᵉ l2ᵉ
    adjancent-prepolytope-Propᵉ =
      adjacent-Finitely-Graded-Poset-Propᵉ
        ( finitely-graded-poset-Prepolytopeᵉ)
        ( iᵉ)
        ( yᵉ)
        ( zᵉ)

    adjacent-Prepolytopeᵉ : UUᵉ l2ᵉ
    adjacent-Prepolytopeᵉ =
      adjacent-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ iᵉ yᵉ zᵉ

    is-prop-adjacent-Prepolytopeᵉ : is-propᵉ adjacent-Prepolytopeᵉ
    is-prop-adjacent-Prepolytopeᵉ =
      is-prop-adjacent-Finitely-Graded-Posetᵉ
        ( finitely-graded-poset-Prepolytopeᵉ)
        ( iᵉ)
        ( yᵉ)
        ( zᵉ)

  set-Prepolytopeᵉ : Setᵉ l1ᵉ
  set-Prepolytopeᵉ =
    set-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  type-Prepolytopeᵉ : UUᵉ l1ᵉ
  type-Prepolytopeᵉ =
    type-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  is-set-type-Prepolytopeᵉ : is-setᵉ type-Prepolytopeᵉ
  is-set-type-Prepolytopeᵉ =
    is-set-type-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  element-face-Prepolytopeᵉ :
    {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Prepolytopeᵉ iᵉ → type-Prepolytopeᵉ
  element-face-Prepolytopeᵉ =
    element-face-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  shape-Prepolytopeᵉ :
    type-Prepolytopeᵉ → Finᵉ (succ-ℕᵉ kᵉ)
  shape-Prepolytopeᵉ =
    shape-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  face-element-Prepolytopeᵉ :
    (xᵉ : type-Prepolytopeᵉ) → face-Prepolytopeᵉ (shape-Prepolytopeᵉ xᵉ)
  face-element-Prepolytopeᵉ =
    face-type-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  path-faces-Prepolytopeᵉ :
    {iᵉ jᵉ : Finᵉ (succ-ℕᵉ kᵉ)} →
    face-Prepolytopeᵉ iᵉ → face-Prepolytopeᵉ jᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  path-faces-Prepolytopeᵉ xᵉ yᵉ =
    path-faces-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ xᵉ yᵉ

  refl-path-faces-Prepolytopeᵉ :
    {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} (xᵉ : face-Prepolytopeᵉ iᵉ) → path-faces-Prepolytopeᵉ xᵉ xᵉ
  refl-path-faces-Prepolytopeᵉ xᵉ = refl-path-faces-Finitely-Graded-Posetᵉ

  cons-path-faces-Prepolytopeᵉ :
    {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} {xᵉ : face-Prepolytopeᵉ iᵉ}
    {jᵉ : Finᵉ kᵉ} {yᵉ : face-Prepolytopeᵉ (inl-Finᵉ kᵉ jᵉ)}
    {zᵉ : face-Prepolytopeᵉ (succ-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ jᵉ))} →
    adjacent-Prepolytopeᵉ jᵉ yᵉ zᵉ → path-faces-Prepolytopeᵉ xᵉ yᵉ →
    path-faces-Prepolytopeᵉ xᵉ zᵉ
  cons-path-faces-Prepolytopeᵉ aᵉ pᵉ = cons-path-faces-Finitely-Graded-Posetᵉ aᵉ pᵉ

  tr-refl-path-faces-Preposetᵉ :
    {iᵉ jᵉ : Finᵉ (succ-ℕᵉ kᵉ)} (pᵉ : Idᵉ jᵉ iᵉ) (xᵉ : face-Prepolytopeᵉ jᵉ) →
    path-faces-Prepolytopeᵉ (trᵉ face-Prepolytopeᵉ pᵉ xᵉ) xᵉ
  tr-refl-path-faces-Preposetᵉ =
    tr-refl-path-faces-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  concat-path-faces-Prepolytopeᵉ :
    {i1ᵉ i2ᵉ i3ᵉ : Finᵉ (succ-ℕᵉ kᵉ)} {xᵉ : face-Prepolytopeᵉ i1ᵉ}
    {yᵉ : face-Prepolytopeᵉ i2ᵉ} {zᵉ : face-Prepolytopeᵉ i3ᵉ} →
    path-faces-Prepolytopeᵉ yᵉ zᵉ → path-faces-Prepolytopeᵉ xᵉ yᵉ →
    path-faces-Prepolytopeᵉ xᵉ zᵉ
  concat-path-faces-Prepolytopeᵉ =
    concat-path-faces-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  path-elements-Prepolytopeᵉ : (xᵉ yᵉ : type-Prepolytopeᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  path-elements-Prepolytopeᵉ =
    path-elements-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  refl-path-elements-Prepolytopeᵉ :
    (xᵉ : type-Prepolytopeᵉ) → path-elements-Prepolytopeᵉ xᵉ xᵉ
  refl-path-elements-Prepolytopeᵉ =
    refl-path-elements-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  concat-path-elements-Prepolytopeᵉ :
    (xᵉ yᵉ zᵉ : type-Prepolytopeᵉ) →
    path-elements-Prepolytopeᵉ yᵉ zᵉ → path-elements-Prepolytopeᵉ xᵉ yᵉ →
    path-elements-Prepolytopeᵉ xᵉ zᵉ
  concat-path-elements-Prepolytopeᵉ =
    concat-path-elements-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  leq-type-path-faces-Prepolytopeᵉ :
    {i1ᵉ i2ᵉ : Finᵉ (succ-ℕᵉ kᵉ)} (xᵉ : face-Prepolytopeᵉ i1ᵉ)
    (yᵉ : face-Prepolytopeᵉ i2ᵉ) →
    path-faces-Prepolytopeᵉ xᵉ yᵉ → leq-Finᵉ (succ-ℕᵉ kᵉ) i1ᵉ i2ᵉ
  leq-type-path-faces-Prepolytopeᵉ =
    leq-type-path-faces-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  eq-path-elements-Prepolytopeᵉ :
    (xᵉ yᵉ : type-Prepolytopeᵉ)
    (pᵉ : Idᵉ (shape-Prepolytopeᵉ xᵉ) (shape-Prepolytopeᵉ yᵉ)) →
    path-elements-Prepolytopeᵉ xᵉ yᵉ → Idᵉ xᵉ yᵉ
  eq-path-elements-Prepolytopeᵉ =
    eq-path-elements-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  eq-path-faces-Prepolytopeᵉ :
    {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} (xᵉ yᵉ : face-Prepolytopeᵉ iᵉ) →
    path-faces-Prepolytopeᵉ xᵉ yᵉ → Idᵉ xᵉ yᵉ
  eq-path-faces-Prepolytopeᵉ =
    eq-path-faces-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  antisymmetric-path-elements-Prepolytopeᵉ :
    (xᵉ yᵉ : type-Prepolytopeᵉ) → path-elements-Prepolytopeᵉ xᵉ yᵉ →
    path-elements-Prepolytopeᵉ yᵉ xᵉ → Idᵉ xᵉ yᵉ
  antisymmetric-path-elements-Prepolytopeᵉ =
    antisymmetric-path-elements-Finitely-Graded-Posetᵉ
      finitely-graded-poset-Prepolytopeᵉ

  module _
    (xᵉ yᵉ : type-Prepolytopeᵉ)
    where

    leq-prepolytope-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
    leq-prepolytope-Propᵉ =
      leq-Finitely-Graded-Poset-Propᵉ finitely-graded-poset-Prepolytopeᵉ xᵉ yᵉ

    leq-Prepolytopeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    leq-Prepolytopeᵉ =
      leq-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ xᵉ yᵉ

    is-prop-leq-Prepolytopeᵉ : is-propᵉ leq-Prepolytopeᵉ
    is-prop-leq-Prepolytopeᵉ =
      is-prop-leq-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ xᵉ yᵉ

  refl-leq-Prepolytopeᵉ : is-reflexiveᵉ leq-Prepolytopeᵉ
  refl-leq-Prepolytopeᵉ =
    refl-leq-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  transitive-leq-Prepolytopeᵉ : is-transitiveᵉ leq-Prepolytopeᵉ
  transitive-leq-Prepolytopeᵉ =
    transitive-leq-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  antisymmetric-leq-Prepolytopeᵉ : is-antisymmetricᵉ leq-Prepolytopeᵉ
  antisymmetric-leq-Prepolytopeᵉ =
    antisymmetric-leq-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  poset-Prepolytopeᵉ : Posetᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)
  poset-Prepolytopeᵉ =
    poset-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  chain-Prepolytopeᵉ : (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
  chain-Prepolytopeᵉ =
    chain-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  flag-Prepolytopeᵉ : (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
  flag-Prepolytopeᵉ =
    maximal-chain-Finitely-Graded-Posetᵉ finitely-graded-poset-Prepolytopeᵉ

  subtype-flag-Prepolytopeᵉ :
    {lᵉ : Level} (Fᵉ : flag-Prepolytopeᵉ lᵉ) →
    {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Prepolytopeᵉ iᵉ → Propᵉ lᵉ
  subtype-flag-Prepolytopeᵉ =
    subtype-maximal-chain-Finitely-Graded-Posetᵉ
      finitely-graded-poset-Prepolytopeᵉ

  type-subtype-flag-Prepolytopeᵉ :
    {lᵉ : Level} (Fᵉ : flag-Prepolytopeᵉ lᵉ) →
    {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Prepolytopeᵉ iᵉ → UUᵉ lᵉ
  type-subtype-flag-Prepolytopeᵉ Fᵉ xᵉ =
    type-Propᵉ (subtype-flag-Prepolytopeᵉ Fᵉ xᵉ)

  face-flag-Prepolytopeᵉ :
    {lᵉ : Level} (Fᵉ : flag-Prepolytopeᵉ lᵉ) → Finᵉ (succ-ℕᵉ kᵉ) → UUᵉ (l1ᵉ ⊔ lᵉ)
  face-flag-Prepolytopeᵉ Fᵉ iᵉ =
    Σᵉ (face-Prepolytopeᵉ iᵉ) (type-subtype-flag-Prepolytopeᵉ Fᵉ)

  face-bottom-element-Prepolytopeᵉ : face-Prepolytopeᵉ (zero-Finᵉ kᵉ)
  face-bottom-element-Prepolytopeᵉ = pr1ᵉ has-bottom-element-Prepolytopeᵉ

  element-bottom-element-Prepolytopeᵉ : type-Prepolytopeᵉ
  element-bottom-element-Prepolytopeᵉ =
    element-face-Prepolytopeᵉ face-bottom-element-Prepolytopeᵉ

  is-bottom-element-bottom-element-Prepolytopeᵉ :
    (xᵉ : type-Prepolytopeᵉ) →
    leq-Prepolytopeᵉ element-bottom-element-Prepolytopeᵉ xᵉ
  is-bottom-element-bottom-element-Prepolytopeᵉ =
    pr2ᵉ has-bottom-element-Prepolytopeᵉ

  face-has-top-element-Prepolytopeᵉ : face-Prepolytopeᵉ (neg-one-Finᵉ kᵉ)
  face-has-top-element-Prepolytopeᵉ = pr1ᵉ has-top-element-Prepolytopeᵉ

  element-has-top-element-Prepolytopeᵉ : type-Prepolytopeᵉ
  element-has-top-element-Prepolytopeᵉ =
    element-face-Prepolytopeᵉ face-has-top-element-Prepolytopeᵉ

  is-has-top-element-has-top-element-Prepolytopeᵉ :
    (xᵉ : type-Prepolytopeᵉ) →
    leq-Prepolytopeᵉ xᵉ element-has-top-element-Prepolytopeᵉ
  is-has-top-element-has-top-element-Prepolytopeᵉ =
    pr2ᵉ has-top-element-Prepolytopeᵉ

  is-contr-face-bottom-dimension-Prepolytopeᵉ :
    is-contrᵉ (face-Prepolytopeᵉ (zero-Finᵉ kᵉ))
  pr1ᵉ is-contr-face-bottom-dimension-Prepolytopeᵉ =
    face-bottom-element-Prepolytopeᵉ
  pr2ᵉ is-contr-face-bottom-dimension-Prepolytopeᵉ xᵉ =
    apply-universal-property-trunc-Propᵉ
      ( is-bottom-element-bottom-element-Prepolytopeᵉ
        ( element-face-Prepolytopeᵉ xᵉ))
      ( Id-Propᵉ
        ( face-prepolytope-Setᵉ (zero-Finᵉ kᵉ))
        ( face-bottom-element-Prepolytopeᵉ)
        ( xᵉ))
      ( λ pᵉ → eq-path-faces-Prepolytopeᵉ face-bottom-element-Prepolytopeᵉ xᵉ pᵉ)

  is-contr-face-top-dimension-Prepolytopeᵉ :
    is-contrᵉ (face-Prepolytopeᵉ (neg-one-Finᵉ kᵉ))
  pr1ᵉ is-contr-face-top-dimension-Prepolytopeᵉ =
    face-has-top-element-Prepolytopeᵉ
  pr2ᵉ is-contr-face-top-dimension-Prepolytopeᵉ xᵉ =
    apply-universal-property-trunc-Propᵉ
      ( is-has-top-element-has-top-element-Prepolytopeᵉ
        ( element-face-Prepolytopeᵉ xᵉ))
      ( Id-Propᵉ
        ( face-prepolytope-Setᵉ (neg-one-Finᵉ kᵉ))
        ( face-has-top-element-Prepolytopeᵉ)
        ( xᵉ))
      ( λ pᵉ →
        invᵉ (eq-path-faces-Prepolytopeᵉ xᵉ face-has-top-element-Prepolytopeᵉ pᵉ))
```

### Flags are equivalently described as paths from the least to the largest element

```agda
  is-on-path-face-prepolytope-Propᵉ :
    {i1ᵉ i2ᵉ : Finᵉ (succ-ℕᵉ kᵉ)} {xᵉ : face-Prepolytopeᵉ i1ᵉ} {yᵉ : face-Prepolytopeᵉ i2ᵉ}
    (pᵉ : path-faces-Prepolytopeᵉ xᵉ yᵉ) →
    {i3ᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Prepolytopeᵉ i3ᵉ → Propᵉ l1ᵉ
  is-on-path-face-prepolytope-Propᵉ
    {xᵉ = xᵉ} refl-path-faces-Finitely-Graded-Posetᵉ zᵉ =
    Id-Propᵉ
      ( set-Prepolytopeᵉ)
      ( element-face-Prepolytopeᵉ xᵉ)
      ( element-face-Prepolytopeᵉ zᵉ)
  is-on-path-face-prepolytope-Propᵉ
    ( cons-path-faces-Finitely-Graded-Posetᵉ {zᵉ = wᵉ} aᵉ pᵉ) zᵉ =
    disjunction-Propᵉ
      ( is-on-path-face-prepolytope-Propᵉ pᵉ zᵉ)
      ( Id-Propᵉ
        ( set-Prepolytopeᵉ)
        ( element-face-Prepolytopeᵉ wᵉ)
        ( element-face-Prepolytopeᵉ zᵉ))

  module _
    {i1ᵉ i2ᵉ i3ᵉ : Finᵉ (succ-ℕᵉ kᵉ)}
    {xᵉ : face-Prepolytopeᵉ i1ᵉ} {yᵉ : face-Prepolytopeᵉ i2ᵉ}
    where

    is-on-path-face-Prepolytopeᵉ :
      path-faces-Prepolytopeᵉ xᵉ yᵉ → face-Prepolytopeᵉ i3ᵉ → UUᵉ l1ᵉ
    is-on-path-face-Prepolytopeᵉ pᵉ zᵉ =
      type-Propᵉ (is-on-path-face-prepolytope-Propᵉ pᵉ zᵉ)

    is-prop-is-on-path-face-Prepolytopeᵉ :
      (pᵉ : path-faces-Prepolytopeᵉ xᵉ yᵉ) (zᵉ : face-Prepolytopeᵉ i3ᵉ) →
      is-propᵉ (is-on-path-face-Prepolytopeᵉ pᵉ zᵉ)
    is-prop-is-on-path-face-Prepolytopeᵉ pᵉ zᵉ =
      is-prop-type-Propᵉ (is-on-path-face-prepolytope-Propᵉ pᵉ zᵉ)
```

### Proof condition P2 of polytopes

Theᵉ secondᵉ axiomᵉ ofᵉ polytopesᵉ assertsᵉ thatᵉ everyᵉ maximalᵉ chainᵉ hasᵉ kᵉ elements.ᵉ
Noteᵉ thatᵉ everyᵉ maximalᵉ chainᵉ isᵉ aᵉ pathᵉ fromᵉ theᵉ bottomᵉ elementᵉ to theᵉ topᵉ
element,ᵉ whichᵉ necessarilyᵉ passesᵉ throughᵉ allᵉ dimensions.ᵉ Therefore,ᵉ theᵉ secondᵉ
axiomᵉ followsᵉ fromᵉ ourᵉ setup.ᵉ Noteᵉ thatᵉ weᵉ didn'tᵉ startᵉ with generalᵉ posets,ᵉ butᵉ
with finitelyᵉ gradedᵉ posets.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (lᵉ : Level) {kᵉ : ℕᵉ} (Xᵉ : Prepolytopeᵉ l1ᵉ l2ᵉ kᵉ)
  where

  condition-P2-prepolytope-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
  condition-P2-prepolytope-Propᵉ =
    Π-Propᵉ
      ( flag-Prepolytopeᵉ Xᵉ lᵉ)
      ( λ Fᵉ →
        Π-Propᵉ
          ( Finᵉ (succ-ℕᵉ kᵉ))
          ( λ iᵉ →
            is-contr-Propᵉ
              ( Σᵉ ( face-Prepolytopeᵉ Xᵉ iᵉ)
                  ( λ xᵉ → type-Propᵉ (subtype-flag-Prepolytopeᵉ Xᵉ Fᵉ xᵉ)))))

  condition-P2-Prepolytopeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
  condition-P2-Prepolytopeᵉ = type-Propᵉ condition-P2-prepolytope-Propᵉ

  is-prop-condition-P2-Prepolytopeᵉ : is-propᵉ condition-P2-Prepolytopeᵉ
  is-prop-condition-P2-Prepolytopeᵉ =
    is-prop-type-Propᵉ condition-P2-prepolytope-Propᵉ
```

### Strong connectedness of polytopes

Theᵉ strongᵉ connectednessᵉ conditionᵉ forᵉ polytopesᵉ assertsᵉ thatᵉ theᵉ unorderedᵉ
graphᵉ ofᵉ flagsᵉ ofᵉ aᵉ polytopeᵉ isᵉ connected.ᵉ Theᵉ edgesᵉ in thisᵉ graphᵉ areᵉ puncturedᵉ
flags,ᵉ i.e.,ᵉ chainsᵉ thatᵉ haveᵉ exactlyᵉ oneᵉ elementᵉ in eachᵉ dimensionᵉ exceptᵉ in
oneᵉ dimensionᵉ thatᵉ isᵉ neitherᵉ theᵉ topᵉ norᵉ theᵉ bottomᵉ dimension.ᵉ Aᵉ puncturedᵉ flagᵉ
connectsᵉ theᵉ twoᵉ flagsᵉ itᵉ isᵉ aᵉ subchainᵉ of.ᵉ

### The definition of polytopes

```agda
Polytopeᵉ :
  (l1ᵉ l2ᵉ l3ᵉ : Level) (kᵉ : ℕᵉ) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
Polytopeᵉ l1ᵉ l2ᵉ l3ᵉ kᵉ =
  Σᵉ ( Prepolytopeᵉ l1ᵉ l2ᵉ kᵉ)
    ( λ Xᵉ →
      ( condition-P2-Prepolytopeᵉ l3ᵉ Xᵉ) ×ᵉ
      unitᵉ)
```