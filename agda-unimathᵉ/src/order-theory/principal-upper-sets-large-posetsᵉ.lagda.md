# Principal upper sets of large posets

```agda
module order-theory.principal-upper-sets-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-subposetsᵉ
open import order-theory.large-subpreordersᵉ
open import order-theory.similarity-of-elements-large-posetsᵉ
```

</details>

## Idea

Theᵉ **principalᵉ upperᵉ set**ᵉ `↑{x}`ᵉ ofᵉ anᵉ elementᵉ `x`ᵉ ofᵉ aᵉ
[largeᵉ poset](order-theory.large-posets.mdᵉ) `P`ᵉ isᵉ theᵉ
[largeᵉ subposet](order-theory.large-subposets.mdᵉ) consistingᵉ ofᵉ allᵉ elementsᵉ
`xᵉ ≤ᵉ y`ᵉ in `P`.ᵉ

Twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ in aᵉ largeᵉ posetᵉ `P`ᵉ areᵉ
[similar](order-theory.similarity-of-elements-large-posets.mdᵉ) ifᵉ andᵉ onlyᵉ ifᵉ
theyᵉ haveᵉ theᵉ sameᵉ principalᵉ upperᵉ sets,ᵉ andᵉ ifᵉ `x`ᵉ andᵉ `y`ᵉ areᵉ ofᵉ theᵉ sameᵉ
[universeᵉ level](foundation.universe-levels.md),ᵉ thenᵉ `x`ᵉ andᵉ `y`ᵉ areᵉ equalᵉ ifᵉ
andᵉ onlyᵉ ifᵉ theyᵉ haveᵉ theᵉ sameᵉ principalᵉ upperᵉ sets.ᵉ Toᵉ seeᵉ this,ᵉ noteᵉ thatᵉ ifᵉ
`↑{xᵉ} = ↑{y}`,ᵉ thenᵉ weᵉ haveᵉ theᵉ implicationsᵉ `(xᵉ ≤ᵉ xᵉ) → (xᵉ ≤ᵉ y)`ᵉ andᵉ
`(yᵉ ≤ᵉ yᵉ) → (yᵉ ≤ᵉ x)`.ᵉ

## Definitions

### The predicate of being a principal upper set of an element

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ)
  {γᵉ : Level → Level} (Sᵉ : Large-Subposetᵉ γᵉ Pᵉ)
  where

  is-principal-upper-set-Large-Subposetᵉ : UUωᵉ
  is-principal-upper-set-Large-Subposetᵉ =
    {lᵉ : Level} (yᵉ : type-Large-Posetᵉ Pᵉ lᵉ) →
    leq-Large-Posetᵉ Pᵉ yᵉ xᵉ ↔ᵉ is-in-Large-Subposetᵉ Pᵉ Sᵉ yᵉ
```

### The principal upper set of an element

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ)
  where

  large-subpreorder-principal-upper-set-element-Large-Posetᵉ :
    Large-Subpreorderᵉ (λ lᵉ → βᵉ l1ᵉ lᵉ) (large-preorder-Large-Posetᵉ Pᵉ)
  large-subpreorder-principal-upper-set-element-Large-Posetᵉ yᵉ =
    leq-prop-Large-Posetᵉ Pᵉ xᵉ yᵉ

  is-closed-under-sim-principal-upper-set-element-Large-Posetᵉ :
    is-closed-under-sim-Large-Subpreorderᵉ Pᵉ
      ( large-subpreorder-principal-upper-set-element-Large-Posetᵉ)
  is-closed-under-sim-principal-upper-set-element-Large-Posetᵉ yᵉ zᵉ pᵉ qᵉ lᵉ =
    transitive-leq-Large-Posetᵉ Pᵉ xᵉ yᵉ zᵉ pᵉ lᵉ

  principal-upper-set-element-Large-Posetᵉ : Large-Subposetᵉ (λ lᵉ → βᵉ l1ᵉ lᵉ) Pᵉ
  large-subpreorder-Large-Subposetᵉ principal-upper-set-element-Large-Posetᵉ =
    large-subpreorder-principal-upper-set-element-Large-Posetᵉ
  is-closed-under-sim-Large-Subposetᵉ principal-upper-set-element-Large-Posetᵉ =
    is-closed-under-sim-principal-upper-set-element-Large-Posetᵉ
```

## Properties

### The principal upper sets `↑{x}` and `↑{y}` have the same elements if and only if `x` and `y` are similar

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level} {xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ} {yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ}
  where

  sim-has-same-elements-principal-upper-set-element-Large-Posetᵉ :
    has-same-elements-Large-Subposetᵉ Pᵉ
      ( principal-upper-set-element-Large-Posetᵉ Pᵉ xᵉ)
      ( principal-upper-set-element-Large-Posetᵉ Pᵉ yᵉ) →
    sim-Large-Posetᵉ Pᵉ xᵉ yᵉ
  pr1ᵉ (sim-has-same-elements-principal-upper-set-element-Large-Posetᵉ Hᵉ) =
    backward-implicationᵉ (Hᵉ yᵉ) (refl-leq-Large-Posetᵉ Pᵉ yᵉ)
  pr2ᵉ (sim-has-same-elements-principal-upper-set-element-Large-Posetᵉ Hᵉ) =
    forward-implicationᵉ (Hᵉ xᵉ) (refl-leq-Large-Posetᵉ Pᵉ xᵉ)

  has-same-elements-principal-upper-set-element-sim-Large-Posetᵉ :
    sim-Large-Posetᵉ Pᵉ xᵉ yᵉ →
    has-same-elements-Large-Subposetᵉ Pᵉ
      ( principal-upper-set-element-Large-Posetᵉ Pᵉ xᵉ)
      ( principal-upper-set-element-Large-Posetᵉ Pᵉ yᵉ)
  pr1ᵉ
    ( has-same-elements-principal-upper-set-element-sim-Large-Posetᵉ (Hᵉ ,ᵉ Kᵉ) zᵉ)
    ( pᵉ) =
    transitive-leq-Large-Posetᵉ Pᵉ yᵉ xᵉ zᵉ pᵉ Kᵉ
  pr2ᵉ
    ( has-same-elements-principal-upper-set-element-sim-Large-Posetᵉ (Hᵉ ,ᵉ Kᵉ) zᵉ)
    ( qᵉ) =
    transitive-leq-Large-Posetᵉ Pᵉ xᵉ yᵉ zᵉ qᵉ Hᵉ
```

### For two elements `x` and `y` of a large poset of the same universe level, if the principal upper sets `↑{x}` and `↑{y}` have the same elements, then `x` and `y` are equal

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ : Level} (xᵉ yᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ)
  where

  eq-has-same-elements-principal-upper-set-element-Large-Posetᵉ :
    has-same-elements-Large-Subposetᵉ Pᵉ
      ( principal-upper-set-element-Large-Posetᵉ Pᵉ xᵉ)
      ( principal-upper-set-element-Large-Posetᵉ Pᵉ yᵉ) →
    xᵉ ＝ᵉ yᵉ
  eq-has-same-elements-principal-upper-set-element-Large-Posetᵉ Hᵉ =
    antisymmetric-leq-Large-Posetᵉ Pᵉ xᵉ yᵉ
      ( pr1ᵉ (sim-has-same-elements-principal-upper-set-element-Large-Posetᵉ Pᵉ Hᵉ))
      ( pr2ᵉ (sim-has-same-elements-principal-upper-set-element-Large-Posetᵉ Pᵉ Hᵉ))
```