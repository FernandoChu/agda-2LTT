# Similarity of elements in large posets

```agda
module order-theory.similarity-of-elements-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.similarity-of-elements-large-preordersᵉ
```

</details>

## Idea

Twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ ofᵉ aᵉ [largeᵉ poset](order-theory.large-posets.mdᵉ) `P`ᵉ
areᵉ saidᵉ to beᵉ **similar**ᵉ ifᵉ bothᵉ `xᵉ ≤ᵉ y`ᵉ andᵉ `yᵉ ≤ᵉ x`ᵉ hold.ᵉ Noteᵉ thatᵉ theᵉ
similarityᵉ relationᵉ isᵉ definedᵉ acrossᵉ universeᵉ levels,ᵉ andᵉ thatᵉ onlyᵉ similarᵉ
elementsᵉ ofᵉ theᵉ sameᵉ universeᵉ levelᵉ areᵉ equal.ᵉ

Inᵉ informalᵉ writingᵉ weᵉ willᵉ useᵉ theᵉ notationᵉ `xᵉ ≈ᵉ y`ᵉ to assertᵉ thatᵉ `x`ᵉ andᵉ `y`ᵉ
areᵉ similarᵉ elementsᵉ in aᵉ posetᵉ `P`.ᵉ

## Definition

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  sim-prop-Large-Posetᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
    Propᵉ (βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l2ᵉ l1ᵉ)
  sim-prop-Large-Posetᵉ = sim-prop-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Pᵉ)

  sim-Large-Posetᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ)
    (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
    UUᵉ (βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l2ᵉ l1ᵉ)
  sim-Large-Posetᵉ = sim-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Pᵉ)

  is-prop-sim-Large-Posetᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
    is-propᵉ (sim-Large-Posetᵉ xᵉ yᵉ)
  is-prop-sim-Large-Posetᵉ =
    is-prop-sim-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Pᵉ)
```

## Properties

### The similarity relation is reflexive

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  refl-sim-Large-Posetᵉ :
    is-reflexive-Large-Relationᵉ (type-Large-Posetᵉ Pᵉ) (sim-Large-Posetᵉ Pᵉ)
  refl-sim-Large-Posetᵉ = refl-sim-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Pᵉ)
```

### The similarity relation is transitive

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  transitive-sim-Large-Posetᵉ :
    is-transitive-Large-Relationᵉ (type-Large-Posetᵉ Pᵉ) (sim-Large-Posetᵉ Pᵉ)
  transitive-sim-Large-Posetᵉ =
    transitive-sim-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Pᵉ)
```

### The similarity relation is symmetric

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  symmetric-sim-Large-Posetᵉ :
    is-symmetric-Large-Relationᵉ (type-Large-Posetᵉ Pᵉ) (sim-Large-Posetᵉ Pᵉ)
  symmetric-sim-Large-Posetᵉ =
    symmetric-sim-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Pᵉ)
```

### For any universe level `l`, any element `x` is similar to at most one element of universe level `l`

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  all-elements-equal-total-sim-Large-Posetᵉ :
    {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) →
    all-elements-equalᵉ (Σᵉ (type-Large-Posetᵉ Pᵉ l2ᵉ) (sim-Large-Posetᵉ Pᵉ xᵉ))
  all-elements-equal-total-sim-Large-Posetᵉ xᵉ (yᵉ ,ᵉ Hᵉ) (zᵉ ,ᵉ Kᵉ) =
    eq-type-subtypeᵉ
      ( sim-prop-Large-Posetᵉ Pᵉ xᵉ)
      ( antisymmetric-leq-Large-Posetᵉ Pᵉ
        ( yᵉ)
        ( zᵉ)
        ( transitive-leq-Large-Posetᵉ Pᵉ _ _ _ (pr1ᵉ Kᵉ) (pr2ᵉ Hᵉ))
        ( transitive-leq-Large-Posetᵉ Pᵉ _ _ _ (pr1ᵉ Hᵉ) (pr2ᵉ Kᵉ)))

  is-prop-total-sim-Large-Posetᵉ :
    {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) →
    is-propᵉ (Σᵉ (type-Large-Posetᵉ Pᵉ l2ᵉ) (sim-Large-Posetᵉ Pᵉ xᵉ))
  is-prop-total-sim-Large-Posetᵉ xᵉ =
    is-prop-all-elements-equalᵉ
      ( all-elements-equal-total-sim-Large-Posetᵉ xᵉ)

  is-torsorial-sim-Large-Posetᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) →
    is-torsorialᵉ (sim-Large-Posetᵉ Pᵉ xᵉ)
  is-torsorial-sim-Large-Posetᵉ xᵉ =
    is-proof-irrelevant-is-propᵉ
      ( is-prop-total-sim-Large-Posetᵉ xᵉ)
      ( xᵉ ,ᵉ refl-sim-Large-Posetᵉ Pᵉ xᵉ)
```

### Similarity characterizes the identity type of elements in a large poset of the same universe level

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  sim-eq-Large-Posetᵉ :
    {l1ᵉ : Level} {xᵉ yᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ} →
    xᵉ ＝ᵉ yᵉ → sim-Large-Posetᵉ Pᵉ xᵉ yᵉ
  sim-eq-Large-Posetᵉ reflᵉ = refl-sim-Large-Posetᵉ Pᵉ _

  is-equiv-sim-eq-Large-Posetᵉ :
    {l1ᵉ : Level} (xᵉ yᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) →
    is-equivᵉ (sim-eq-Large-Posetᵉ {l1ᵉ} {xᵉ} {yᵉ})
  is-equiv-sim-eq-Large-Posetᵉ xᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-sim-Large-Posetᵉ Pᵉ xᵉ)
      ( λ yᵉ → sim-eq-Large-Posetᵉ {ᵉ_} {xᵉ} {yᵉ})

  extensionality-Large-Posetᵉ :
    {l1ᵉ : Level} (xᵉ yᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) →
    (xᵉ ＝ᵉ yᵉ) ≃ᵉ sim-Large-Posetᵉ Pᵉ xᵉ yᵉ
  pr1ᵉ (extensionality-Large-Posetᵉ xᵉ yᵉ) = sim-eq-Large-Posetᵉ
  pr2ᵉ (extensionality-Large-Posetᵉ xᵉ yᵉ) = is-equiv-sim-eq-Large-Posetᵉ xᵉ yᵉ

  eq-sim-Large-Posetᵉ :
    {l1ᵉ : Level} (xᵉ yᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) →
    sim-Large-Posetᵉ Pᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-sim-Large-Posetᵉ xᵉ yᵉ = map-inv-is-equivᵉ (is-equiv-sim-eq-Large-Posetᵉ xᵉ yᵉ)
```