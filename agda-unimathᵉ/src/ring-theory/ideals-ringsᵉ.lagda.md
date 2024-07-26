# Ideals of rings

```agda
module ring-theory.ideals-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.binary-transportᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.congruence-relations-abelian-groupsᵉ
open import group-theory.congruence-relations-monoidsᵉ
open import group-theory.subgroups-abelian-groupsᵉ

open import ring-theory.congruence-relations-ringsᵉ
open import ring-theory.left-ideals-ringsᵉ
open import ring-theory.right-ideals-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Anᵉ **ideal**ᵉ in aᵉ [ring](ring-theory.rings.mdᵉ) `R`ᵉ isᵉ aᵉ submoduleᵉ ofᵉ `R`.ᵉ

## Definitions

### Two-sided ideals

```agda
is-ideal-subset-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Pᵉ : subset-Ringᵉ l2ᵉ Rᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-ideal-subset-Ringᵉ Rᵉ Pᵉ =
  is-additive-subgroup-subset-Ringᵉ Rᵉ Pᵉ ×ᵉ
  ( is-closed-under-left-multiplication-subset-Ringᵉ Rᵉ Pᵉ ×ᵉ
    is-closed-under-right-multiplication-subset-Ringᵉ Rᵉ Pᵉ)

is-prop-is-ideal-subset-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Pᵉ : subset-Ringᵉ l2ᵉ Rᵉ) →
  is-propᵉ (is-ideal-subset-Ringᵉ Rᵉ Pᵉ)
is-prop-is-ideal-subset-Ringᵉ Rᵉ Pᵉ =
  is-prop-productᵉ
    ( is-prop-is-additive-subgroup-subset-Ringᵉ Rᵉ Pᵉ)
    ( is-prop-productᵉ
      ( is-prop-is-closed-under-left-multiplication-subset-Ringᵉ Rᵉ Pᵉ)
      ( is-prop-is-closed-under-right-multiplication-subset-Ringᵉ Rᵉ Pᵉ))

ideal-Ringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
ideal-Ringᵉ lᵉ Rᵉ =
  Σᵉ (subset-Ringᵉ lᵉ Rᵉ) (is-ideal-subset-Ringᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  subset-ideal-Ringᵉ : subset-Ringᵉ l2ᵉ Rᵉ
  subset-ideal-Ringᵉ = pr1ᵉ Iᵉ

  is-in-ideal-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ l2ᵉ
  is-in-ideal-Ringᵉ xᵉ = type-Propᵉ (subset-ideal-Ringᵉ xᵉ)

  type-ideal-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-ideal-Ringᵉ = type-subset-Ringᵉ Rᵉ subset-ideal-Ringᵉ

  inclusion-ideal-Ringᵉ : type-ideal-Ringᵉ → type-Ringᵉ Rᵉ
  inclusion-ideal-Ringᵉ =
    inclusion-subset-Ringᵉ Rᵉ subset-ideal-Ringᵉ

  ap-inclusion-ideal-Ringᵉ :
    (xᵉ yᵉ : type-ideal-Ringᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-ideal-Ringᵉ xᵉ ＝ᵉ inclusion-ideal-Ringᵉ yᵉ
  ap-inclusion-ideal-Ringᵉ = ap-inclusion-subset-Ringᵉ Rᵉ subset-ideal-Ringᵉ

  is-in-subset-inclusion-ideal-Ringᵉ :
    (xᵉ : type-ideal-Ringᵉ) → is-in-ideal-Ringᵉ (inclusion-ideal-Ringᵉ xᵉ)
  is-in-subset-inclusion-ideal-Ringᵉ =
    is-in-subset-inclusion-subset-Ringᵉ Rᵉ subset-ideal-Ringᵉ

  is-closed-under-eq-ideal-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → is-in-ideal-Ringᵉ xᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-ideal-Ringᵉ yᵉ
  is-closed-under-eq-ideal-Ringᵉ =
    is-closed-under-eq-subset-Ringᵉ Rᵉ subset-ideal-Ringᵉ

  is-closed-under-eq-ideal-Ring'ᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → is-in-ideal-Ringᵉ yᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-ideal-Ringᵉ xᵉ
  is-closed-under-eq-ideal-Ring'ᵉ =
    is-closed-under-eq-subset-Ring'ᵉ Rᵉ subset-ideal-Ringᵉ

  is-ideal-ideal-Ringᵉ :
    is-ideal-subset-Ringᵉ Rᵉ subset-ideal-Ringᵉ
  is-ideal-ideal-Ringᵉ = pr2ᵉ Iᵉ

  is-additive-subgroup-ideal-Ringᵉ :
    is-additive-subgroup-subset-Ringᵉ Rᵉ subset-ideal-Ringᵉ
  is-additive-subgroup-ideal-Ringᵉ =
    pr1ᵉ is-ideal-ideal-Ringᵉ

  contains-zero-ideal-Ringᵉ : contains-zero-subset-Ringᵉ Rᵉ subset-ideal-Ringᵉ
  contains-zero-ideal-Ringᵉ = pr1ᵉ is-additive-subgroup-ideal-Ringᵉ

  is-closed-under-addition-ideal-Ringᵉ :
    is-closed-under-addition-subset-Ringᵉ Rᵉ subset-ideal-Ringᵉ
  is-closed-under-addition-ideal-Ringᵉ =
    pr1ᵉ (pr2ᵉ is-additive-subgroup-ideal-Ringᵉ)

  is-closed-under-negatives-ideal-Ringᵉ :
    is-closed-under-negatives-subset-Ringᵉ Rᵉ subset-ideal-Ringᵉ
  is-closed-under-negatives-ideal-Ringᵉ =
    pr2ᵉ (pr2ᵉ is-additive-subgroup-ideal-Ringᵉ)

  is-closed-under-left-multiplication-ideal-Ringᵉ :
    is-closed-under-left-multiplication-subset-Ringᵉ Rᵉ subset-ideal-Ringᵉ
  is-closed-under-left-multiplication-ideal-Ringᵉ =
    pr1ᵉ (pr2ᵉ is-ideal-ideal-Ringᵉ)

  is-closed-under-right-multiplication-ideal-Ringᵉ :
    is-closed-under-right-multiplication-subset-Ringᵉ Rᵉ subset-ideal-Ringᵉ
  is-closed-under-right-multiplication-ideal-Ringᵉ =
    pr2ᵉ (pr2ᵉ is-ideal-ideal-Ringᵉ)

  subgroup-ideal-Ringᵉ : Subgroup-Abᵉ l2ᵉ (ab-Ringᵉ Rᵉ)
  pr1ᵉ subgroup-ideal-Ringᵉ = subset-ideal-Ringᵉ
  pr1ᵉ (pr2ᵉ subgroup-ideal-Ringᵉ) = contains-zero-ideal-Ringᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ subgroup-ideal-Ringᵉ)) = is-closed-under-addition-ideal-Ringᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ subgroup-ideal-Ringᵉ)) = is-closed-under-negatives-ideal-Ringᵉ

  normal-subgroup-ideal-Ringᵉ : Normal-Subgroup-Abᵉ l2ᵉ (ab-Ringᵉ Rᵉ)
  normal-subgroup-ideal-Ringᵉ =
    normal-subgroup-Subgroup-Abᵉ (ab-Ringᵉ Rᵉ) subgroup-ideal-Ringᵉ

  left-ideal-ideal-Ringᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ
  pr1ᵉ left-ideal-ideal-Ringᵉ = subset-ideal-Ringᵉ
  pr1ᵉ (pr2ᵉ left-ideal-ideal-Ringᵉ) = is-additive-subgroup-ideal-Ringᵉ
  pr2ᵉ (pr2ᵉ left-ideal-ideal-Ringᵉ) =
    is-closed-under-left-multiplication-ideal-Ringᵉ

  right-ideal-ideal-Ringᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ
  pr1ᵉ right-ideal-ideal-Ringᵉ = subset-ideal-Ringᵉ
  pr1ᵉ (pr2ᵉ right-ideal-ideal-Ringᵉ) = is-additive-subgroup-ideal-Ringᵉ
  pr2ᵉ (pr2ᵉ right-ideal-ideal-Ringᵉ) =
    is-closed-under-right-multiplication-ideal-Ringᵉ
```

## Properties

### Characterizing equality of ideals in rings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  has-same-elements-ideal-Ringᵉ : (Jᵉ : ideal-Ringᵉ l3ᵉ Rᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-ideal-Ringᵉ Jᵉ =
    has-same-elements-subtypeᵉ (subset-ideal-Ringᵉ Rᵉ Iᵉ) (subset-ideal-Ringᵉ Rᵉ Jᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  refl-has-same-elements-ideal-Ringᵉ :
    has-same-elements-ideal-Ringᵉ Rᵉ Iᵉ Iᵉ
  refl-has-same-elements-ideal-Ringᵉ =
    refl-has-same-elements-subtypeᵉ (subset-ideal-Ringᵉ Rᵉ Iᵉ)

  is-torsorial-has-same-elements-ideal-Ringᵉ :
    is-torsorialᵉ (has-same-elements-ideal-Ringᵉ Rᵉ Iᵉ)
  is-torsorial-has-same-elements-ideal-Ringᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-has-same-elements-subtypeᵉ (subset-ideal-Ringᵉ Rᵉ Iᵉ))
      ( is-prop-is-ideal-subset-Ringᵉ Rᵉ)
      ( subset-ideal-Ringᵉ Rᵉ Iᵉ)
      ( refl-has-same-elements-ideal-Ringᵉ)
      ( is-ideal-ideal-Ringᵉ Rᵉ Iᵉ)

  has-same-elements-eq-ideal-Ringᵉ :
    (Jᵉ : ideal-Ringᵉ l2ᵉ Rᵉ) → (Iᵉ ＝ᵉ Jᵉ) → has-same-elements-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ
  has-same-elements-eq-ideal-Ringᵉ .Iᵉ reflᵉ = refl-has-same-elements-ideal-Ringᵉ

  is-equiv-has-same-elements-eq-ideal-Ringᵉ :
    (Jᵉ : ideal-Ringᵉ l2ᵉ Rᵉ) → is-equivᵉ (has-same-elements-eq-ideal-Ringᵉ Jᵉ)
  is-equiv-has-same-elements-eq-ideal-Ringᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-has-same-elements-ideal-Ringᵉ
      has-same-elements-eq-ideal-Ringᵉ

  extensionality-ideal-Ringᵉ :
    (Jᵉ : ideal-Ringᵉ l2ᵉ Rᵉ) → (Iᵉ ＝ᵉ Jᵉ) ≃ᵉ has-same-elements-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ
  pr1ᵉ (extensionality-ideal-Ringᵉ Jᵉ) = has-same-elements-eq-ideal-Ringᵉ Jᵉ
  pr2ᵉ (extensionality-ideal-Ringᵉ Jᵉ) = is-equiv-has-same-elements-eq-ideal-Ringᵉ Jᵉ

  eq-has-same-elements-ideal-Ringᵉ :
    (Jᵉ : ideal-Ringᵉ l2ᵉ Rᵉ) → has-same-elements-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ → Iᵉ ＝ᵉ Jᵉ
  eq-has-same-elements-ideal-Ringᵉ Jᵉ =
    map-inv-equivᵉ (extensionality-ideal-Ringᵉ Jᵉ)
```

### Two sided ideals of rings are in 1-1 correspondence with congruence relations

#### The standard similarity relation obtained from an ideal

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  sim-congruence-ideal-Ringᵉ : (xᵉ yᵉ : type-Ringᵉ Rᵉ) → UUᵉ l2ᵉ
  sim-congruence-ideal-Ringᵉ =
    sim-congruence-Subgroup-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( subgroup-ideal-Ringᵉ Rᵉ Iᵉ)

  is-prop-sim-congruence-ideal-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) → is-propᵉ (sim-congruence-ideal-Ringᵉ xᵉ yᵉ)
  is-prop-sim-congruence-ideal-Ringᵉ =
    is-prop-sim-congruence-Subgroup-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( subgroup-ideal-Ringᵉ Rᵉ Iᵉ)

  prop-congruence-ideal-Ringᵉ : (xᵉ yᵉ : type-Ringᵉ Rᵉ) → Propᵉ l2ᵉ
  prop-congruence-ideal-Ringᵉ =
    prop-congruence-Subgroup-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( subgroup-ideal-Ringᵉ Rᵉ Iᵉ)
```

#### The left equivalence relation obtained from an ideal

```agda
  left-equivalence-relation-congruence-ideal-Ringᵉ :
    equivalence-relationᵉ l2ᵉ (type-Ringᵉ Rᵉ)
  left-equivalence-relation-congruence-ideal-Ringᵉ =
    left-equivalence-relation-congruence-Subgroup-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( subgroup-ideal-Ringᵉ Rᵉ Iᵉ)

  left-sim-congruence-ideal-Ringᵉ :
    type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ → UUᵉ l2ᵉ
  left-sim-congruence-ideal-Ringᵉ =
    left-sim-congruence-Subgroup-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( subgroup-ideal-Ringᵉ Rᵉ Iᵉ)
```

#### The left similarity relation of an ideal relates the same elements as the standard similarity relation

```agda
  left-sim-sim-congruence-ideal-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    sim-congruence-ideal-Ringᵉ xᵉ yᵉ →
    left-sim-congruence-ideal-Ringᵉ xᵉ yᵉ
  left-sim-sim-congruence-ideal-Ringᵉ =
    left-sim-sim-congruence-Subgroup-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( subgroup-ideal-Ringᵉ Rᵉ Iᵉ)

  sim-left-sim-congruence-ideal-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    left-sim-congruence-ideal-Ringᵉ xᵉ yᵉ →
    sim-congruence-ideal-Ringᵉ xᵉ yᵉ
  sim-left-sim-congruence-ideal-Ringᵉ =
    sim-left-sim-congruence-Subgroup-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( subgroup-ideal-Ringᵉ Rᵉ Iᵉ)
```

#### The standard similarity relation is a congruence relation

```agda
  refl-congruence-ideal-Ringᵉ :
    is-reflexiveᵉ sim-congruence-ideal-Ringᵉ
  refl-congruence-ideal-Ringᵉ =
    refl-congruence-Subgroup-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( subgroup-ideal-Ringᵉ Rᵉ Iᵉ)

  symmetric-congruence-ideal-Ringᵉ :
    is-symmetricᵉ sim-congruence-ideal-Ringᵉ
  symmetric-congruence-ideal-Ringᵉ =
    symmetric-congruence-Subgroup-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( subgroup-ideal-Ringᵉ Rᵉ Iᵉ)

  transitive-congruence-ideal-Ringᵉ :
    is-transitiveᵉ sim-congruence-ideal-Ringᵉ
  transitive-congruence-ideal-Ringᵉ =
    transitive-congruence-Subgroup-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( subgroup-ideal-Ringᵉ Rᵉ Iᵉ)

  equivalence-relation-congruence-ideal-Ringᵉ :
    equivalence-relationᵉ l2ᵉ (type-Ringᵉ Rᵉ)
  equivalence-relation-congruence-ideal-Ringᵉ =
    equivalence-relation-congruence-Subgroup-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( subgroup-ideal-Ringᵉ Rᵉ Iᵉ)

  relate-same-elements-left-sim-congruence-ideal-Ringᵉ :
    relate-same-elements-equivalence-relationᵉ
      ( equivalence-relation-congruence-ideal-Ringᵉ)
      ( left-equivalence-relation-congruence-ideal-Ringᵉ)
  relate-same-elements-left-sim-congruence-ideal-Ringᵉ =
    relate-same-elements-left-sim-congruence-Subgroup-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( subgroup-ideal-Ringᵉ Rᵉ Iᵉ)

  add-congruence-ideal-Ringᵉ :
    ( is-congruence-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( equivalence-relation-congruence-ideal-Ringᵉ))
  add-congruence-ideal-Ringᵉ =
    ( add-congruence-Subgroup-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( subgroup-ideal-Ringᵉ Rᵉ Iᵉ))

  is-congruence-monoid-mul-congruence-ideal-Ringᵉ :
    { xᵉ yᵉ uᵉ vᵉ : type-Ringᵉ Rᵉ} →
    ( is-in-ideal-Ringᵉ Rᵉ Iᵉ (add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) yᵉ)) →
    ( is-in-ideal-Ringᵉ Rᵉ Iᵉ (add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ uᵉ) vᵉ)) →
    ( is-in-ideal-Ringᵉ Rᵉ Iᵉ
      ( add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ uᵉ)) (mul-Ringᵉ Rᵉ yᵉ vᵉ)))
  is-congruence-monoid-mul-congruence-ideal-Ringᵉ {xᵉ} {yᵉ} {uᵉ} {vᵉ} eᵉ fᵉ =
    ( is-closed-under-eq-ideal-Ringᵉ Rᵉ Iᵉ
      ( is-closed-under-addition-ideal-Ringᵉ Rᵉ Iᵉ
        ( is-closed-under-right-multiplication-ideal-Ringᵉ Rᵉ Iᵉ
          ( add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) yᵉ)
          ( uᵉ)
          ( eᵉ))
        ( is-closed-under-left-multiplication-ideal-Ringᵉ Rᵉ Iᵉ
          ( yᵉ)
          ( add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ uᵉ) vᵉ)
          ( fᵉ))))
    ( equational-reasoningᵉ
      ( add-Ringᵉ Rᵉ
        ( mul-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) yᵉ) uᵉ)
        ( mul-Ringᵉ Rᵉ yᵉ (add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ uᵉ) vᵉ)))
    ＝ᵉ ( add-Ringᵉ Rᵉ
        ( mul-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) yᵉ) uᵉ)
        ( add-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ yᵉ (neg-Ringᵉ Rᵉ uᵉ)) (mul-Ringᵉ Rᵉ yᵉ vᵉ)))
      byᵉ
      ( apᵉ
        ( add-Ringᵉ Rᵉ ( mul-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) yᵉ) uᵉ))
        ( left-distributive-mul-add-Ringᵉ Rᵉ yᵉ (neg-Ringᵉ Rᵉ uᵉ) vᵉ))
    ＝ᵉ ( add-Ringᵉ Rᵉ
        ( mul-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) yᵉ) uᵉ)
        ( add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ yᵉ uᵉ)) (mul-Ringᵉ Rᵉ yᵉ vᵉ)))
      byᵉ
      ( apᵉ
        ( λ aᵉ →
          add-Ringᵉ Rᵉ
            ( mul-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) yᵉ) uᵉ)
            ( add-Ringᵉ Rᵉ aᵉ (mul-Ringᵉ Rᵉ yᵉ vᵉ)))
        ( right-negative-law-mul-Ringᵉ Rᵉ yᵉ uᵉ))
    ＝ᵉ ( add-Ringᵉ Rᵉ
        ( add-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) uᵉ) (mul-Ringᵉ Rᵉ yᵉ uᵉ))
        ( add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ yᵉ uᵉ)) (mul-Ringᵉ Rᵉ yᵉ vᵉ)))
      byᵉ
      ( apᵉ
        ( add-Ring'ᵉ Rᵉ
          ( add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ yᵉ uᵉ)) (mul-Ringᵉ Rᵉ yᵉ vᵉ)))
        ( right-distributive-mul-add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) yᵉ uᵉ))
    ＝ᵉ ( add-Ringᵉ Rᵉ
        ( add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ uᵉ)) (mul-Ringᵉ Rᵉ yᵉ uᵉ))
        ( add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ yᵉ uᵉ)) (mul-Ringᵉ Rᵉ yᵉ vᵉ)))
      byᵉ
      ( apᵉ
        ( λ aᵉ →
          add-Ringᵉ Rᵉ
            ( add-Ringᵉ Rᵉ aᵉ (mul-Ringᵉ Rᵉ yᵉ uᵉ))
            ( add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ yᵉ uᵉ)) (mul-Ringᵉ Rᵉ yᵉ vᵉ)))
        ( left-negative-law-mul-Ringᵉ Rᵉ xᵉ uᵉ))
    ＝ᵉ ( add-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ uᵉ)) (mul-Ringᵉ Rᵉ yᵉ vᵉ))
      byᵉ
      ( add-and-subtract-Ringᵉ Rᵉ
        ( neg-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ uᵉ))
        ( mul-Ringᵉ Rᵉ yᵉ uᵉ)
        ( mul-Ringᵉ Rᵉ yᵉ vᵉ)))

  mul-congruence-ideal-Ringᵉ :
    ( is-congruence-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( equivalence-relation-congruence-ideal-Ringᵉ))
  mul-congruence-ideal-Ringᵉ =
    is-congruence-monoid-mul-congruence-ideal-Ringᵉ

  congruence-ideal-Ringᵉ : congruence-Ringᵉ l2ᵉ Rᵉ
  congruence-ideal-Ringᵉ = construct-congruence-Ringᵉ Rᵉ
    ( equivalence-relation-congruence-ideal-Ringᵉ)
    ( add-congruence-ideal-Ringᵉ)
    ( mul-congruence-ideal-Ringᵉ)
```

#### The ideal obtained from a congruence relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : congruence-Ringᵉ l2ᵉ Rᵉ)
  where

  subset-congruence-Ringᵉ : subset-Ringᵉ l2ᵉ Rᵉ
  subset-congruence-Ringᵉ = prop-congruence-Ringᵉ Rᵉ Sᵉ (zero-Ringᵉ Rᵉ)

  is-in-subset-congruence-Ringᵉ : (type-Ringᵉ Rᵉ) → UUᵉ l2ᵉ
  is-in-subset-congruence-Ringᵉ = type-Propᵉ ∘ᵉ subset-congruence-Ringᵉ

  contains-zero-subset-congruence-Ringᵉ :
    contains-zero-subset-Ringᵉ Rᵉ subset-congruence-Ringᵉ
  contains-zero-subset-congruence-Ringᵉ =
    refl-congruence-Ringᵉ Rᵉ Sᵉ (zero-Ringᵉ Rᵉ)

  is-closed-under-addition-subset-congruence-Ringᵉ :
    is-closed-under-addition-subset-Ringᵉ Rᵉ subset-congruence-Ringᵉ
  is-closed-under-addition-subset-congruence-Ringᵉ Hᵉ Kᵉ =
    concatenate-eq-sim-congruence-Ringᵉ Rᵉ Sᵉ
      ( invᵉ (left-unit-law-add-Ringᵉ Rᵉ (zero-Ringᵉ Rᵉ)))
      ( add-congruence-Ringᵉ Rᵉ Sᵉ Hᵉ Kᵉ)

  is-closed-under-negatives-subset-congruence-Ringᵉ :
    is-closed-under-negatives-subset-Ringᵉ Rᵉ subset-congruence-Ringᵉ
  is-closed-under-negatives-subset-congruence-Ringᵉ Hᵉ =
      concatenate-eq-sim-congruence-Ringᵉ Rᵉ Sᵉ
        ( invᵉ (neg-zero-Ringᵉ Rᵉ))
        ( neg-congruence-Ringᵉ Rᵉ Sᵉ Hᵉ)

  is-closed-under-left-multiplication-subset-congruence-Ringᵉ :
    is-closed-under-left-multiplication-subset-Ringᵉ Rᵉ subset-congruence-Ringᵉ
  is-closed-under-left-multiplication-subset-congruence-Ringᵉ xᵉ yᵉ Hᵉ =
    concatenate-eq-sim-congruence-Ringᵉ Rᵉ Sᵉ
      ( invᵉ (right-zero-law-mul-Ringᵉ Rᵉ xᵉ))
      ( left-mul-congruence-Ringᵉ Rᵉ Sᵉ xᵉ Hᵉ)

  is-closed-under-right-multiplication-subset-congruence-Ringᵉ :
    is-closed-under-right-multiplication-subset-Ringᵉ Rᵉ subset-congruence-Ringᵉ
  is-closed-under-right-multiplication-subset-congruence-Ringᵉ xᵉ yᵉ Hᵉ =
    concatenate-eq-sim-congruence-Ringᵉ Rᵉ Sᵉ
      ( invᵉ (left-zero-law-mul-Ringᵉ Rᵉ yᵉ))
      ( right-mul-congruence-Ringᵉ Rᵉ Sᵉ Hᵉ yᵉ)

  is-additive-subgroup-congruence-Ringᵉ :
    is-additive-subgroup-subset-Ringᵉ Rᵉ subset-congruence-Ringᵉ
  pr1ᵉ is-additive-subgroup-congruence-Ringᵉ =
    contains-zero-subset-congruence-Ringᵉ
  pr1ᵉ (pr2ᵉ is-additive-subgroup-congruence-Ringᵉ) =
    is-closed-under-addition-subset-congruence-Ringᵉ
  pr2ᵉ (pr2ᵉ is-additive-subgroup-congruence-Ringᵉ) =
    is-closed-under-negatives-subset-congruence-Ringᵉ

  ideal-congruence-Ringᵉ : ideal-Ringᵉ l2ᵉ Rᵉ
  pr1ᵉ ideal-congruence-Ringᵉ =
    subset-congruence-Ringᵉ
  pr1ᵉ (pr2ᵉ ideal-congruence-Ringᵉ) =
    is-additive-subgroup-congruence-Ringᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ ideal-congruence-Ringᵉ)) =
    is-closed-under-left-multiplication-subset-congruence-Ringᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ ideal-congruence-Ringᵉ)) =
    is-closed-under-right-multiplication-subset-congruence-Ringᵉ
```

#### The ideal obtained from the congruence relation of an ideal `I` is `I` itself

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  has-same-elements-ideal-congruence-Ringᵉ :
    has-same-elements-ideal-Ringᵉ Rᵉ
      ( ideal-congruence-Ringᵉ Rᵉ (congruence-ideal-Ringᵉ Rᵉ Iᵉ))
      ( Iᵉ)
  pr1ᵉ (has-same-elements-ideal-congruence-Ringᵉ xᵉ) Hᵉ =
    is-closed-under-eq-ideal-Ringᵉ Rᵉ Iᵉ Hᵉ
      ( ( apᵉ (add-Ring'ᵉ Rᵉ xᵉ) (neg-zero-Ringᵉ Rᵉ)) ∙ᵉ
        ( left-unit-law-add-Ringᵉ Rᵉ xᵉ))
  pr2ᵉ (has-same-elements-ideal-congruence-Ringᵉ xᵉ) Hᵉ =
    is-closed-under-eq-ideal-Ring'ᵉ Rᵉ Iᵉ Hᵉ
      ( ( apᵉ (add-Ring'ᵉ Rᵉ xᵉ) (neg-zero-Ringᵉ Rᵉ)) ∙ᵉ
        ( left-unit-law-add-Ringᵉ Rᵉ xᵉ))

  is-retraction-ideal-congruence-Ringᵉ :
    ideal-congruence-Ringᵉ Rᵉ (congruence-ideal-Ringᵉ Rᵉ Iᵉ) ＝ᵉ Iᵉ
  is-retraction-ideal-congruence-Ringᵉ =
    eq-has-same-elements-ideal-Ringᵉ Rᵉ
      ( ideal-congruence-Ringᵉ Rᵉ (congruence-ideal-Ringᵉ Rᵉ Iᵉ))
      ( Iᵉ)
      ( has-same-elements-ideal-congruence-Ringᵉ)
```

#### The congruence relation of the ideal obtained from a congruence relation `S` is `S` itself

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : congruence-Ringᵉ l2ᵉ Rᵉ)
  where

  relate-same-elements-congruence-ideal-congruence-Ringᵉ :
    relate-same-elements-congruence-Ringᵉ Rᵉ
      ( congruence-ideal-Ringᵉ Rᵉ (ideal-congruence-Ringᵉ Rᵉ Sᵉ))
      ( Sᵉ)
  pr1ᵉ
    ( relate-same-elements-congruence-ideal-congruence-Ringᵉ xᵉ yᵉ) Hᵉ =
    binary-trᵉ
      ( sim-congruence-Ringᵉ Rᵉ Sᵉ)
      ( right-unit-law-add-Ringᵉ Rᵉ xᵉ)
      ( is-section-left-subtraction-Ringᵉ Rᵉ xᵉ yᵉ)
      ( left-add-congruence-Ringᵉ Rᵉ Sᵉ xᵉ Hᵉ)
  pr2ᵉ
    ( relate-same-elements-congruence-ideal-congruence-Ringᵉ xᵉ yᵉ) Hᵉ =
    symmetric-congruence-Ringᵉ Rᵉ Sᵉ
      ( left-subtraction-Ringᵉ Rᵉ xᵉ yᵉ)
      ( zero-Ringᵉ Rᵉ)
      ( map-sim-left-subtraction-zero-congruence-Ringᵉ Rᵉ Sᵉ Hᵉ)

  is-section-ideal-congruence-Ringᵉ :
    congruence-ideal-Ringᵉ Rᵉ (ideal-congruence-Ringᵉ Rᵉ Sᵉ) ＝ᵉ Sᵉ
  is-section-ideal-congruence-Ringᵉ =
    eq-relate-same-elements-congruence-Ringᵉ Rᵉ
      ( congruence-ideal-Ringᵉ Rᵉ (ideal-congruence-Ringᵉ Rᵉ Sᵉ))
      ( Sᵉ)
      ( relate-same-elements-congruence-ideal-congruence-Ringᵉ)
```

#### The equivalence of two sided ideals and congruence relations

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  is-equiv-congruence-ideal-Ringᵉ :
    is-equivᵉ (congruence-ideal-Ringᵉ {l1ᵉ} {l2ᵉ} Rᵉ)
  is-equiv-congruence-ideal-Ringᵉ =
    is-equiv-is-invertibleᵉ
      ( ideal-congruence-Ringᵉ Rᵉ)
      ( is-section-ideal-congruence-Ringᵉ Rᵉ)
      ( is-retraction-ideal-congruence-Ringᵉ Rᵉ)

  equiv-congruence-ideal-Ringᵉ :
    ideal-Ringᵉ l2ᵉ Rᵉ ≃ᵉ congruence-Ringᵉ l2ᵉ Rᵉ
  pr1ᵉ equiv-congruence-ideal-Ringᵉ = congruence-ideal-Ringᵉ Rᵉ
  pr2ᵉ equiv-congruence-ideal-Ringᵉ = is-equiv-congruence-ideal-Ringᵉ

  is-equiv-ideal-congruence-Ringᵉ :
    is-equivᵉ (ideal-congruence-Ringᵉ {l1ᵉ} {l2ᵉ} Rᵉ)
  is-equiv-ideal-congruence-Ringᵉ =
    is-equiv-is-invertibleᵉ
      ( congruence-ideal-Ringᵉ Rᵉ)
      ( is-retraction-ideal-congruence-Ringᵉ Rᵉ)
      ( is-section-ideal-congruence-Ringᵉ Rᵉ)

  equiv-ideal-congruence-Ringᵉ :
    congruence-Ringᵉ l2ᵉ Rᵉ ≃ᵉ ideal-Ringᵉ l2ᵉ Rᵉ
  pr1ᵉ equiv-ideal-congruence-Ringᵉ = ideal-congruence-Ringᵉ Rᵉ
  pr2ᵉ equiv-ideal-congruence-Ringᵉ = is-equiv-ideal-congruence-Ringᵉ
```