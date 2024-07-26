# The orbit-stabilizer theorem for concrete groups

```agda
module group-theory.orbit-stabilizer-theorem-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-group-actionsᵉ
open import group-theory.concrete-groupsᵉ
open import group-theory.mere-equivalences-concrete-group-actionsᵉ
open import group-theory.stabilizer-groups-concrete-group-actionsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Theᵉ orbitᵉ stabilizerᵉ theoremᵉ forᵉ concreteᵉ groupsᵉ assertsᵉ thatᵉ theᵉ typeᵉ
`Orbit(x)`ᵉ ofᵉ orbitsᵉ ofᵉ anᵉ elementᵉ `xᵉ : Xᵉ *`ᵉ isᵉ deloopableᵉ andᵉ fitsᵉ in aᵉ fiberᵉ
sequenceᵉ

```text
  BG_xᵉ ---->ᵉ BGᵉ ---->ᵉ B(Orbit(xᵉ))
```

Toᵉ seeᵉ thatᵉ thisᵉ isᵉ indeedᵉ aᵉ formulationᵉ ofᵉ theᵉ orbit-stabilizerᵉ theorem,ᵉ noteᵉ
thatᵉ theᵉ deloopingᵉ ofᵉ `Orbit(x)`ᵉ givesᵉ `Orbit(x)`ᵉ theᵉ structureᵉ ofᵉ aᵉ group.ᵉ
Furthermore,ᵉ thisᵉ fiberᵉ sequenceᵉ inducesᵉ aᵉ shortᵉ exactᵉ sequenceᵉ

```text
  G_xᵉ ---->ᵉ Gᵉ ---->ᵉ Orbit(x),ᵉ
```

whichᵉ inducesᵉ aᵉ bijectionᵉ fromᵉ theᵉ cosetsᵉ ofᵉ theᵉ stabilizerᵉ subgroupᵉ `G_x`ᵉ ofᵉ
`G`ᵉ to theᵉ typeᵉ `Orbit(x)`.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  classifying-type-quotient-stabilizer-action-Concrete-Groupᵉ :
    type-action-Concrete-Groupᵉ Gᵉ Xᵉ → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
  classifying-type-quotient-stabilizer-action-Concrete-Groupᵉ xᵉ =
    Σᵉ ( action-Concrete-Groupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ)
      ( mere-equiv-action-Concrete-Groupᵉ Gᵉ
        ( action-stabilizer-action-Concrete-Groupᵉ Gᵉ Xᵉ xᵉ))

  point-classifying-type-quotient-stabilizer-action-Concrete-Groupᵉ :
    (xᵉ : type-action-Concrete-Groupᵉ Gᵉ Xᵉ) →
    classifying-type-quotient-stabilizer-action-Concrete-Groupᵉ xᵉ
  pr1ᵉ (point-classifying-type-quotient-stabilizer-action-Concrete-Groupᵉ xᵉ) =
    action-stabilizer-action-Concrete-Groupᵉ Gᵉ Xᵉ xᵉ
  pr2ᵉ (point-classifying-type-quotient-stabilizer-action-Concrete-Groupᵉ xᵉ) =
    refl-mere-equiv-action-Concrete-Groupᵉ Gᵉ
      (action-stabilizer-action-Concrete-Groupᵉ Gᵉ Xᵉ xᵉ)

  classifying-pointed-type-stabilizer-action-Concrete-Groupᵉ :
    (xᵉ : type-action-Concrete-Groupᵉ Gᵉ Xᵉ) →
    Pointed-Typeᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
  pr1ᵉ (classifying-pointed-type-stabilizer-action-Concrete-Groupᵉ xᵉ) =
    classifying-type-quotient-stabilizer-action-Concrete-Groupᵉ xᵉ
  pr2ᵉ (classifying-pointed-type-stabilizer-action-Concrete-Groupᵉ xᵉ) =
    point-classifying-type-quotient-stabilizer-action-Concrete-Groupᵉ xᵉ
```