# Group actions

```agda
module group-theory.group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.symmetric-groupsᵉ
open import group-theory.trivial-group-homomorphismsᵉ
```

</details>

## Idea

Anᵉ **action**ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ onᵉ aᵉ
[set](foundation-core.sets.mdᵉ) `X`,ᵉ alsoᵉ calledᵉ aᵉ **`G`-action**,ᵉ isᵉ aᵉ
[groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ) fromᵉ `G`ᵉ intoᵉ
`symmetric-Groupᵉ X`.ᵉ Aᵉ setᵉ equippedᵉ with aᵉ `G`-actionᵉ isᵉ calledᵉ aᵉ **`G`-set**.ᵉ

## Definitions

### The type of `G`-sets

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  action-Groupᵉ : (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
  action-Groupᵉ lᵉ =
    Σᵉ (Setᵉ lᵉ) (λ Xᵉ → hom-Groupᵉ Gᵉ (symmetric-Groupᵉ Xᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ)
  where

  set-action-Groupᵉ : Setᵉ l2ᵉ
  set-action-Groupᵉ = pr1ᵉ Xᵉ

  type-action-Groupᵉ : UUᵉ l2ᵉ
  type-action-Groupᵉ = type-Setᵉ set-action-Groupᵉ

  is-set-type-action-Groupᵉ : is-setᵉ type-action-Groupᵉ
  is-set-type-action-Groupᵉ = is-set-type-Setᵉ set-action-Groupᵉ

  equiv-mul-action-Groupᵉ : type-Groupᵉ Gᵉ → type-action-Groupᵉ ≃ᵉ type-action-Groupᵉ
  equiv-mul-action-Groupᵉ =
    map-hom-Groupᵉ Gᵉ (symmetric-Groupᵉ set-action-Groupᵉ) (pr2ᵉ Xᵉ)

  mul-action-Groupᵉ : type-Groupᵉ Gᵉ → type-action-Groupᵉ → type-action-Groupᵉ
  mul-action-Groupᵉ gᵉ = map-equivᵉ (equiv-mul-action-Groupᵉ gᵉ)

  mul-action-Group'ᵉ : type-action-Groupᵉ → type-Groupᵉ Gᵉ → type-action-Groupᵉ
  mul-action-Group'ᵉ xᵉ gᵉ = mul-action-Groupᵉ gᵉ xᵉ

  preserves-unit-mul-action-Groupᵉ : mul-action-Groupᵉ (unit-Groupᵉ Gᵉ) ~ᵉ idᵉ
  preserves-unit-mul-action-Groupᵉ =
    htpy-eqᵉ
      ( apᵉ pr1ᵉ
        ( preserves-unit-hom-Groupᵉ Gᵉ
          ( symmetric-Groupᵉ set-action-Groupᵉ)
          ( pr2ᵉ Xᵉ)))

  preserves-mul-action-Groupᵉ :
    (gᵉ : type-Groupᵉ Gᵉ) (hᵉ : type-Groupᵉ Gᵉ) (xᵉ : type-action-Groupᵉ) →
    mul-action-Groupᵉ (mul-Groupᵉ Gᵉ gᵉ hᵉ) xᵉ ＝ᵉ
    mul-action-Groupᵉ gᵉ (mul-action-Groupᵉ hᵉ xᵉ)
  preserves-mul-action-Groupᵉ gᵉ hᵉ =
    htpy-eqᵉ
      ( apᵉ pr1ᵉ
        ( preserves-mul-hom-Groupᵉ Gᵉ (symmetric-Groupᵉ set-action-Groupᵉ) (pr2ᵉ Xᵉ)))

  transpose-eq-mul-action-Groupᵉ :
    (gᵉ : type-Groupᵉ Gᵉ) (xᵉ yᵉ : type-action-Groupᵉ) →
    mul-action-Groupᵉ gᵉ xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ mul-action-Groupᵉ (inv-Groupᵉ Gᵉ gᵉ) yᵉ
  transpose-eq-mul-action-Groupᵉ gᵉ xᵉ ._ reflᵉ =
    ( invᵉ
      ( ( apᵉ (mul-action-Group'ᵉ xᵉ) (left-inverse-law-mul-Groupᵉ Gᵉ gᵉ)) ∙ᵉ
        ( preserves-unit-mul-action-Groupᵉ xᵉ))) ∙ᵉ
    ( preserves-mul-action-Groupᵉ (inv-Groupᵉ Gᵉ gᵉ) gᵉ xᵉ)
```

## Examples

### Trivial `G`-sets

Everyᵉ setᵉ givesᵉ riseᵉ to aᵉ `G`-setᵉ byᵉ havingᵉ everyᵉ pointᵉ fixedᵉ underᵉ theᵉ actionᵉ
ofᵉ `G`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : Setᵉ l2ᵉ)
  where

  trivial-action-Groupᵉ : action-Groupᵉ Gᵉ l2ᵉ
  pr1ᵉ trivial-action-Groupᵉ = Xᵉ
  pr2ᵉ trivial-action-Groupᵉ = trivial-hom-Groupᵉ Gᵉ (symmetric-Groupᵉ Xᵉ)
```

## External links

-ᵉ [Groupᵉ action](https://en.wikipedia.org/wiki/Group_actionᵉ) atᵉ Wikipediaᵉ
-ᵉ [Actionsᵉ ofᵉ aᵉ group](https://ncatlab.org/nlab/show/action#ActionsOfAGroupᵉ) atᵉ
  $n$Labᵉ
-ᵉ [Groupᵉ Action](https://mathworld.wolfram.com/GroupAction.htmlᵉ) atᵉ Wolframᵉ
  MathWorldᵉ