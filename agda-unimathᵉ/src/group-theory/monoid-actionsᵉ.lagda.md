# Monoid actions

```agda
module group-theory.monoid-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.endomorphismsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-monoidsᵉ
open import group-theory.monoidsᵉ
```

</details>

## Idea

Aᵉ **monoidᵉ action**ᵉ ofᵉ aᵉ [monoid](group-theory.monoids.mdᵉ) `M`ᵉ onᵉ aᵉ
[set](foundation-core.sets.mdᵉ) `X`ᵉ isᵉ aᵉ
[monoidᵉ homomorphism](group-theory.homomorphisms-monoids.mdᵉ) fromᵉ `M`ᵉ intoᵉ theᵉ
monoidᵉ ofᵉ [endomorphisms](foundation.endomorphisms.mdᵉ) `Xᵉ → X`.ᵉ Theᵉ factᵉ thatᵉ
monoidᵉ homomorphismsᵉ preserveᵉ theᵉ monoidᵉ operationᵉ andᵉ theᵉ unitᵉ impliesᵉ thatᵉ aᵉ
monoidᵉ actionᵉ `μ`ᵉ ofᵉ `M`ᵉ onᵉ `X`ᵉ satisfiesᵉ theᵉ followingᵉ lawsᵉ:

```text
  μᵉ mnᵉ xᵉ ＝ᵉ μᵉ mᵉ (μᵉ nᵉ xᵉ)
   μᵉ 1 xᵉ ＝ᵉ x.ᵉ
```

## Definition

### Monoid actions

```agda
action-Monoidᵉ : {l1ᵉ : Level} (lᵉ : Level) (Mᵉ : Monoidᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
action-Monoidᵉ lᵉ Mᵉ = Σᵉ (Setᵉ lᵉ) (λ Xᵉ → hom-Monoidᵉ Mᵉ (endo-Monoidᵉ Xᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Xᵉ : action-Monoidᵉ l2ᵉ Mᵉ)
  where

  set-action-Monoidᵉ : Setᵉ l2ᵉ
  set-action-Monoidᵉ = pr1ᵉ Xᵉ

  type-action-Monoidᵉ : UUᵉ l2ᵉ
  type-action-Monoidᵉ = type-Setᵉ set-action-Monoidᵉ

  is-set-type-action-Monoidᵉ : is-setᵉ type-action-Monoidᵉ
  is-set-type-action-Monoidᵉ = is-set-type-Setᵉ set-action-Monoidᵉ

  mul-hom-monoid-action-Monoidᵉ : hom-Monoidᵉ Mᵉ (endo-Monoidᵉ set-action-Monoidᵉ)
  mul-hom-monoid-action-Monoidᵉ = pr2ᵉ Xᵉ

  mul-action-Monoidᵉ : type-Monoidᵉ Mᵉ → type-action-Monoidᵉ → type-action-Monoidᵉ
  mul-action-Monoidᵉ =
    map-hom-Monoidᵉ Mᵉ
      ( endo-Monoidᵉ set-action-Monoidᵉ)
      ( mul-hom-monoid-action-Monoidᵉ)

  ap-mul-action-Monoidᵉ :
    {mᵉ : type-Monoidᵉ Mᵉ} {xᵉ yᵉ : type-action-Monoidᵉ} →
    xᵉ ＝ᵉ yᵉ → mul-action-Monoidᵉ mᵉ xᵉ ＝ᵉ mul-action-Monoidᵉ mᵉ yᵉ
  ap-mul-action-Monoidᵉ {mᵉ} = apᵉ (mul-action-Monoidᵉ mᵉ)

  ap-mul-action-Monoid'ᵉ :
    {mᵉ nᵉ : type-Monoidᵉ Mᵉ} (pᵉ : mᵉ ＝ᵉ nᵉ) {xᵉ : type-action-Monoidᵉ} →
    mul-action-Monoidᵉ mᵉ xᵉ ＝ᵉ mul-action-Monoidᵉ nᵉ xᵉ
  ap-mul-action-Monoid'ᵉ pᵉ {xᵉ} = apᵉ (λ tᵉ → mul-action-Monoidᵉ tᵉ xᵉ) pᵉ

  associative-mul-action-Monoidᵉ :
    (xᵉ yᵉ : type-Monoidᵉ Mᵉ) (zᵉ : type-action-Monoidᵉ) →
    mul-action-Monoidᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-action-Monoidᵉ xᵉ (mul-action-Monoidᵉ yᵉ zᵉ)
  associative-mul-action-Monoidᵉ xᵉ yᵉ =
    htpy-eqᵉ
      ( preserves-mul-hom-Monoidᵉ Mᵉ
        ( endo-Monoidᵉ set-action-Monoidᵉ)
        ( mul-hom-monoid-action-Monoidᵉ))

  unit-law-mul-action-Monoidᵉ :
    (xᵉ : type-action-Monoidᵉ) → mul-action-Monoidᵉ (unit-Monoidᵉ Mᵉ) xᵉ ＝ᵉ xᵉ
  unit-law-mul-action-Monoidᵉ =
    htpy-eqᵉ
      ( preserves-unit-hom-Monoidᵉ Mᵉ
        ( endo-Monoidᵉ set-action-Monoidᵉ)
        ( mul-hom-monoid-action-Monoidᵉ))
```