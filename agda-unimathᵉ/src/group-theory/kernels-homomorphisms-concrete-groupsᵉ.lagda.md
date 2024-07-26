# Kernels of homomorphisms of concrete groups

```agda
module group-theory.kernels-homomorphisms-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.1-typesᵉ
open import foundation.connected-componentsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.setsᵉ
open import foundation.truncated-mapsᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.homomorphisms-concrete-groupsᵉ

open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Theᵉ kernelᵉ ofᵉ aᵉ concreteᵉ groupᵉ homomorphsimᵉ `Bfᵉ : BGᵉ →∗ᵉ BH`ᵉ isᵉ theᵉ connectedᵉ
componentᵉ atᵉ theᵉ baseᵉ pointᵉ ofᵉ theᵉ fiberᵉ ofᵉ `Bf`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Hᵉ : Concrete-Groupᵉ l2ᵉ)
  (fᵉ : hom-Concrete-Groupᵉ Gᵉ Hᵉ)
  where

  classifying-type-kernel-hom-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  classifying-type-kernel-hom-Concrete-Groupᵉ =
    connected-componentᵉ
      ( fiberᵉ
        ( classifying-map-hom-Concrete-Groupᵉ Gᵉ Hᵉ fᵉ)
        ( shape-Concrete-Groupᵉ Hᵉ))
      ( pairᵉ
        ( shape-Concrete-Groupᵉ Gᵉ)
        ( preserves-point-classifying-map-hom-Concrete-Groupᵉ Gᵉ Hᵉ fᵉ))

  shape-kernel-hom-Concrete-Groupᵉ :
    classifying-type-kernel-hom-Concrete-Groupᵉ
  shape-kernel-hom-Concrete-Groupᵉ =
    point-connected-componentᵉ
      ( fiberᵉ
        ( classifying-map-hom-Concrete-Groupᵉ Gᵉ Hᵉ fᵉ)
        ( shape-Concrete-Groupᵉ Hᵉ))
      ( shape-Concrete-Groupᵉ Gᵉ
        ,ᵉ preserves-point-classifying-map-hom-Concrete-Groupᵉ Gᵉ Hᵉ fᵉ)

  classifying-pointed-type-kernel-hom-Concrete-Groupᵉ : Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ classifying-pointed-type-kernel-hom-Concrete-Groupᵉ =
    classifying-type-kernel-hom-Concrete-Groupᵉ
  pr2ᵉ classifying-pointed-type-kernel-hom-Concrete-Groupᵉ =
    shape-kernel-hom-Concrete-Groupᵉ

  is-0-connected-classifying-type-kernel-hom-Concrete-Groupᵉ :
    is-0-connectedᵉ classifying-type-kernel-hom-Concrete-Groupᵉ
  is-0-connected-classifying-type-kernel-hom-Concrete-Groupᵉ =
    is-0-connected-connected-componentᵉ _ _

  is-1-type-classifying-type-kernel-hom-Concrete-Groupᵉ :
    is-1-typeᵉ classifying-type-kernel-hom-Concrete-Groupᵉ
  is-1-type-classifying-type-kernel-hom-Concrete-Groupᵉ =
    is-trunc-connected-componentᵉ _ _
      ( is-trunc-map-is-trunc-domain-codomainᵉ
        ( one-𝕋ᵉ)
        ( is-1-type-classifying-type-Concrete-Groupᵉ Gᵉ)
        ( is-1-type-classifying-type-Concrete-Groupᵉ Hᵉ)
        ( shape-Concrete-Groupᵉ Hᵉ))

  ∞-group-kernel-hom-Concrete-Groupᵉ : ∞-Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ ∞-group-kernel-hom-Concrete-Groupᵉ =
    classifying-pointed-type-kernel-hom-Concrete-Groupᵉ
  pr2ᵉ ∞-group-kernel-hom-Concrete-Groupᵉ =
    is-0-connected-classifying-type-kernel-hom-Concrete-Groupᵉ

  type-kernel-hom-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-kernel-hom-Concrete-Groupᵉ =
    type-∞-Groupᵉ ∞-group-kernel-hom-Concrete-Groupᵉ

  is-set-type-kernel-hom-Concrete-Groupᵉ :
    is-setᵉ type-kernel-hom-Concrete-Groupᵉ
  is-set-type-kernel-hom-Concrete-Groupᵉ =
    is-1-type-classifying-type-kernel-hom-Concrete-Groupᵉ
      shape-kernel-hom-Concrete-Groupᵉ
      shape-kernel-hom-Concrete-Groupᵉ

  concrete-group-kernel-hom-Concrete-Groupᵉ : Concrete-Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ concrete-group-kernel-hom-Concrete-Groupᵉ =
    ∞-group-kernel-hom-Concrete-Groupᵉ
  pr2ᵉ concrete-group-kernel-hom-Concrete-Groupᵉ =
    is-set-type-kernel-hom-Concrete-Groupᵉ
```