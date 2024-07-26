# Surjective group homomorphisms

```agda
module group-theory.surjective-group-homomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.full-subgroupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.images-of-group-homomorphismsᵉ
open import group-theory.surjective-semigroup-homomorphismsᵉ
```

</details>

Aᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ) `fᵉ : Gᵉ → H`ᵉ isᵉ saidᵉ
to beᵉ **surjective**ᵉ ifᵉ itsᵉ underlyingᵉ mapᵉ isᵉ
[surjective](foundation.surjective-maps.md).ᵉ

## Definition

### Surjective group homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  is-surjective-prop-hom-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-surjective-prop-hom-Groupᵉ =
    is-surjective-prop-hom-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)

  is-surjective-hom-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-surjective-hom-Groupᵉ =
    is-surjective-hom-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)

  is-prop-is-surjective-hom-Groupᵉ : is-propᵉ is-surjective-hom-Groupᵉ
  is-prop-is-surjective-hom-Groupᵉ =
    is-prop-is-surjective-hom-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)
```

## Properties

### A group homomorphism is surjective if and only if its image is the full subgroup

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  is-surjective-is-full-subgroup-image-hom-Groupᵉ :
    is-full-Subgroupᵉ Hᵉ (image-hom-Groupᵉ Gᵉ Hᵉ fᵉ) →
    is-surjective-hom-Groupᵉ Gᵉ Hᵉ fᵉ
  is-surjective-is-full-subgroup-image-hom-Groupᵉ uᵉ = uᵉ

  is-full-subgroup-image-is-surjective-hom-Groupᵉ :
    is-surjective-hom-Groupᵉ Gᵉ Hᵉ fᵉ →
    is-full-Subgroupᵉ Hᵉ (image-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
  is-full-subgroup-image-is-surjective-hom-Groupᵉ uᵉ = uᵉ
```