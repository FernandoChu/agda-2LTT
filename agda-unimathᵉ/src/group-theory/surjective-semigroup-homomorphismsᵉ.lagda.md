# Surjective semigroup homomorphisms

```agda
module group-theory.surjective-semigroup-homomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.full-subsemigroupsᵉ
open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.images-of-semigroup-homomorphismsᵉ
open import group-theory.semigroupsᵉ
```

</details>

Aᵉ [semigroupᵉ homomorphism](group-theory.homomorphisms-semigroups.mdᵉ) `fᵉ : Gᵉ → H`ᵉ
isᵉ saidᵉ to beᵉ **surjective**ᵉ ifᵉ itsᵉ underlyingᵉ mapᵉ isᵉ
[surjective](foundation.surjective-maps.md).ᵉ

## Definition

### Surjective semigroup homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ) (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ)
  where

  is-surjective-prop-hom-Semigroupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-surjective-prop-hom-Semigroupᵉ =
    is-surjective-Propᵉ (map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)

  is-surjective-hom-Semigroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-surjective-hom-Semigroupᵉ = type-Propᵉ is-surjective-prop-hom-Semigroupᵉ

  is-prop-is-surjective-hom-Semigroupᵉ : is-propᵉ is-surjective-hom-Semigroupᵉ
  is-prop-is-surjective-hom-Semigroupᵉ =
    is-prop-type-Propᵉ is-surjective-prop-hom-Semigroupᵉ
```

## Properties

### A semigroup homomorphism is surjective if and only if its image is the full subsemigroup

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ) (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ)
  where

  is-surjective-is-full-subsemigroup-image-hom-Semigroupᵉ :
    is-full-Subsemigroupᵉ Hᵉ (image-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ) →
    is-surjective-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ
  is-surjective-is-full-subsemigroup-image-hom-Semigroupᵉ uᵉ = uᵉ

  is-full-subsemigroup-image-is-surjective-hom-Semigroupᵉ :
    is-surjective-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ →
    is-full-Subsemigroupᵉ Hᵉ (image-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)
  is-full-subsemigroup-image-is-surjective-hom-Semigroupᵉ uᵉ = uᵉ
```