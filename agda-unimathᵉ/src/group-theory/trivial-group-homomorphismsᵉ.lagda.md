# Trivial group homomorphisms

```agda
module group-theory.trivial-group-homomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
```

</details>

## Idea

Aᵉ **trivialᵉ groupᵉ homomorphism**ᵉ fromᵉ `G`ᵉ to `H`ᵉ isᵉ aᵉ
[groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ) `fᵉ : Gᵉ → H`ᵉ suchᵉ thatᵉ
`fᵉ xᵉ ＝ᵉ 1`ᵉ forᵉ everyᵉ `xᵉ : G`.ᵉ

## Definitions

### The predicate of being a trivial group homomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  is-trivial-prop-hom-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-trivial-prop-hom-Groupᵉ =
    Π-Propᵉ
      ( type-Groupᵉ Gᵉ)
      ( λ xᵉ → Id-Propᵉ (set-Groupᵉ Hᵉ) (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ) (unit-Groupᵉ Hᵉ))

  is-trivial-hom-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-trivial-hom-Groupᵉ = type-Propᵉ is-trivial-prop-hom-Groupᵉ

  is-prop-is-trivial-hom-Groupᵉ : is-propᵉ is-trivial-hom-Groupᵉ
  is-prop-is-trivial-hom-Groupᵉ = is-prop-type-Propᵉ is-trivial-prop-hom-Groupᵉ
```

### The trivial group homomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  where

  trivial-hom-Groupᵉ : hom-Groupᵉ Gᵉ Hᵉ
  pr1ᵉ trivial-hom-Groupᵉ xᵉ = unit-Groupᵉ Hᵉ
  pr2ᵉ trivial-hom-Groupᵉ = invᵉ (left-unit-law-mul-Groupᵉ Hᵉ (unit-Groupᵉ Hᵉ))
```