# Alternating groups

```agda
module finite-group-theory.alternating-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.sign-homomorphismᵉ

open import group-theory.groupsᵉ
open import group-theory.kernels-homomorphisms-groupsᵉ
open import group-theory.symmetric-groupsᵉ

open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ alternatingᵉ groupᵉ onᵉ aᵉ finiteᵉ setᵉ `X`ᵉ isᵉ theᵉ groupᵉ ofᵉ evenᵉ permutationsᵉ ofᵉ
`X`,ᵉ i.e.ᵉ itᵉ isᵉ theᵉ kernelᵉ ofᵉ theᵉ signᵉ homomorphismᵉ `Aut(Xᵉ) → Aut(2)`.ᵉ

## Definition

```agda
module _
  {lᵉ} (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ nᵉ)
  where
  alternating-Groupᵉ : Groupᵉ lᵉ
  alternating-Groupᵉ = group-kernel-hom-Groupᵉ
    ( symmetric-Groupᵉ (set-UU-Finᵉ nᵉ Xᵉ))
    ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
    ( sign-homomorphismᵉ nᵉ Xᵉ)
```