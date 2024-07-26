# Comprehension of fibered type theories

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module type-theories.comprehension-type-theoriesᵉ where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Givenᵉ aᵉ fiberedᵉ typeᵉ theoryᵉ `S`ᵉ overᵉ `T`,ᵉ weᵉ canᵉ formᵉ theᵉ comprehensionᵉ typeᵉ
theoryᵉ `∫ST`ᵉ analogousᵉ to theᵉ Grothendieckᵉ construction.ᵉ

## Definition

```agda
{-ᵉ
record comprehensionᵉ
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ}
  {Bᵉ : fibered.fibered-type-theoryᵉ l3ᵉ l4ᵉ Aᵉ} : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  where
  coinductiveᵉ
  field
    typeᵉ : {!!ᵉ}
    elementᵉ : {!!ᵉ}
    sliceᵉ : {!!ᵉ}
-ᵉ}
```