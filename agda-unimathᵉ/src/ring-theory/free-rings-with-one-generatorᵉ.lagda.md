# The free ring with one generator

```agda
module ring-theory.free-rings-with-one-generatorᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ **freeᵉ ringᵉ with oneᵉ generator**ᵉ isᵉ specifiedᵉ asᵉ aᵉ
[ring](ring-theory.rings.mdᵉ) `R`ᵉ equippedᵉ with anᵉ elementᵉ `gᵉ : R`ᵉ suchᵉ thatᵉ forᵉ
everyᵉ ringᵉ `S`ᵉ theᵉ mapᵉ

```text
  hom-set-Ringᵉ Rᵉ Sᵉ → type-Ringᵉ Sᵉ
```

givenᵉ byᵉ evaluatingᵉ atᵉ theᵉ elementᵉ `g`ᵉ isᵉ anᵉ equivalence.ᵉ Thisᵉ propertyᵉ isᵉ alsoᵉ
calledᵉ theᵉ **universalᵉ propertyᵉ ofᵉ theᵉ freeᵉ ringᵉ with oneᵉ generator**.ᵉ Inᵉ otherᵉ
words,ᵉ theᵉ freeᵉ ringᵉ with oneᵉ generatorᵉ isᵉ aᵉ representingᵉ objectᵉ forᵉ theᵉ functorᵉ
`Sᵉ ↦ᵉ type-Ringᵉ S`.ᵉ

Weᵉ willᵉ showᵉ thatᵉ theᵉ polynomialᵉ ringᵉ `ℤ[x]`ᵉ ofᵉ polynomialsᵉ with
[integer](elementary-number-theory.ring-of-integers.mdᵉ) coefficientsᵉ satisfiesᵉ
theᵉ universalᵉ propertyᵉ ofᵉ theᵉ freeᵉ ringᵉ with oneᵉ generator.ᵉ

## Definitions

### The universal property of the free ring with one generator

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (gᵉ : type-Ringᵉ Rᵉ)
  where

  is-free-ring-with-one-generatorᵉ : UUωᵉ
  is-free-ring-with-one-generatorᵉ =
    {l2ᵉ : Level} (Sᵉ : Ringᵉ l2ᵉ) → is-equivᵉ (ev-element-hom-Ringᵉ Rᵉ Sᵉ gᵉ)
```