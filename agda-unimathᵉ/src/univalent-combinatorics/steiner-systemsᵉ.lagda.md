# Steiner systems

```agda
module univalent-combinatorics.steiner-systemsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.contractible-typesᵉ
open import foundation.decidable-subtypesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ Steinerᵉ systemᵉ ofᵉ typeᵉ `(t,k,nᵉ) : ℕ³`ᵉ consistsᵉ ofᵉ anᵉ `n`-elementᵉ typeᵉ `X`ᵉ
equippedᵉ with aᵉ (decidableᵉ) setᵉ `P`ᵉ ofᵉ `k`-elementᵉ subtypesᵉ ofᵉ `X`ᵉ suchᵉ thatᵉ
eachᵉ `t`-elementᵉ subtypeᵉ ofᵉ `X`ᵉ isᵉ containedᵉ in exactlyᵉ oneᵉ `k`-elementᵉ subtypeᵉ
in `P`.ᵉ Aᵉ basicᵉ exampleᵉ isᵉ theᵉ Fanoᵉ plane,ᵉ whichᵉ isᵉ aᵉ Steinerᵉ systemᵉ ofᵉ typeᵉ
`(2,3,7)`.ᵉ

## Definition

### Steiner systems

```agda
Steiner-Systemᵉ : ℕᵉ → ℕᵉ → ℕᵉ → UUᵉ (lsuc lzero)
Steiner-Systemᵉ tᵉ kᵉ nᵉ =
  Σᵉ ( UU-Finᵉ lzero nᵉ)
    ( λ Xᵉ →
      Σᵉ ( decidable-subtypeᵉ lzero
          ( Σᵉ ( decidable-subtypeᵉ lzero (type-UU-Finᵉ nᵉ Xᵉ))
              ( λ Pᵉ → has-cardinalityᵉ kᵉ (type-decidable-subtypeᵉ Pᵉ))))
        ( λ Pᵉ →
          ( Qᵉ : decidable-subtypeᵉ lzero (type-UU-Finᵉ nᵉ Xᵉ)) →
          has-cardinalityᵉ tᵉ (type-decidable-subtypeᵉ Qᵉ) →
          is-contrᵉ
            ( Σᵉ ( type-decidable-subtypeᵉ Pᵉ)
                ( λ Uᵉ →
                  (xᵉ : type-UU-Finᵉ nᵉ Xᵉ) →
                  is-in-decidable-subtypeᵉ Qᵉ xᵉ →
                  is-in-decidable-subtypeᵉ (pr1ᵉ (pr1ᵉ Uᵉ)) xᵉ))))
```