# Radical ideals of commutative rings

```agda
module commutative-algebra.radical-ideals-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.ideals-commutative-ringsᵉ
open import commutative-algebra.powers-of-elements-commutative-ringsᵉ
open import commutative-algebra.subsets-commutative-ringsᵉ

open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ idealᵉ `I`ᵉ in aᵉ commutativeᵉ ringᵉ isᵉ saidᵉ to beᵉ **radical**ᵉ ifᵉ forᵉ everyᵉ
elementᵉ `fᵉ : A`ᵉ suchᵉ thatᵉ thereᵉ existsᵉ anᵉ `n`ᵉ suchᵉ thatᵉ `fⁿᵉ ∈ᵉ I`,ᵉ weᵉ haveᵉ
`fᵉ ∈ᵉ I`.ᵉ Inᵉ otherᵉ words,ᵉ radicalᵉ idealsᵉ areᵉ idealsᵉ thatᵉ contain,ᵉ forᵉ everyᵉ
elementᵉ `uᵉ ∈ᵉ I`,ᵉ alsoᵉ theᵉ `n`-thᵉ rootsᵉ ofᵉ `u`ᵉ ifᵉ itᵉ hasᵉ any.ᵉ

## Definitions

### The condition of being a radical ideal

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  is-radical-ideal-prop-Commutative-Ringᵉ :
    (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-radical-ideal-prop-Commutative-Ringᵉ Iᵉ =
    Π-Propᵉ
      ( type-Commutative-Ringᵉ Aᵉ)
      ( λ fᵉ →
        Π-Propᵉ ℕᵉ
          ( λ nᵉ →
            function-Propᵉ
              ( is-in-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (power-Commutative-Ringᵉ Aᵉ nᵉ fᵉ))
              ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ fᵉ)))

  is-radical-ideal-Commutative-Ringᵉ :
    (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-radical-ideal-Commutative-Ringᵉ Iᵉ =
    type-Propᵉ (is-radical-ideal-prop-Commutative-Ringᵉ Iᵉ)

  is-prop-is-radical-ideal-Commutative-Ringᵉ :
    (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    is-propᵉ (is-radical-ideal-Commutative-Ringᵉ Iᵉ)
  is-prop-is-radical-ideal-Commutative-Ringᵉ Iᵉ =
    is-prop-type-Propᵉ (is-radical-ideal-prop-Commutative-Ringᵉ Iᵉ)
```

### Radical ideals

```agda
radical-ideal-Commutative-Ringᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → Commutative-Ringᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ =
  Σᵉ (ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) (is-radical-ideal-Commutative-Ringᵉ Aᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  where

  ideal-radical-ideal-Commutative-Ringᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ
  ideal-radical-ideal-Commutative-Ringᵉ = pr1ᵉ Iᵉ

  is-radical-radical-ideal-Commutative-Ringᵉ :
    is-radical-ideal-Commutative-Ringᵉ Aᵉ ideal-radical-ideal-Commutative-Ringᵉ
  is-radical-radical-ideal-Commutative-Ringᵉ = pr2ᵉ Iᵉ

  subset-radical-ideal-Commutative-Ringᵉ : subset-Commutative-Ringᵉ l2ᵉ Aᵉ
  subset-radical-ideal-Commutative-Ringᵉ =
    subset-ideal-Commutative-Ringᵉ Aᵉ ideal-radical-ideal-Commutative-Ringᵉ

  is-in-radical-ideal-Commutative-Ringᵉ : type-Commutative-Ringᵉ Aᵉ → UUᵉ l2ᵉ
  is-in-radical-ideal-Commutative-Ringᵉ =
    is-in-ideal-Commutative-Ringᵉ Aᵉ ideal-radical-ideal-Commutative-Ringᵉ

  is-closed-under-eq-radical-ideal-Commutative-Ringᵉ :
    {xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ} → is-in-radical-ideal-Commutative-Ringᵉ xᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-radical-ideal-Commutative-Ringᵉ yᵉ
  is-closed-under-eq-radical-ideal-Commutative-Ringᵉ =
    is-closed-under-eq-subset-Commutative-Ringᵉ Aᵉ
      subset-radical-ideal-Commutative-Ringᵉ

  is-closed-under-eq-radical-ideal-Commutative-Ring'ᵉ :
    {xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ} → is-in-radical-ideal-Commutative-Ringᵉ yᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-radical-ideal-Commutative-Ringᵉ xᵉ
  is-closed-under-eq-radical-ideal-Commutative-Ring'ᵉ =
    is-closed-under-eq-subset-Commutative-Ring'ᵉ Aᵉ
      subset-radical-ideal-Commutative-Ringᵉ

  type-radical-ideal-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-radical-ideal-Commutative-Ringᵉ =
    type-ideal-Commutative-Ringᵉ Aᵉ ideal-radical-ideal-Commutative-Ringᵉ

  inclusion-radical-ideal-Commutative-Ringᵉ :
    type-radical-ideal-Commutative-Ringᵉ → type-Commutative-Ringᵉ Aᵉ
  inclusion-radical-ideal-Commutative-Ringᵉ =
    inclusion-ideal-Commutative-Ringᵉ Aᵉ ideal-radical-ideal-Commutative-Ringᵉ

  is-ideal-radical-ideal-Commutative-Ringᵉ :
    is-ideal-subset-Commutative-Ringᵉ Aᵉ subset-radical-ideal-Commutative-Ringᵉ
  is-ideal-radical-ideal-Commutative-Ringᵉ =
    is-ideal-ideal-Commutative-Ringᵉ Aᵉ
      ideal-radical-ideal-Commutative-Ringᵉ

  contains-zero-radical-ideal-Commutative-Ringᵉ :
    is-in-radical-ideal-Commutative-Ringᵉ (zero-Commutative-Ringᵉ Aᵉ)
  contains-zero-radical-ideal-Commutative-Ringᵉ =
    contains-zero-ideal-Commutative-Ringᵉ Aᵉ ideal-radical-ideal-Commutative-Ringᵉ

  is-closed-under-addition-radical-ideal-Commutative-Ringᵉ :
    is-closed-under-addition-subset-Commutative-Ringᵉ Aᵉ
      subset-radical-ideal-Commutative-Ringᵉ
  is-closed-under-addition-radical-ideal-Commutative-Ringᵉ =
    is-closed-under-addition-ideal-Commutative-Ringᵉ Aᵉ
      ideal-radical-ideal-Commutative-Ringᵉ

  is-closed-under-left-multiplication-radical-ideal-Commutative-Ringᵉ :
    is-closed-under-left-multiplication-subset-Commutative-Ringᵉ Aᵉ
      subset-radical-ideal-Commutative-Ringᵉ
  is-closed-under-left-multiplication-radical-ideal-Commutative-Ringᵉ =
    is-closed-under-left-multiplication-ideal-Commutative-Ringᵉ Aᵉ
      ideal-radical-ideal-Commutative-Ringᵉ

  is-closed-under-right-multiplication-radical-ideal-Commutative-Ringᵉ :
    is-closed-under-right-multiplication-subset-Commutative-Ringᵉ Aᵉ
      subset-radical-ideal-Commutative-Ringᵉ
  is-closed-under-right-multiplication-radical-ideal-Commutative-Ringᵉ =
    is-closed-under-right-multiplication-ideal-Commutative-Ringᵉ Aᵉ
      ideal-radical-ideal-Commutative-Ringᵉ

  is-closed-under-powers-radical-ideal-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    is-in-radical-ideal-Commutative-Ringᵉ xᵉ →
    is-in-radical-ideal-Commutative-Ringᵉ (power-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ) xᵉ)
  is-closed-under-powers-radical-ideal-Commutative-Ringᵉ =
    is-closed-under-powers-ideal-Commutative-Ringᵉ Aᵉ
      ideal-radical-ideal-Commutative-Ringᵉ
```

## Properties

### Characterizing equality of radical ideals

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  has-same-elements-radical-ideal-Commutative-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} →
    radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ →
    radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ =
    has-same-elements-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)

  refl-has-same-elements-radical-ideal-Commutative-Ringᵉ :
    {l2ᵉ : Level} (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    has-same-elements-radical-ideal-Commutative-Ringᵉ Iᵉ Iᵉ
  refl-has-same-elements-radical-ideal-Commutative-Ringᵉ Iᵉ =
    refl-has-same-elements-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)

  is-torsorial-has-same-elements-radical-ideal-Commutative-Ringᵉ :
    {l2ᵉ : Level} (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    is-torsorialᵉ
      ( has-same-elements-radical-ideal-Commutative-Ringᵉ Iᵉ)
  is-torsorial-has-same-elements-radical-ideal-Commutative-Ringᵉ Iᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-has-same-elements-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ))
      ( is-prop-is-radical-ideal-Commutative-Ringᵉ Aᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( refl-has-same-elements-radical-ideal-Commutative-Ringᵉ Iᵉ)
      ( is-radical-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)

  has-same-elements-eq-radical-ideal-Commutative-Ringᵉ :
    {l2ᵉ : Level} (Iᵉ Jᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    (Iᵉ ＝ᵉ Jᵉ) → has-same-elements-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ
  has-same-elements-eq-radical-ideal-Commutative-Ringᵉ Iᵉ .Iᵉ reflᵉ =
    refl-has-same-elements-radical-ideal-Commutative-Ringᵉ Iᵉ

  is-equiv-has-same-elements-eq-radical-ideal-Commutative-Ringᵉ :
    {l2ᵉ : Level} (Iᵉ Jᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    is-equivᵉ (has-same-elements-eq-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ)
  is-equiv-has-same-elements-eq-radical-ideal-Commutative-Ringᵉ Iᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-has-same-elements-radical-ideal-Commutative-Ringᵉ Iᵉ)
      ( has-same-elements-eq-radical-ideal-Commutative-Ringᵉ Iᵉ)

  extensionality-radical-ideal-Commutative-Ringᵉ :
    {l2ᵉ : Level} (Iᵉ Jᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    (Iᵉ ＝ᵉ Jᵉ) ≃ᵉ has-same-elements-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ
  pr1ᵉ (extensionality-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ) =
    has-same-elements-eq-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ
  pr2ᵉ (extensionality-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ) =
    is-equiv-has-same-elements-eq-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ

  eq-has-same-elements-radical-ideal-Commutative-Ringᵉ :
    {l2ᵉ : Level} (Iᵉ Jᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    has-same-elements-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ → Iᵉ ＝ᵉ Jᵉ
  eq-has-same-elements-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ =
    map-inv-equivᵉ (extensionality-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ)
```