# Prime ideals of commutative rings

```agda
module commutative-algebra.prime-ideals-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.full-ideals-commutative-ringsᵉ
open import commutative-algebra.ideals-commutative-ringsᵉ
open import commutative-algebra.powers-of-elements-commutative-ringsᵉ
open import commutative-algebra.radical-ideals-commutative-ringsᵉ
open import commutative-algebra.subsets-commutative-ringsᵉ

open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.disjunctionᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Aᵉ **primeᵉ ideal**ᵉ isᵉ anᵉ idealᵉ `I`ᵉ in aᵉ commutativeᵉ ringᵉ `R`ᵉ suchᵉ thatᵉ forᵉ everyᵉ
`a,bᵉ : R`ᵉ wheᵉ haveᵉ `abᵉ ∈ᵉ Iᵉ ⇒ᵉ (aᵉ ∈ᵉ Iᵉ) ∨ᵉ (bᵉ ∈ᵉ I)`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Commutative-Ringᵉ l1ᵉ) (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Rᵉ)
  where

  is-prime-ideal-commutative-ring-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-prime-ideal-commutative-ring-Propᵉ =
    Π-Propᵉ
      ( type-Commutative-Ringᵉ Rᵉ)
      ( λ aᵉ →
        Π-Propᵉ
          ( type-Commutative-Ringᵉ Rᵉ)
          ( λ bᵉ →
            function-Propᵉ
              ( is-in-ideal-Commutative-Ringᵉ Rᵉ Iᵉ (mul-Commutative-Ringᵉ Rᵉ aᵉ bᵉ))
              ( disjunction-Propᵉ
                ( subset-ideal-Commutative-Ringᵉ Rᵉ Iᵉ aᵉ)
                ( subset-ideal-Commutative-Ringᵉ Rᵉ Iᵉ bᵉ))))

  is-prime-ideal-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-prime-ideal-Commutative-Ringᵉ =
    type-Propᵉ is-prime-ideal-commutative-ring-Propᵉ

  is-prop-is-prime-ideal-Commutative-Ringᵉ :
    is-propᵉ is-prime-ideal-Commutative-Ringᵉ
  is-prop-is-prime-ideal-Commutative-Ringᵉ =
    is-prop-type-Propᵉ is-prime-ideal-commutative-ring-Propᵉ

prime-ideal-Commutative-Ringᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → Commutative-Ringᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
prime-ideal-Commutative-Ringᵉ l2ᵉ Rᵉ =
  Σᵉ (ideal-Commutative-Ringᵉ l2ᵉ Rᵉ) (is-prime-ideal-Commutative-Ringᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Commutative-Ringᵉ l1ᵉ)
  (Pᵉ : prime-ideal-Commutative-Ringᵉ l2ᵉ Rᵉ)
  where

  ideal-prime-ideal-Commutative-Ringᵉ : ideal-Commutative-Ringᵉ l2ᵉ Rᵉ
  ideal-prime-ideal-Commutative-Ringᵉ = pr1ᵉ Pᵉ

  is-prime-ideal-ideal-prime-ideal-Commutative-Ringᵉ :
    is-prime-ideal-Commutative-Ringᵉ Rᵉ ideal-prime-ideal-Commutative-Ringᵉ
  is-prime-ideal-ideal-prime-ideal-Commutative-Ringᵉ = pr2ᵉ Pᵉ

  subset-prime-ideal-Commutative-Ringᵉ : subset-Commutative-Ringᵉ l2ᵉ Rᵉ
  subset-prime-ideal-Commutative-Ringᵉ =
    subset-ideal-Commutative-Ringᵉ Rᵉ ideal-prime-ideal-Commutative-Ringᵉ

  is-in-prime-ideal-Commutative-Ringᵉ : type-Commutative-Ringᵉ Rᵉ → UUᵉ l2ᵉ
  is-in-prime-ideal-Commutative-Ringᵉ =
    is-in-ideal-Commutative-Ringᵉ Rᵉ ideal-prime-ideal-Commutative-Ringᵉ

  is-closed-under-eq-prime-ideal-Commutative-Ringᵉ :
    {xᵉ yᵉ : type-Commutative-Ringᵉ Rᵉ} → is-in-prime-ideal-Commutative-Ringᵉ xᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-prime-ideal-Commutative-Ringᵉ yᵉ
  is-closed-under-eq-prime-ideal-Commutative-Ringᵉ =
    is-closed-under-eq-subset-Commutative-Ringᵉ Rᵉ
      subset-prime-ideal-Commutative-Ringᵉ

  is-closed-under-eq-prime-ideal-Commutative-Ring'ᵉ :
    {xᵉ yᵉ : type-Commutative-Ringᵉ Rᵉ} → is-in-prime-ideal-Commutative-Ringᵉ yᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-prime-ideal-Commutative-Ringᵉ xᵉ
  is-closed-under-eq-prime-ideal-Commutative-Ring'ᵉ =
    is-closed-under-eq-subset-Commutative-Ring'ᵉ Rᵉ
      subset-prime-ideal-Commutative-Ringᵉ

  type-prime-ideal-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-prime-ideal-Commutative-Ringᵉ =
    type-ideal-Commutative-Ringᵉ Rᵉ ideal-prime-ideal-Commutative-Ringᵉ

  inclusion-prime-ideal-Commutative-Ringᵉ :
    type-prime-ideal-Commutative-Ringᵉ → type-Commutative-Ringᵉ Rᵉ
  inclusion-prime-ideal-Commutative-Ringᵉ =
    inclusion-subset-Commutative-Ringᵉ Rᵉ subset-prime-ideal-Commutative-Ringᵉ

  is-ideal-prime-ideal-Commutative-Ringᵉ :
    is-ideal-subset-Commutative-Ringᵉ Rᵉ subset-prime-ideal-Commutative-Ringᵉ
  is-ideal-prime-ideal-Commutative-Ringᵉ =
    is-ideal-ideal-Commutative-Ringᵉ Rᵉ ideal-prime-ideal-Commutative-Ringᵉ

  is-additive-subgroup-prime-ideal-Commutative-Ringᵉ :
    is-additive-subgroup-subset-Ringᵉ
      ( ring-Commutative-Ringᵉ Rᵉ)
      ( subset-prime-ideal-Commutative-Ringᵉ)
  is-additive-subgroup-prime-ideal-Commutative-Ringᵉ =
    is-additive-subgroup-ideal-Commutative-Ringᵉ Rᵉ
      ideal-prime-ideal-Commutative-Ringᵉ

  contains-zero-prime-ideal-Commutative-Ringᵉ :
    is-in-prime-ideal-Commutative-Ringᵉ (zero-Commutative-Ringᵉ Rᵉ)
  contains-zero-prime-ideal-Commutative-Ringᵉ =
    contains-zero-ideal-Commutative-Ringᵉ Rᵉ ideal-prime-ideal-Commutative-Ringᵉ

  is-closed-under-addition-prime-ideal-Commutative-Ringᵉ :
    is-closed-under-addition-subset-Commutative-Ringᵉ Rᵉ
      subset-prime-ideal-Commutative-Ringᵉ
  is-closed-under-addition-prime-ideal-Commutative-Ringᵉ =
    is-closed-under-addition-ideal-Commutative-Ringᵉ Rᵉ
      ideal-prime-ideal-Commutative-Ringᵉ

  is-closed-under-left-multiplication-prime-ideal-Commutative-Ringᵉ :
    is-closed-under-left-multiplication-subset-Commutative-Ringᵉ Rᵉ
      subset-prime-ideal-Commutative-Ringᵉ
  is-closed-under-left-multiplication-prime-ideal-Commutative-Ringᵉ =
    is-closed-under-left-multiplication-ideal-Commutative-Ringᵉ Rᵉ
      ideal-prime-ideal-Commutative-Ringᵉ

  is-closed-under-right-multiplication-prime-ideal-Commutative-Ringᵉ :
    is-closed-under-right-multiplication-subset-Commutative-Ringᵉ Rᵉ
      subset-prime-ideal-Commutative-Ringᵉ
  is-closed-under-right-multiplication-prime-ideal-Commutative-Ringᵉ =
    is-closed-under-right-multiplication-ideal-Commutative-Ringᵉ Rᵉ
      ideal-prime-ideal-Commutative-Ringᵉ
```

### Every prime ideal is radical

```agda
is-radical-prime-ideal-Commutative-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ)
  (Pᵉ : prime-ideal-Commutative-Ringᵉ lᵉ Rᵉ) →
  is-radical-ideal-Commutative-Ringᵉ Rᵉ (ideal-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ)
is-radical-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ xᵉ zero-ℕᵉ pᵉ =
  is-full-contains-one-ideal-Commutative-Ringᵉ Rᵉ
    ( ideal-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ)
    ( pᵉ)
    ( xᵉ)
is-radical-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ xᵉ (succ-ℕᵉ nᵉ) pᵉ =
  elim-disjunctionᵉ
    ( subset-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ xᵉ)
    ( is-radical-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ xᵉ nᵉ)
    ( idᵉ)
    ( is-prime-ideal-ideal-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ
      ( power-Commutative-Ringᵉ Rᵉ nᵉ xᵉ)
      ( xᵉ)
      ( is-closed-under-eq-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ pᵉ
        ( power-succ-Commutative-Ringᵉ Rᵉ nᵉ xᵉ)))

radical-ideal-prime-ideal-Commutative-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ)
  (Pᵉ : prime-ideal-Commutative-Ringᵉ lᵉ Rᵉ) →
  radical-ideal-Commutative-Ringᵉ lᵉ Rᵉ
pr1ᵉ (radical-ideal-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ) =
  ideal-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ
pr2ᵉ (radical-ideal-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ) =
  is-radical-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ

is-prime-ideal-radical-ideal-prime-ideal-Commutative-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ)
  (Pᵉ : prime-ideal-Commutative-Ringᵉ lᵉ Rᵉ) →
  is-prime-ideal-Commutative-Ringᵉ Rᵉ
    ( ideal-radical-ideal-Commutative-Ringᵉ Rᵉ
      ( radical-ideal-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ))
is-prime-ideal-radical-ideal-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ = pr2ᵉ Pᵉ

is-in-prime-ideal-is-in-radical-ideal-Commutative-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ)
  (Pᵉ : prime-ideal-Commutative-Ringᵉ lᵉ Rᵉ) (xᵉ : type-Commutative-Ringᵉ Rᵉ) →
  is-in-radical-ideal-Commutative-Ringᵉ Rᵉ
    ( radical-ideal-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ)
    ( xᵉ) →
  is-in-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ xᵉ
is-in-prime-ideal-is-in-radical-ideal-Commutative-Ringᵉ Rᵉ Pᵉ xᵉ pᵉ = pᵉ
```