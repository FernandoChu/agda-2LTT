# The Fibonacci sequence

```agda
module elementary-number-theory.fibonacci-sequenceᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.greatest-common-divisor-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.relatively-prime-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
```

</details>

## Definitions

### The standard definition using pattern matching

```agda
Fibonacci-ℕᵉ : ℕᵉ → ℕᵉ
Fibonacci-ℕᵉ 0 = 0
Fibonacci-ℕᵉ (succ-ℕᵉ 0ᵉ) = 1
Fibonacci-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) = (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)) +ℕᵉ (Fibonacci-ℕᵉ nᵉ)
```

### A definition using the induction principle of `ℕ`

Theᵉ aboveᵉ definitionᵉ ofᵉ theᵉ Fibonacciᵉ sequenceᵉ usesᵉ Agda'sᵉ powerfulᵉ pattern
matchingᵉ definitions.ᵉ Below,ᵉ weᵉ willᵉ giveᵉ aᵉ definitionᵉ ofᵉ theᵉ Fibonacciᵉ sequenceᵉ
in termsᵉ ofᵉ `ind-ℕ`.ᵉ

Theᵉ problemᵉ with definingᵉ theᵉ Fibonacciᵉ sequenceᵉ using `ind-ℕ`,ᵉ isᵉ thatᵉ `ind-ℕ`ᵉ
doesn'tᵉ giveᵉ usᵉ aᵉ wayᵉ to referᵉ to bothᵉ `(Fᵉ n)`ᵉ andᵉ `(Fᵉ (succ-ℕᵉ n))`.ᵉ So,ᵉ weᵉ haveᵉ
to giveᵉ aᵉ workaround,ᵉ where weᵉ storeᵉ twoᵉ valuesᵉ in theᵉ Fibonacciᵉ sequenceᵉ atᵉ
once.ᵉ

Theᵉ basicᵉ ideaᵉ isᵉ thatᵉ weᵉ defineᵉ aᵉ sequenceᵉ ofᵉ pairsᵉ ofᵉ integers,ᵉ whichᵉ willᵉ beᵉ
consecutiveᵉ Fibonacciᵉ numbers.ᵉ Thisᵉ wouldᵉ beᵉ aᵉ functionᵉ ofᵉ typeᵉ $ℕᵉ → ℕ²$.ᵉ

Suchᵉ aᵉ functionᵉ isᵉ easyᵉ to giveᵉ with induction,ᵉ using theᵉ mapᵉ $ℕ²ᵉ → ℕ²$ᵉ thatᵉ
takesᵉ aᵉ pairᵉ `(m,n)`ᵉ to theᵉ pairᵉ `(n,n+m)`.ᵉ Startingᵉ theᵉ iterationᵉ with `(0,1)`ᵉ
weᵉ obtainᵉ theᵉ Fibonacciᵉ sequenceᵉ byᵉ takingᵉ theᵉ firstᵉ projection.ᵉ

However,ᵉ weᵉ haven'tᵉ definedᵉ cartesianᵉ productsᵉ orᵉ booleansᵉ yet.ᵉ Thereforeᵉ weᵉ
mimicᵉ theᵉ aboveᵉ idea,ᵉ using $ℕᵉ → ℕ$ᵉ insteadᵉ ofᵉ $ℕ²$.ᵉ

```agda
shift-oneᵉ : ℕᵉ → (ℕᵉ → ℕᵉ) → (ℕᵉ → ℕᵉ)
shift-oneᵉ nᵉ fᵉ = ind-ℕᵉ nᵉ (λ xᵉ yᵉ → fᵉ xᵉ)

shift-twoᵉ : ℕᵉ → ℕᵉ → (ℕᵉ → ℕᵉ) → (ℕᵉ → ℕᵉ)
shift-twoᵉ mᵉ nᵉ fᵉ = shift-oneᵉ mᵉ (shift-oneᵉ nᵉ fᵉ)

Fibo-zero-ℕᵉ : ℕᵉ → ℕᵉ
Fibo-zero-ℕᵉ = shift-twoᵉ 0 1 (λ xᵉ → 0ᵉ)

Fibo-succ-ℕᵉ : (ℕᵉ → ℕᵉ) → (ℕᵉ → ℕᵉ)
Fibo-succ-ℕᵉ fᵉ = shift-twoᵉ (fᵉ 1ᵉ) ((fᵉ 1ᵉ) +ℕᵉ (fᵉ 0ᵉ)) (λ xᵉ → 0ᵉ)

Fibo-functionᵉ : ℕᵉ → ℕᵉ → ℕᵉ
Fibo-functionᵉ =
  ind-ℕᵉ
    ( Fibo-zero-ℕᵉ)
    ( λ nᵉ → Fibo-succ-ℕᵉ)

Fiboᵉ : ℕᵉ → ℕᵉ
Fiboᵉ kᵉ = Fibo-functionᵉ kᵉ 0
```

## Properties

### `F(m+n+1) ＝ F(m+1)F(n+1) + F(m)F(n)`

```agda
Fibonacci-add-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) →
  Fibonacci-ℕᵉ (mᵉ +ℕᵉ (succ-ℕᵉ nᵉ)) ＝ᵉ
  ( (Fibonacci-ℕᵉ (succ-ℕᵉ mᵉ)) *ℕᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ))) +ℕᵉ
  ( (Fibonacci-ℕᵉ mᵉ) *ℕᵉ (Fibonacci-ℕᵉ nᵉ))
Fibonacci-add-ℕᵉ mᵉ zero-ℕᵉ =
  ap-add-ℕᵉ
    ( invᵉ (right-unit-law-mul-ℕᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ mᵉ))))
    ( invᵉ (right-zero-law-mul-ℕᵉ (Fibonacci-ℕᵉ mᵉ)))
Fibonacci-add-ℕᵉ mᵉ (succ-ℕᵉ nᵉ) =
  ( apᵉ Fibonacci-ℕᵉ (invᵉ (left-successor-law-add-ℕᵉ mᵉ (succ-ℕᵉ nᵉ)))) ∙ᵉ
  ( ( Fibonacci-add-ℕᵉ (succ-ℕᵉ mᵉ) nᵉ) ∙ᵉ
    ( ( apᵉ
        ( _+ℕᵉ ((Fibonacci-ℕᵉ (succ-ℕᵉ mᵉ)) *ℕᵉ (Fibonacci-ℕᵉ nᵉ)))
        ( right-distributive-mul-add-ℕᵉ
          ( Fibonacci-ℕᵉ (succ-ℕᵉ mᵉ))
          ( Fibonacci-ℕᵉ mᵉ)
          ( Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)))) ∙ᵉ
      ( ( associative-add-ℕᵉ
          ( (Fibonacci-ℕᵉ (succ-ℕᵉ mᵉ)) *ℕᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)))
          ( (Fibonacci-ℕᵉ mᵉ) *ℕᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)))
          ( (Fibonacci-ℕᵉ (succ-ℕᵉ mᵉ)) *ℕᵉ (Fibonacci-ℕᵉ nᵉ))) ∙ᵉ
        ( ( apᵉ
            ( ((Fibonacci-ℕᵉ (succ-ℕᵉ mᵉ)) *ℕᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ))) +ℕᵉ_)
            ( commutative-add-ℕᵉ
              ( (Fibonacci-ℕᵉ mᵉ) *ℕᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)))
              ( (Fibonacci-ℕᵉ (succ-ℕᵉ mᵉ)) *ℕᵉ (Fibonacci-ℕᵉ nᵉ)))) ∙ᵉ
          ( ( invᵉ
              ( associative-add-ℕᵉ
                ( (Fibonacci-ℕᵉ (succ-ℕᵉ mᵉ)) *ℕᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)))
                ( (Fibonacci-ℕᵉ (succ-ℕᵉ mᵉ)) *ℕᵉ (Fibonacci-ℕᵉ nᵉ))
                ( (Fibonacci-ℕᵉ mᵉ) *ℕᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ))))) ∙ᵉ
            ( apᵉ
              ( _+ℕᵉ ((Fibonacci-ℕᵉ mᵉ) *ℕᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ))))
              ( invᵉ
                ( left-distributive-mul-add-ℕᵉ
                  ( Fibonacci-ℕᵉ (succ-ℕᵉ mᵉ))
                  ( Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ))
                  ( Fibonacci-ℕᵉ nᵉ)))))))))
```

### Consecutive Fibonacci numbers are relatively prime

```agda
is-one-div-fibonacci-succ-div-fibonacci-ℕᵉ :
  (dᵉ nᵉ : ℕᵉ) → div-ℕᵉ dᵉ (Fibonacci-ℕᵉ nᵉ) → div-ℕᵉ dᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)) →
  is-one-ℕᵉ dᵉ
is-one-div-fibonacci-succ-div-fibonacci-ℕᵉ dᵉ zero-ℕᵉ Hᵉ Kᵉ = is-one-div-one-ℕᵉ dᵉ Kᵉ
is-one-div-fibonacci-succ-div-fibonacci-ℕᵉ dᵉ (succ-ℕᵉ nᵉ) Hᵉ Kᵉ =
  is-one-div-fibonacci-succ-div-fibonacci-ℕᵉ dᵉ nᵉ
    ( div-right-summand-ℕᵉ dᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)) (Fibonacci-ℕᵉ nᵉ) Hᵉ Kᵉ)
    ( Hᵉ)

relatively-prime-fibonacci-fibonacci-succ-ℕᵉ :
  (nᵉ : ℕᵉ) → is-relatively-prime-ℕᵉ (Fibonacci-ℕᵉ nᵉ) (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ))
relatively-prime-fibonacci-fibonacci-succ-ℕᵉ nᵉ =
  is-one-div-fibonacci-succ-div-fibonacci-ℕᵉ
    ( gcd-ℕᵉ (Fibonacci-ℕᵉ nᵉ) (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)))
    ( nᵉ)
    ( div-left-factor-gcd-ℕᵉ (Fibonacci-ℕᵉ nᵉ) (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)))
    ( div-right-factor-gcd-ℕᵉ (Fibonacci-ℕᵉ nᵉ) (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)))
```

### A 3-for-2 property of divisibility of Fibonacci numbers

Weᵉ proveᵉ thatᵉ ifᵉ anᵉ twoᵉ ofᵉ theᵉ followingᵉ threeᵉ propertiesᵉ hold,ᵉ thenᵉ soᵉ doesᵉ theᵉ
thirdᵉ:

1.ᵉ `dᵉ | Fibonacci-ℕᵉ m`ᵉ
2.ᵉ `dᵉ | Fibonacci-ℕᵉ n`ᵉ
3.ᵉ `dᵉ | Fibonacci-ℕᵉ (mᵉ +ℕᵉ n)`.ᵉ

```agda
div-Fibonacci-add-ℕᵉ :
  (dᵉ mᵉ nᵉ : ℕᵉ) → div-ℕᵉ dᵉ (Fibonacci-ℕᵉ mᵉ) → div-ℕᵉ dᵉ (Fibonacci-ℕᵉ nᵉ) →
  div-ℕᵉ dᵉ (Fibonacci-ℕᵉ (mᵉ +ℕᵉ nᵉ))
div-Fibonacci-add-ℕᵉ dᵉ mᵉ zero-ℕᵉ H1ᵉ H2ᵉ = H1ᵉ
div-Fibonacci-add-ℕᵉ dᵉ mᵉ (succ-ℕᵉ nᵉ) H1ᵉ H2ᵉ =
  trᵉ
    ( div-ℕᵉ dᵉ)
    ( invᵉ (Fibonacci-add-ℕᵉ mᵉ nᵉ))
    ( div-add-ℕᵉ dᵉ
      ( (Fibonacci-ℕᵉ (succ-ℕᵉ mᵉ)) *ℕᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)))
      ( (Fibonacci-ℕᵉ mᵉ) *ℕᵉ (Fibonacci-ℕᵉ nᵉ))
      ( div-mul-ℕᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ mᵉ)) dᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)) H2ᵉ)
      ( trᵉ
        ( div-ℕᵉ dᵉ)
        ( commutative-mul-ℕᵉ (Fibonacci-ℕᵉ nᵉ) (Fibonacci-ℕᵉ mᵉ))
        ( div-mul-ℕᵉ (Fibonacci-ℕᵉ nᵉ) dᵉ (Fibonacci-ℕᵉ mᵉ) H1ᵉ)))
```

### If `m | n`, then `d | F(m)` implies `d | F(n)`

```agda
div-Fibonacci-div-ℕᵉ :
  (dᵉ mᵉ nᵉ : ℕᵉ) → div-ℕᵉ mᵉ nᵉ → div-ℕᵉ dᵉ (Fibonacci-ℕᵉ mᵉ) → div-ℕᵉ dᵉ (Fibonacci-ℕᵉ nᵉ)
div-Fibonacci-div-ℕᵉ dᵉ mᵉ .zero-ℕᵉ (zero-ℕᵉ ,ᵉ reflᵉ) Hᵉ = div-zero-ℕᵉ dᵉ
div-Fibonacci-div-ℕᵉ dᵉ zero-ℕᵉ .(kᵉ *ℕᵉ zero-ℕᵉ) (succ-ℕᵉ kᵉ ,ᵉ reflᵉ) Hᵉ =
  trᵉ
    ( div-ℕᵉ dᵉ)
    ( apᵉ Fibonacci-ℕᵉ (invᵉ (right-zero-law-mul-ℕᵉ (succ-ℕᵉ kᵉ))))
    ( div-zero-ℕᵉ dᵉ)
div-Fibonacci-div-ℕᵉ dᵉ (succ-ℕᵉ mᵉ) ._ (succ-ℕᵉ kᵉ ,ᵉ reflᵉ) Hᵉ =
  div-Fibonacci-add-ℕᵉ dᵉ
    ( kᵉ *ℕᵉ (succ-ℕᵉ mᵉ))
    ( succ-ℕᵉ mᵉ)
    ( div-Fibonacci-div-ℕᵉ dᵉ
      ( succ-ℕᵉ mᵉ)
      ( kᵉ *ℕᵉ (succ-ℕᵉ mᵉ))
      ( pairᵉ kᵉ reflᵉ)
      ( Hᵉ))
    ( Hᵉ)
```

### Fibonacci-ℕ is an order preserving map on ℕ ordered by divisibility

```agda
preserves-div-Fibonacci-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) → div-ℕᵉ mᵉ nᵉ → div-ℕᵉ (Fibonacci-ℕᵉ mᵉ) (Fibonacci-ℕᵉ nᵉ)
preserves-div-Fibonacci-ℕᵉ mᵉ nᵉ Hᵉ =
  div-Fibonacci-div-ℕᵉ (Fibonacci-ℕᵉ mᵉ) mᵉ nᵉ Hᵉ (refl-div-ℕᵉ (Fibonacci-ℕᵉ mᵉ))
```