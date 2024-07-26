# Telephone numbers

```agda
module elementary-number-theory.telephone-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
```

</details>

## Idea

Theᵉ telephoneᵉ numbersᵉ areᵉ aᵉ sequenceᵉ ofᵉ naturalᵉ numbersᵉ thatᵉ countᵉ theᵉ wayᵉ `n`ᵉ
telephoneᵉ linesᵉ canᵉ beᵉ connectedᵉ to eachᵉ other,ᵉ where eachᵉ lineᵉ canᵉ beᵉ connectedᵉ
to atᵉ mostᵉ oneᵉ otherᵉ line.ᵉ Theyᵉ alsoᵉ occurᵉ in severalᵉ otherᵉ combinatoricsᵉ
problems.ᵉ

## Definitions

```agda
telephone-numberᵉ : ℕᵉ → ℕᵉ
telephone-numberᵉ zero-ℕᵉ = succ-ℕᵉ zero-ℕᵉ
telephone-numberᵉ (succ-ℕᵉ zero-ℕᵉ) = succ-ℕᵉ zero-ℕᵉ
telephone-numberᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) =
  (telephone-numberᵉ (succ-ℕᵉ nᵉ)) +ℕᵉ ((succ-ℕᵉ nᵉ) *ℕᵉ (telephone-numberᵉ nᵉ))
```