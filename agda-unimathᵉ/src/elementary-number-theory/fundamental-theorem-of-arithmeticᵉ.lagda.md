# The fundamental theorem of arithmetic

```agda
module elementary-number-theory.fundamental-theorem-of-arithmeticᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-strong-induction-natural-numbersᵉ
open import elementary-number-theory.bezouts-lemma-integersᵉ
open import elementary-number-theory.decidable-total-order-natural-numbersᵉ
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.lower-bounds-natural-numbersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.multiplication-lists-of-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.prime-numbersᵉ
open import elementary-number-theory.relatively-prime-natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ
open import elementary-number-theory.well-ordering-principle-natural-numbersᵉ

open import finite-group-theory.permutations-standard-finite-typesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import lists.concatenation-listsᵉ
open import lists.functoriality-listsᵉ
open import lists.listsᵉ
open import lists.permutation-listsᵉ
open import lists.predicates-on-listsᵉ
open import lists.sort-by-insertion-listsᵉ
open import lists.sorted-listsᵉ
```

</details>

## Idea

Theᵉ **fundamentalᵉ theoremᵉ ofᵉ arithmetic**ᵉ assertsᵉ thatᵉ everyᵉ nonzeroᵉ naturalᵉ
numberᵉ canᵉ beᵉ writtenᵉ asᵉ aᵉ productᵉ ofᵉ primes,ᵉ andᵉ thisᵉ productᵉ isᵉ uniqueᵉ upᵉ to
theᵉ orderᵉ ofᵉ theᵉ factors.ᵉ

Theᵉ uniquenessᵉ ofᵉ theᵉ primeᵉ factorizationᵉ ofᵉ aᵉ naturalᵉ numberᵉ canᵉ beᵉ expressedᵉ
in severalᵉ waysᵉ:

-ᵉ Weᵉ canᵉ findᵉ aᵉ uniqueᵉ listᵉ ofᵉ primesᵉ `p₁ᵉ ≤ᵉ p₂ᵉ ≤ᵉ ⋯ᵉ ≤ᵉ pᵢ`ᵉ ofᵉ whichᵉ theᵉ productᵉ isᵉ
  equalᵉ to `n`ᵉ
-ᵉ Theᵉ typeᵉ ofᵉ finiteᵉ setsᵉ `X`ᵉ equippedᵉ with functionsᵉ `pᵉ : Xᵉ → Σᵉ ℕᵉ is-prime-ℕ`ᵉ
  andᵉ `mᵉ : Xᵉ → positive-ℕ`ᵉ suchᵉ thatᵉ theᵉ productᵉ ofᵉ `pₓᵐ⁽ˣ⁾`ᵉ isᵉ equalᵉ to `n`ᵉ isᵉ
  contractible.ᵉ

Noteᵉ thatᵉ theᵉ univalenceᵉ axiomᵉ isᵉ neccessaryᵉ to proveᵉ theᵉ secondᵉ uniquenessᵉ
propertyᵉ ofᵉ primeᵉ factorizations.ᵉ

## Definitions

### Prime decomposition of a natural number with lists

Aᵉ listᵉ ofᵉ naturalᵉ numbersᵉ isᵉ aᵉ primeᵉ decompositionᵉ ofᵉ aᵉ naturalᵉ numberᵉ `n`ᵉ ifᵉ :

-ᵉ Theᵉ listᵉ isᵉ sortedᵉ
-ᵉ Everyᵉ elementᵉ ofᵉ theᵉ listᵉ isᵉ prime.ᵉ
-ᵉ Theᵉ productᵉ ofᵉ theᵉ elementᵉ ofᵉ theᵉ listᵉ isᵉ equalᵉ to `n`ᵉ

```agda
is-prime-list-ℕᵉ :
  listᵉ ℕᵉ → UUᵉ lzero
is-prime-list-ℕᵉ = for-all-listᵉ ℕᵉ is-prime-ℕ-Propᵉ

is-prop-is-prime-list-ℕᵉ :
  (lᵉ : listᵉ ℕᵉ) → is-propᵉ (is-prime-list-ℕᵉ lᵉ)
is-prop-is-prime-list-ℕᵉ = is-prop-for-all-listᵉ ℕᵉ is-prime-ℕ-Propᵉ

is-prime-list-primes-ℕᵉ :
  (lᵉ : listᵉ Prime-ℕᵉ) → is-prime-list-ℕᵉ (map-listᵉ nat-Prime-ℕᵉ lᵉ)
is-prime-list-primes-ℕᵉ nilᵉ = raise-starᵉ
is-prime-list-primes-ℕᵉ (consᵉ xᵉ lᵉ) =
  (is-prime-Prime-ℕᵉ xᵉ) ,ᵉ (is-prime-list-primes-ℕᵉ lᵉ)

module _
  (xᵉ : ℕᵉ)
  (lᵉ : listᵉ ℕᵉ)
  where

  is-decomposition-list-ℕᵉ :
    UUᵉ lzero
  is-decomposition-list-ℕᵉ =
    mul-list-ℕᵉ lᵉ ＝ᵉ xᵉ

  is-prop-is-decomposition-list-ℕᵉ :
    is-propᵉ (is-decomposition-list-ℕᵉ)
  is-prop-is-decomposition-list-ℕᵉ = is-set-ℕᵉ (mul-list-ℕᵉ lᵉ) xᵉ

  is-prime-decomposition-list-ℕᵉ :
    UUᵉ lzero
  is-prime-decomposition-list-ℕᵉ =
    is-sorted-listᵉ ℕ-Decidable-Total-Orderᵉ lᵉ ×ᵉ
    ( is-prime-list-ℕᵉ lᵉ ×ᵉ
      is-decomposition-list-ℕᵉ)

  is-sorted-list-is-prime-decomposition-list-ℕᵉ :
    is-prime-decomposition-list-ℕᵉ →
    is-sorted-listᵉ ℕ-Decidable-Total-Orderᵉ lᵉ
  is-sorted-list-is-prime-decomposition-list-ℕᵉ Dᵉ = pr1ᵉ Dᵉ

  is-prime-list-is-prime-decomposition-list-ℕᵉ :
    is-prime-decomposition-list-ℕᵉ →
    is-prime-list-ℕᵉ lᵉ
  is-prime-list-is-prime-decomposition-list-ℕᵉ Dᵉ =
    pr1ᵉ (pr2ᵉ Dᵉ)

  is-decomposition-list-is-prime-decomposition-list-ℕᵉ :
    is-prime-decomposition-list-ℕᵉ →
    is-decomposition-list-ℕᵉ
  is-decomposition-list-is-prime-decomposition-list-ℕᵉ Dᵉ =
    pr2ᵉ (pr2ᵉ Dᵉ)

  is-prop-is-prime-decomposition-list-ℕᵉ :
    is-propᵉ (is-prime-decomposition-list-ℕᵉ)
  is-prop-is-prime-decomposition-list-ℕᵉ =
    is-prop-productᵉ
      ( is-prop-is-sorted-listᵉ ℕ-Decidable-Total-Orderᵉ lᵉ)
      ( is-prop-productᵉ
        ( is-prop-is-prime-list-ℕᵉ lᵉ)
        ( is-prop-is-decomposition-list-ℕᵉ))

  is-prime-decomposition-list-ℕ-Propᵉ : Propᵉ lzero
  pr1ᵉ is-prime-decomposition-list-ℕ-Propᵉ = is-prime-decomposition-list-ℕᵉ
  pr2ᵉ is-prime-decomposition-list-ℕ-Propᵉ = is-prop-is-prime-decomposition-list-ℕᵉ
```

### Nontrivial divisors

Nontrivialᵉ divisorsᵉ ofᵉ aᵉ naturalᵉ numberᵉ areᵉ divisorsᵉ strictlyᵉ greaterᵉ thanᵉ `1`.ᵉ

```agda
is-nontrivial-divisor-ℕᵉ : (nᵉ xᵉ : ℕᵉ) → UUᵉ lzero
is-nontrivial-divisor-ℕᵉ nᵉ xᵉ = (le-ℕᵉ 1 xᵉ) ×ᵉ (div-ℕᵉ xᵉ nᵉ)

is-prop-is-nontrivial-divisor-ℕᵉ :
  (nᵉ xᵉ : ℕᵉ) → is-propᵉ (is-nontrivial-divisor-ℕᵉ nᵉ xᵉ)
is-prop-is-nontrivial-divisor-ℕᵉ nᵉ xᵉ =
  is-prop-Σᵉ
    ( is-prop-le-ℕᵉ 1 xᵉ)
    ( λ pᵉ → is-prop-div-ℕᵉ xᵉ nᵉ (is-nonzero-le-ℕᵉ 1 xᵉ pᵉ))

is-nontrivial-divisor-ℕ-Propᵉ : (nᵉ xᵉ : ℕᵉ) → Propᵉ lzero
pr1ᵉ (is-nontrivial-divisor-ℕ-Propᵉ nᵉ xᵉ) = is-nontrivial-divisor-ℕᵉ nᵉ xᵉ
pr2ᵉ (is-nontrivial-divisor-ℕ-Propᵉ nᵉ xᵉ) = is-prop-is-nontrivial-divisor-ℕᵉ nᵉ xᵉ

is-decidable-is-nontrivial-divisor-ℕᵉ :
  (nᵉ xᵉ : ℕᵉ) → is-decidableᵉ (is-nontrivial-divisor-ℕᵉ nᵉ xᵉ)
is-decidable-is-nontrivial-divisor-ℕᵉ nᵉ xᵉ =
  is-decidable-productᵉ (is-decidable-le-ℕᵉ 1 xᵉ) (is-decidable-div-ℕᵉ xᵉ nᵉ)

is-nontrivial-divisor-diagonal-ℕᵉ :
  (nᵉ : ℕᵉ) → le-ℕᵉ 1 nᵉ → is-nontrivial-divisor-ℕᵉ nᵉ nᵉ
pr1ᵉ (is-nontrivial-divisor-diagonal-ℕᵉ nᵉ Hᵉ) = Hᵉ
pr2ᵉ (is-nontrivial-divisor-diagonal-ℕᵉ nᵉ Hᵉ) = refl-div-ℕᵉ nᵉ
```

Ifᵉ `l`ᵉ isᵉ aᵉ primeᵉ decompositionᵉ ofᵉ `n`,ᵉ thenᵉ `l`ᵉ isᵉ aᵉ listᵉ ofᵉ nontrivialᵉ
divisorsᵉ ofᵉ `n`.ᵉ

```agda
is-list-of-nontrivial-divisors-ℕᵉ :
  ℕᵉ → listᵉ ℕᵉ → UUᵉ lzero
is-list-of-nontrivial-divisors-ℕᵉ xᵉ nilᵉ = unitᵉ
is-list-of-nontrivial-divisors-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) =
  (is-nontrivial-divisor-ℕᵉ xᵉ yᵉ) ×ᵉ (is-list-of-nontrivial-divisors-ℕᵉ xᵉ lᵉ)

is-nontrivial-divisors-div-list-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → div-ℕᵉ xᵉ yᵉ → (lᵉ : listᵉ ℕᵉ) →
  is-list-of-nontrivial-divisors-ℕᵉ xᵉ lᵉ → is-list-of-nontrivial-divisors-ℕᵉ yᵉ lᵉ
is-nontrivial-divisors-div-list-ℕᵉ xᵉ yᵉ dᵉ nilᵉ Hᵉ = starᵉ
is-nontrivial-divisors-div-list-ℕᵉ xᵉ yᵉ dᵉ (consᵉ zᵉ lᵉ) Hᵉ =
  ( pr1ᵉ (pr1ᵉ Hᵉ) ,ᵉ transitive-div-ℕᵉ zᵉ xᵉ yᵉ dᵉ (pr2ᵉ (pr1ᵉ Hᵉ))) ,ᵉ
  is-nontrivial-divisors-div-list-ℕᵉ xᵉ yᵉ dᵉ lᵉ (pr2ᵉ Hᵉ)

is-divisor-head-is-decomposition-list-ℕᵉ :
  (xᵉ : ℕᵉ) (yᵉ : ℕᵉ) (lᵉ : listᵉ ℕᵉ) →
  is-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) →
  div-ℕᵉ yᵉ xᵉ
pr1ᵉ (is-divisor-head-is-decomposition-list-ℕᵉ xᵉ yᵉ lᵉ Dᵉ) =
  mul-list-ℕᵉ lᵉ
pr2ᵉ (is-divisor-head-is-decomposition-list-ℕᵉ xᵉ yᵉ lᵉ Dᵉ) =
  commutative-mul-ℕᵉ (mul-list-ℕᵉ lᵉ) yᵉ ∙ᵉ Dᵉ

is-nontrivial-divisor-head-is-decomposition-is-prime-list-ℕᵉ :
  (xᵉ : ℕᵉ) (yᵉ : ℕᵉ) (lᵉ : listᵉ ℕᵉ) →
  is-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) →
  is-prime-list-ℕᵉ (consᵉ yᵉ lᵉ) →
  is-nontrivial-divisor-ℕᵉ xᵉ yᵉ
pr1ᵉ (is-nontrivial-divisor-head-is-decomposition-is-prime-list-ℕᵉ xᵉ yᵉ lᵉ Dᵉ Pᵉ) =
  le-one-is-prime-ℕᵉ yᵉ (pr1ᵉ Pᵉ)
pr2ᵉ (is-nontrivial-divisor-head-is-decomposition-is-prime-list-ℕᵉ xᵉ yᵉ lᵉ Dᵉ Pᵉ) =
  is-divisor-head-is-decomposition-list-ℕᵉ xᵉ yᵉ lᵉ Dᵉ

is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕᵉ :
  (xᵉ : ℕᵉ) → (lᵉ : listᵉ ℕᵉ) →
  is-decomposition-list-ℕᵉ xᵉ lᵉ →
  is-prime-list-ℕᵉ lᵉ →
  is-list-of-nontrivial-divisors-ℕᵉ xᵉ lᵉ
is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕᵉ xᵉ nilᵉ _ _ = starᵉ
is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕᵉ
  ( xᵉ)
  ( consᵉ yᵉ lᵉ)
  ( Dᵉ)
  ( Pᵉ) =
  ( is-nontrivial-divisor-head-is-decomposition-is-prime-list-ℕᵉ xᵉ yᵉ lᵉ Dᵉ Pᵉ ,ᵉ
    is-nontrivial-divisors-div-list-ℕᵉ
      ( mul-list-ℕᵉ lᵉ)
      ( xᵉ)
      ( yᵉ ,ᵉ Dᵉ)
      ( lᵉ)
      ( is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕᵉ
        ( mul-list-ℕᵉ lᵉ)
        ( lᵉ)
        ( reflᵉ)
        ( pr2ᵉ Pᵉ)))

is-divisor-head-prime-decomposition-list-ℕᵉ :
  (xᵉ : ℕᵉ) (yᵉ : ℕᵉ) (lᵉ : listᵉ ℕᵉ) →
  is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) →
  div-ℕᵉ yᵉ xᵉ
is-divisor-head-prime-decomposition-list-ℕᵉ xᵉ yᵉ lᵉ Dᵉ =
  is-divisor-head-is-decomposition-list-ℕᵉ
    ( xᵉ)
    ( yᵉ)
    ( lᵉ)
    ( is-decomposition-list-is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) Dᵉ)

is-nontrivial-divisor-head-prime-decomposition-list-ℕᵉ :
  (xᵉ : ℕᵉ) (yᵉ : ℕᵉ) (lᵉ : listᵉ ℕᵉ) →
  is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) →
  is-nontrivial-divisor-ℕᵉ xᵉ yᵉ
is-nontrivial-divisor-head-prime-decomposition-list-ℕᵉ xᵉ yᵉ lᵉ Dᵉ =
  is-nontrivial-divisor-head-is-decomposition-is-prime-list-ℕᵉ
    ( xᵉ)
    ( yᵉ)
    ( lᵉ)
    ( is-decomposition-list-is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) Dᵉ)
    ( is-prime-list-is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) Dᵉ)

is-list-of-nontrivial-divisors-is-prime-decomposition-list-ℕᵉ :
  (xᵉ : ℕᵉ) → (lᵉ : listᵉ ℕᵉ) →
  is-prime-decomposition-list-ℕᵉ xᵉ lᵉ →
  is-list-of-nontrivial-divisors-ℕᵉ xᵉ lᵉ
is-list-of-nontrivial-divisors-is-prime-decomposition-list-ℕᵉ xᵉ lᵉ Dᵉ =
  is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕᵉ
    ( xᵉ)
    ( lᵉ)
    ( is-decomposition-list-is-prime-decomposition-list-ℕᵉ xᵉ lᵉ Dᵉ)
    ( is-prime-list-is-prime-decomposition-list-ℕᵉ xᵉ lᵉ Dᵉ)
```

## Lemmas

### Every natural number strictly greater than `1` has a least nontrivial divisor

```agda
least-nontrivial-divisor-ℕᵉ :
  (nᵉ : ℕᵉ) → le-ℕᵉ 1 nᵉ → minimal-element-ℕᵉ (is-nontrivial-divisor-ℕᵉ nᵉ)
least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ =
  well-ordering-principle-ℕᵉ
    ( is-nontrivial-divisor-ℕᵉ nᵉ)
    ( is-decidable-is-nontrivial-divisor-ℕᵉ nᵉ)
    ( nᵉ ,ᵉ is-nontrivial-divisor-diagonal-ℕᵉ nᵉ Hᵉ)

nat-least-nontrivial-divisor-ℕᵉ : (nᵉ : ℕᵉ) → le-ℕᵉ 1 nᵉ → ℕᵉ
nat-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ = pr1ᵉ (least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ)

le-one-least-nontrivial-divisor-ℕᵉ :
  (nᵉ : ℕᵉ) (Hᵉ : le-ℕᵉ 1 nᵉ) → le-ℕᵉ 1 (nat-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ)
le-one-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ =
  pr1ᵉ (pr1ᵉ (pr2ᵉ (least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ)))

div-least-nontrivial-divisor-ℕᵉ :
  (nᵉ : ℕᵉ) (Hᵉ : le-ℕᵉ 1 nᵉ) → div-ℕᵉ (nat-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ) nᵉ
div-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ =
  pr2ᵉ (pr1ᵉ (pr2ᵉ (least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ)))

is-minimal-least-nontrivial-divisor-ℕᵉ :
  (nᵉ : ℕᵉ) (Hᵉ : le-ℕᵉ 1 nᵉ) (xᵉ : ℕᵉ) (Kᵉ : le-ℕᵉ 1 xᵉ) (dᵉ : div-ℕᵉ xᵉ nᵉ) →
  leq-ℕᵉ (nat-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ) xᵉ
is-minimal-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ xᵉ Kᵉ dᵉ =
  pr2ᵉ (pr2ᵉ (least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ)) xᵉ (Kᵉ ,ᵉ dᵉ)
```

### The least nontrivial divisor of a number `> 1` is nonzero

```agda
abstract
  is-nonzero-least-nontrivial-divisor-ℕᵉ :
    (nᵉ : ℕᵉ) (Hᵉ : le-ℕᵉ 1 nᵉ) → is-nonzero-ℕᵉ (nat-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ)
  is-nonzero-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ =
    is-nonzero-div-ℕᵉ
      ( nat-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ)
      ( nᵉ)
      ( div-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ)
      ( λ where reflᵉ → Hᵉ)
```

### The least nontrivial divisor of a number `> 1` is prime

```agda
is-prime-least-nontrivial-divisor-ℕᵉ :
  (nᵉ : ℕᵉ) (Hᵉ : le-ℕᵉ 1 nᵉ) → is-prime-ℕᵉ (nat-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ)
pr1ᵉ (is-prime-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ xᵉ) (Kᵉ ,ᵉ Lᵉ) =
  map-right-unit-law-coproduct-is-emptyᵉ
    ( is-one-ℕᵉ xᵉ)
    ( le-ℕᵉ 1 xᵉ)
    ( λ pᵉ →
      contradiction-le-ℕᵉ xᵉ lᵉ
        ( le-div-ℕᵉ xᵉ lᵉ
          ( is-nonzero-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ)
          ( Lᵉ)
          ( Kᵉ))
        ( is-minimal-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ xᵉ pᵉ
          ( transitive-div-ℕᵉ xᵉ lᵉ nᵉ (div-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ) Lᵉ)))
    ( eq-or-le-leq-ℕ'ᵉ 1 xᵉ
      ( leq-one-div-ℕᵉ xᵉ nᵉ
        ( transitive-div-ℕᵉ xᵉ lᵉ nᵉ
          ( div-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ) Lᵉ)
        ( leq-le-ℕᵉ 1 nᵉ Hᵉ)))
  where
  lᵉ = nat-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ
pr1ᵉ (pr2ᵉ (is-prime-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ .1ᵉ) reflᵉ) =
  neq-le-ℕᵉ (le-one-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ)
pr2ᵉ (pr2ᵉ (is-prime-least-nontrivial-divisor-ℕᵉ nᵉ Hᵉ .1ᵉ) reflᵉ) =
  div-one-ℕᵉ _
```

### The least prime divisor of a number `1 < n`

```agda
nat-least-prime-divisor-ℕᵉ : (xᵉ : ℕᵉ) → le-ℕᵉ 1 xᵉ → ℕᵉ
nat-least-prime-divisor-ℕᵉ xᵉ Hᵉ = nat-least-nontrivial-divisor-ℕᵉ xᵉ Hᵉ

is-prime-least-prime-divisor-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : le-ℕᵉ 1 xᵉ) → is-prime-ℕᵉ (nat-least-prime-divisor-ℕᵉ xᵉ Hᵉ)
is-prime-least-prime-divisor-ℕᵉ xᵉ Hᵉ = is-prime-least-nontrivial-divisor-ℕᵉ xᵉ Hᵉ

least-prime-divisor-ℕᵉ : (xᵉ : ℕᵉ) → le-ℕᵉ 1 xᵉ → Prime-ℕᵉ
pr1ᵉ (least-prime-divisor-ℕᵉ xᵉ Hᵉ) = nat-least-prime-divisor-ℕᵉ xᵉ Hᵉ
pr2ᵉ (least-prime-divisor-ℕᵉ xᵉ Hᵉ) = is-prime-least-prime-divisor-ℕᵉ xᵉ Hᵉ

div-least-prime-divisor-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : le-ℕᵉ 1 xᵉ) → div-ℕᵉ (nat-least-prime-divisor-ℕᵉ xᵉ Hᵉ) xᵉ
div-least-prime-divisor-ℕᵉ xᵉ Hᵉ = div-least-nontrivial-divisor-ℕᵉ xᵉ Hᵉ

quotient-div-least-prime-divisor-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : le-ℕᵉ 1 xᵉ) → ℕᵉ
quotient-div-least-prime-divisor-ℕᵉ xᵉ Hᵉ =
  quotient-div-ℕᵉ
    ( nat-least-prime-divisor-ℕᵉ xᵉ Hᵉ)
    ( xᵉ)
    ( div-least-prime-divisor-ℕᵉ xᵉ Hᵉ)

leq-quotient-div-least-prime-divisor-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : le-ℕᵉ 1 (succ-ℕᵉ xᵉ)) →
  leq-ℕᵉ (quotient-div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) Hᵉ) xᵉ
leq-quotient-div-least-prime-divisor-ℕᵉ xᵉ Hᵉ =
  leq-quotient-div-is-prime-ℕᵉ
    ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) Hᵉ)
    ( xᵉ)
    ( is-prime-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) Hᵉ)
    ( div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) Hᵉ)
```

## The fundamental theorem of arithmetic (with lists)

### Existence

#### The list given by the fundamental theorem of arithmetic

```agda
list-primes-fundamental-theorem-arithmetic-ℕᵉ :
  (xᵉ : ℕᵉ) → leq-ℕᵉ 1 xᵉ → listᵉ Prime-ℕᵉ
list-primes-fundamental-theorem-arithmetic-ℕᵉ zero-ℕᵉ ()
list-primes-fundamental-theorem-arithmetic-ℕᵉ (succ-ℕᵉ xᵉ) Hᵉ =
  based-strong-ind-ℕᵉ 1
    ( λ _ → listᵉ Prime-ℕᵉ)
    ( nilᵉ)
    ( λ nᵉ Nᵉ fᵉ →
      consᵉ
        ( least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
        ( fᵉ
          ( quotient-div-least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
          ( leq-one-quotient-div-ℕᵉ
            ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
            ( succ-ℕᵉ nᵉ)
            ( div-least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
            ( preserves-leq-succ-ℕᵉ 1 nᵉ Nᵉ))
          ( leq-quotient-div-least-prime-divisor-ℕᵉ nᵉ (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))))
    ( succ-ℕᵉ xᵉ)
    ( Hᵉ)

list-fundamental-theorem-arithmetic-ℕᵉ :
  (xᵉ : ℕᵉ) → leq-ℕᵉ 1 xᵉ → listᵉ ℕᵉ
list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ =
  map-listᵉ nat-Prime-ℕᵉ (list-primes-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)
```

#### Computational rules for the list given by the fundamental theorem of arithmetic

```agda
helper-compute-list-primes-fundamental-theorem-arithmetic-succ-ℕᵉ :
  (xᵉ : ℕᵉ) → (Hᵉ : leq-ℕᵉ 1 xᵉ) →
  based-strong-ind-ℕᵉ 1
    ( λ _ → listᵉ Prime-ℕᵉ)
    ( nilᵉ)
    ( λ nᵉ Nᵉ fᵉ →
      consᵉ
        ( least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
        ( fᵉ
          ( quotient-div-least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
          ( leq-one-quotient-div-ℕᵉ
            ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
            ( succ-ℕᵉ nᵉ)
            ( div-least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
            ( preserves-leq-succ-ℕᵉ 1 nᵉ Nᵉ))
          ( leq-quotient-div-least-prime-divisor-ℕᵉ nᵉ (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))))
    ( xᵉ)
    ( Hᵉ) ＝ᵉ
  list-primes-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ
helper-compute-list-primes-fundamental-theorem-arithmetic-succ-ℕᵉ (succ-ℕᵉ xᵉ) Hᵉ =
  reflᵉ

compute-list-primes-fundamental-theorem-arithmetic-succ-ℕᵉ :
  (xᵉ : ℕᵉ) → (Hᵉ : 1 ≤-ℕᵉ xᵉ) →
  list-primes-fundamental-theorem-arithmetic-ℕᵉ (succ-ℕᵉ xᵉ) starᵉ ＝ᵉ
  consᵉ
    ( least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
    ( list-primes-fundamental-theorem-arithmetic-ℕᵉ
      ( quotient-div-least-prime-divisor-ℕᵉ
        ( succ-ℕᵉ xᵉ)
        ( le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
      ( leq-one-quotient-div-ℕᵉ
        ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
        ( succ-ℕᵉ xᵉ)
        ( div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
        ( preserves-leq-succ-ℕᵉ 1 xᵉ Hᵉ)))
compute-list-primes-fundamental-theorem-arithmetic-succ-ℕᵉ xᵉ Hᵉ =
  compute-succ-based-strong-ind-ℕᵉ
    ( 1ᵉ)
    ( λ _ → listᵉ Prime-ℕᵉ)
    ( nilᵉ)
    ( λ nᵉ Nᵉ fᵉ →
      consᵉ
        ( least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
        ( fᵉ
          ( quotient-div-least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
          ( leq-one-quotient-div-ℕᵉ
            ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
            ( succ-ℕᵉ nᵉ)
            ( div-least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
            ( preserves-leq-succ-ℕᵉ 1 nᵉ Nᵉ))
          ( leq-quotient-div-least-prime-divisor-ℕᵉ nᵉ (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))))
    ( xᵉ)
    ( Hᵉ)
    ( starᵉ) ∙ᵉ
  apᵉ
    ( consᵉ (least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ)))
    ( helper-compute-list-primes-fundamental-theorem-arithmetic-succ-ℕᵉ
      ( quotient-div-least-prime-divisor-ℕᵉ
        ( succ-ℕᵉ xᵉ)
        ( le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
      ( leq-one-quotient-div-ℕᵉ
        ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
        ( succ-ℕᵉ xᵉ)
        ( div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
        ( preserves-leq-succ-ℕᵉ 1 xᵉ Hᵉ)))

compute-list-fundamental-theorem-arithmetic-succ-ℕᵉ :
  (xᵉ : ℕᵉ) → (Hᵉ : leq-ℕᵉ 1 xᵉ) →
  list-fundamental-theorem-arithmetic-ℕᵉ (succ-ℕᵉ xᵉ) starᵉ ＝ᵉ
  consᵉ
    ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
    ( list-fundamental-theorem-arithmetic-ℕᵉ
      ( quotient-div-least-prime-divisor-ℕᵉ
        ( succ-ℕᵉ xᵉ)
        ( le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
      ( leq-one-quotient-div-ℕᵉ
        ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
        ( succ-ℕᵉ xᵉ)
        ( div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
        ( preserves-leq-succ-ℕᵉ 1 xᵉ Hᵉ)))
compute-list-fundamental-theorem-arithmetic-succ-ℕᵉ xᵉ Hᵉ =
  apᵉ
    ( map-listᵉ nat-Prime-ℕᵉ)
    ( compute-list-primes-fundamental-theorem-arithmetic-succ-ℕᵉ xᵉ Hᵉ)
```

#### Proof that the list given by the fundamental theorem of arithmetic is a prime decomposition

```agda
is-prime-list-fundamental-theorem-arithmetic-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : leq-ℕᵉ 1 xᵉ) →
  is-prime-list-ℕᵉ (list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)
is-prime-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ =
  is-prime-list-primes-ℕᵉ (list-primes-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)

is-decomposition-list-fundamental-theorem-arithmetic-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : leq-ℕᵉ 1 xᵉ) →
  is-decomposition-list-ℕᵉ xᵉ (list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)
is-decomposition-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ =
  based-strong-ind-ℕ'ᵉ 1
    ( λ nᵉ Nᵉ →
      is-decomposition-list-ℕᵉ nᵉ (list-fundamental-theorem-arithmetic-ℕᵉ nᵉ Nᵉ))
    ( reflᵉ)
    ( λ nᵉ Nᵉ fᵉ →
      trᵉ
        ( λ pᵉ → is-decomposition-list-ℕᵉ (succ-ℕᵉ nᵉ) pᵉ)
        ( invᵉ (compute-list-fundamental-theorem-arithmetic-succ-ℕᵉ nᵉ Nᵉ))
        ( ( apᵉ
            ( ( nat-least-prime-divisor-ℕᵉ
                ( succ-ℕᵉ nᵉ)
                ( le-succ-leq-ℕᵉ 1 nᵉ Nᵉ)) *ℕᵉ_)
            ( fᵉ
              ( quotient-div-least-prime-divisor-ℕᵉ
                ( succ-ℕᵉ nᵉ)
                ( le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
              ( leq-one-quotient-div-ℕᵉ
                ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
                ( succ-ℕᵉ nᵉ)
                ( div-least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
                ( preserves-leq-succ-ℕᵉ 1 nᵉ Nᵉ))
              ( leq-quotient-div-least-prime-divisor-ℕᵉ
                ( nᵉ)
                ( le-succ-leq-ℕᵉ 1 nᵉ Nᵉ)))) ∙ᵉ
          eq-quotient-div-ℕ'ᵉ
            ( nat-least-prime-divisor-ℕᵉ
              ( succ-ℕᵉ nᵉ)
              ( le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
            ( succ-ℕᵉ nᵉ)
            ( div-least-prime-divisor-ℕᵉ
              ( succ-ℕᵉ nᵉ)
              ( le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))))
    ( xᵉ)
    ( Hᵉ)

is-list-of-nontrivial-divisors-fundamental-theorem-arithmetic-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : leq-ℕᵉ 1 xᵉ) →
  is-list-of-nontrivial-divisors-ℕᵉ xᵉ (list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)
is-list-of-nontrivial-divisors-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ =
  is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕᵉ
    ( xᵉ)
    ( list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)
    ( is-decomposition-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)
    ( is-prime-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)

is-least-element-list-least-prime-divisor-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : leq-ℕᵉ 1 xᵉ) (lᵉ : listᵉ ℕᵉ) →
  is-list-of-nontrivial-divisors-ℕᵉ
    ( quotient-div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
    ( lᵉ) →
  is-least-element-listᵉ
    ( ℕ-Decidable-Total-Orderᵉ)
    ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
    ( lᵉ)
is-least-element-list-least-prime-divisor-ℕᵉ xᵉ Hᵉ nilᵉ Dᵉ = raise-starᵉ
is-least-element-list-least-prime-divisor-ℕᵉ xᵉ Hᵉ (consᵉ yᵉ lᵉ) Dᵉ =
  is-minimal-least-nontrivial-divisor-ℕᵉ
    ( succ-ℕᵉ xᵉ)
    ( le-succ-leq-ℕᵉ 1 xᵉ Hᵉ)
    ( yᵉ)
    ( pr1ᵉ (pr1ᵉ Dᵉ))
    ( transitive-div-ℕᵉ
      ( yᵉ)
      ( quotient-div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
      ( succ-ℕᵉ xᵉ)
      ( div-quotient-div-ℕᵉ
        ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
        ( succ-ℕᵉ xᵉ)
        ( div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ)))
      ( pr2ᵉ (pr1ᵉ Dᵉ))) ,ᵉ
  is-least-element-list-least-prime-divisor-ℕᵉ xᵉ Hᵉ lᵉ (pr2ᵉ Dᵉ)

is-least-element-head-list-fundamental-theorem-arithmetic-succ-ℕᵉ :
  (xᵉ : ℕᵉ) → (Hᵉ : leq-ℕᵉ 1 xᵉ) →
  is-least-element-listᵉ
    ( ℕ-Decidable-Total-Orderᵉ)
    ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
    ( list-fundamental-theorem-arithmetic-ℕᵉ
      ( quotient-div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
      ( leq-one-quotient-div-ℕᵉ
        ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
        ( succ-ℕᵉ xᵉ)
        ( div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
        ( preserves-leq-succ-ℕᵉ 1 xᵉ Hᵉ)))
is-least-element-head-list-fundamental-theorem-arithmetic-succ-ℕᵉ xᵉ Hᵉ =
  is-least-element-list-least-prime-divisor-ℕᵉ
    ( xᵉ)
    ( Hᵉ)
    ( list-fundamental-theorem-arithmetic-ℕᵉ
      ( quotient-div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
      ( leq-one-quotient-div-ℕᵉ
        ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
        ( succ-ℕᵉ xᵉ)
        ( div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
        ( preserves-leq-succ-ℕᵉ 1 xᵉ Hᵉ)))
    ( is-list-of-nontrivial-divisors-fundamental-theorem-arithmetic-ℕᵉ
      ( quotient-div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
      ( leq-one-quotient-div-ℕᵉ
        ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
        ( succ-ℕᵉ xᵉ)
        ( div-least-prime-divisor-ℕᵉ (succ-ℕᵉ xᵉ) (le-succ-leq-ℕᵉ 1 xᵉ Hᵉ))
        ( preserves-leq-succ-ℕᵉ 1 xᵉ Hᵉ)))

is-sorted-least-element-list-fundamental-theorem-arithmetic-ℕᵉ :
  (xᵉ : ℕᵉ) → (Hᵉ : leq-ℕᵉ 1 xᵉ) →
  is-sorted-least-element-listᵉ
    ( ℕ-Decidable-Total-Orderᵉ)
    ( list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)
is-sorted-least-element-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ =
  based-strong-ind-ℕ'ᵉ 1
    ( λ xᵉ Hᵉ →
      is-sorted-least-element-listᵉ
        ( ℕ-Decidable-Total-Orderᵉ)
        ( list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ))
    ( raise-starᵉ)
    ( λ nᵉ Nᵉ fᵉ →
      trᵉ
        ( λ lᵉ →
          is-sorted-least-element-listᵉ
            ( ℕ-Decidable-Total-Orderᵉ)
            ( lᵉ))
        ( invᵉ (compute-list-fundamental-theorem-arithmetic-succ-ℕᵉ nᵉ Nᵉ))
        ( is-least-element-head-list-fundamental-theorem-arithmetic-succ-ℕᵉ nᵉ Nᵉ ,ᵉ
          fᵉ
            ( quotient-div-least-prime-divisor-ℕᵉ
              ( succ-ℕᵉ nᵉ)
              ( le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
            ( leq-one-quotient-div-ℕᵉ
              ( nat-least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
              ( succ-ℕᵉ nᵉ)
              ( div-least-prime-divisor-ℕᵉ (succ-ℕᵉ nᵉ) (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))
              ( preserves-leq-succ-ℕᵉ 1 nᵉ Nᵉ))
            ( leq-quotient-div-least-prime-divisor-ℕᵉ nᵉ (le-succ-leq-ℕᵉ 1 nᵉ Nᵉ))))
    ( xᵉ)
    ( Hᵉ)

is-sorted-list-fundamental-theorem-arithmetic-ℕᵉ :
  (xᵉ : ℕᵉ) → (Hᵉ : leq-ℕᵉ 1 xᵉ) →
  is-sorted-listᵉ
    ( ℕ-Decidable-Total-Orderᵉ)
    ( list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)
is-sorted-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ =
  is-sorted-list-is-sorted-least-element-listᵉ
    ( ℕ-Decidable-Total-Orderᵉ)
    ( list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)
    ( is-sorted-least-element-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)

is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : leq-ℕᵉ 1 xᵉ) →
  is-prime-decomposition-list-ℕᵉ xᵉ (list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)
pr1ᵉ (is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ) =
  is-sorted-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ
pr1ᵉ (pr2ᵉ (is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)) =
  is-prime-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ
pr2ᵉ (pr2ᵉ (is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)) =
  is-decomposition-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ
```

### Uniqueness

#### Definition of the type of prime decomposition of an integer

```agda
prime-decomposition-list-ℕᵉ :
  (xᵉ : ℕᵉ) → (leq-ℕᵉ 1 xᵉ) → UUᵉ lzero
prime-decomposition-list-ℕᵉ xᵉ _ =
  Σᵉ (listᵉ ℕᵉ) (λ lᵉ → is-prime-decomposition-list-ℕᵉ xᵉ lᵉ)
```

#### `prime-decomposition-list-ℕ n` is contractible for every `n`

```agda
prime-decomposition-fundamental-theorem-arithmetic-list-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : leq-ℕᵉ 1 xᵉ) → prime-decomposition-list-ℕᵉ xᵉ Hᵉ
pr1ᵉ (prime-decomposition-fundamental-theorem-arithmetic-list-ℕᵉ xᵉ Hᵉ) =
  list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ
pr2ᵉ (prime-decomposition-fundamental-theorem-arithmetic-list-ℕᵉ xᵉ Hᵉ) =
  is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ

le-one-is-nonempty-prime-decomposition-list-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : leq-ℕᵉ 1 xᵉ) (yᵉ : ℕᵉ) (lᵉ : listᵉ ℕᵉ) →
  is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) →
  le-ℕᵉ 1 xᵉ
le-one-is-nonempty-prime-decomposition-list-ℕᵉ xᵉ Hᵉ yᵉ lᵉ Dᵉ =
  concatenate-le-leq-ℕᵉ
    {xᵉ = 1ᵉ}
    {yᵉ = yᵉ}
    {zᵉ = xᵉ}
    ( le-one-is-prime-ℕᵉ
      ( yᵉ)
      ( pr1ᵉ (is-prime-list-is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) Dᵉ)))
    ( leq-div-ℕᵉ
      ( yᵉ)
      ( xᵉ)
      ( is-nonzero-leq-one-ℕᵉ xᵉ Hᵉ)
      ( mul-list-ℕᵉ lᵉ ,ᵉ
        ( commutative-mul-ℕᵉ (mul-list-ℕᵉ lᵉ) yᵉ ∙ᵉ
          is-decomposition-list-is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) Dᵉ)))

is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : leq-ℕᵉ 1 xᵉ) (lᵉ : listᵉ ℕᵉ) →
  is-prime-decomposition-list-ℕᵉ xᵉ lᵉ →
  ( yᵉ : ℕᵉ) →
  div-ℕᵉ yᵉ xᵉ →
  is-prime-ℕᵉ yᵉ →
  yᵉ ∈-listᵉ lᵉ
is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕᵉ xᵉ Hᵉ nilᵉ Dᵉ yᵉ dᵉ pᵉ =
  ex-falsoᵉ
    ( contradiction-le-ℕᵉ
      ( 1ᵉ)
      ( xᵉ)
      ( concatenate-le-leq-ℕᵉ
        {xᵉ = 1ᵉ}
        {yᵉ = yᵉ}
        {zᵉ = xᵉ}
        ( le-one-is-prime-ℕᵉ yᵉ pᵉ)
        ( leq-div-ℕᵉ
          ( yᵉ)
          ( xᵉ)
          ( is-nonzero-leq-one-ℕᵉ xᵉ Hᵉ)
          ( dᵉ)))
        ( leq-eq-ℕᵉ
          ( xᵉ)
          ( 1ᵉ)
          ( invᵉ (is-decomposition-list-is-prime-decomposition-list-ℕᵉ xᵉ nilᵉ Dᵉ))))
is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕᵉ xᵉ Hᵉ (consᵉ zᵉ lᵉ) Dᵉ yᵉ dᵉ pᵉ =
  rec-coproductᵉ
    ( λ eᵉ → trᵉ (λ wᵉ → wᵉ ∈-listᵉ (consᵉ zᵉ lᵉ)) (invᵉ eᵉ) (is-headᵉ zᵉ lᵉ))
    ( λ eᵉ →
      is-in-tailᵉ
        ( yᵉ)
        ( zᵉ)
        ( lᵉ)
        ( is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕᵉ
          ( quotient-div-ℕᵉ
            ( zᵉ)
            ( xᵉ)
            ( is-divisor-head-prime-decomposition-list-ℕᵉ xᵉ zᵉ lᵉ Dᵉ))
          ( leq-one-quotient-div-ℕᵉ
            ( zᵉ)
            ( xᵉ)
            ( is-divisor-head-prime-decomposition-list-ℕᵉ xᵉ zᵉ lᵉ Dᵉ)
            ( Hᵉ))
          ( lᵉ)
          ( ( is-sorted-tail-is-sorted-listᵉ
              ( ℕ-Decidable-Total-Orderᵉ)
              ( consᵉ zᵉ lᵉ)
              ( is-sorted-list-is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ zᵉ lᵉ) Dᵉ)) ,ᵉ
            ( pr2ᵉ
              ( is-prime-list-is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ zᵉ lᵉ) Dᵉ)) ,ᵉ
            ( reflᵉ))
          ( yᵉ)
          ( div-right-factor-coprime-ℕᵉ
            ( yᵉ)
            ( zᵉ)
            ( mul-list-ℕᵉ lᵉ)
            ( trᵉ
              ( λ xᵉ → div-ℕᵉ yᵉ xᵉ)
              ( invᵉ
                ( is-decomposition-list-is-prime-decomposition-list-ℕᵉ
                  ( xᵉ)
                  ( consᵉ zᵉ lᵉ)
                  ( Dᵉ)))
              ( dᵉ))
            ( is-relatively-prime-is-prime-ℕᵉ
              ( yᵉ)
              ( zᵉ)
              ( pᵉ)
              ( pr1ᵉ
                ( is-prime-list-is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ zᵉ lᵉ) Dᵉ))
              ( eᵉ)))
          ( pᵉ)))
    ( has-decidable-equality-ℕᵉ yᵉ zᵉ)

is-lower-bound-head-prime-decomposition-list-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : leq-ℕᵉ 1 xᵉ) (yᵉ : ℕᵉ) (lᵉ : listᵉ ℕᵉ) →
  is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) →
  is-lower-bound-ℕᵉ (is-nontrivial-divisor-ℕᵉ xᵉ) yᵉ
is-lower-bound-head-prime-decomposition-list-ℕᵉ xᵉ Hᵉ yᵉ lᵉ Dᵉ mᵉ dᵉ =
  transitive-leq-ℕᵉ
    ( yᵉ)
    ( nat-least-prime-divisor-ℕᵉ mᵉ (pr1ᵉ dᵉ))
    ( mᵉ)
    ( leq-div-ℕᵉ
      ( nat-least-prime-divisor-ℕᵉ mᵉ (pr1ᵉ dᵉ))
      ( mᵉ)
      ( is-nonzero-le-ℕᵉ 1 mᵉ (pr1ᵉ dᵉ))
      ( div-least-prime-divisor-ℕᵉ mᵉ (pr1ᵉ dᵉ)))
    ( leq-element-in-list-leq-head-is-sorted-listᵉ
      ( ℕ-Decidable-Total-Orderᵉ)
      ( yᵉ)
      ( yᵉ)
      ( nat-least-prime-divisor-ℕᵉ mᵉ (pr1ᵉ dᵉ))
      ( lᵉ)
      ( is-sorted-list-is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) Dᵉ)
      ( is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕᵉ
        ( xᵉ)
        ( Hᵉ)
        ( consᵉ yᵉ lᵉ)
        ( Dᵉ)
        ( nat-least-prime-divisor-ℕᵉ mᵉ (pr1ᵉ dᵉ))
        ( transitive-div-ℕᵉ
          ( nat-least-prime-divisor-ℕᵉ mᵉ (pr1ᵉ dᵉ))
          ( mᵉ)
          ( xᵉ)
          ( pr2ᵉ dᵉ)
          ( div-least-nontrivial-divisor-ℕᵉ mᵉ (pr1ᵉ dᵉ)))
        ( is-prime-least-prime-divisor-ℕᵉ mᵉ (pr1ᵉ dᵉ)))
      ( refl-leq-ℕᵉ yᵉ))

eq-head-prime-decomposition-list-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : leq-ℕᵉ 1 xᵉ) (yᵉ zᵉ : ℕᵉ) (pᵉ qᵉ : listᵉ ℕᵉ) →
  is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ pᵉ) →
  is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ zᵉ qᵉ) →
  yᵉ ＝ᵉ zᵉ
eq-head-prime-decomposition-list-ℕᵉ xᵉ Hᵉ yᵉ zᵉ pᵉ qᵉ Iᵉ Jᵉ =
  apᵉ
    ( pr1ᵉ)
    ( all-elements-equal-minimal-element-ℕᵉ
      ( is-nontrivial-divisor-ℕ-Propᵉ xᵉ)
      ( yᵉ ,ᵉ
        is-nontrivial-divisor-head-prime-decomposition-list-ℕᵉ xᵉ yᵉ pᵉ Iᵉ ,ᵉ
        is-lower-bound-head-prime-decomposition-list-ℕᵉ xᵉ Hᵉ yᵉ pᵉ Iᵉ)
      ( zᵉ ,ᵉ
        is-nontrivial-divisor-head-prime-decomposition-list-ℕᵉ xᵉ zᵉ qᵉ Jᵉ ,ᵉ
        is-lower-bound-head-prime-decomposition-list-ℕᵉ xᵉ Hᵉ zᵉ qᵉ Jᵉ))

eq-prime-decomposition-list-ℕᵉ :
  (xᵉ : ℕᵉ) (Hᵉ : leq-ℕᵉ 1 xᵉ) (pᵉ qᵉ : listᵉ ℕᵉ) →
  is-prime-decomposition-list-ℕᵉ xᵉ pᵉ →
  is-prime-decomposition-list-ℕᵉ xᵉ qᵉ →
  pᵉ ＝ᵉ qᵉ
eq-prime-decomposition-list-ℕᵉ xᵉ Hᵉ nilᵉ nilᵉ _ _ =
  reflᵉ
eq-prime-decomposition-list-ℕᵉ xᵉ Hᵉ (consᵉ yᵉ lᵉ) nilᵉ Iᵉ Jᵉ =
  ex-falsoᵉ
    ( contradiction-le-ℕᵉ
      ( 1ᵉ)
      ( xᵉ)
      ( le-one-is-nonempty-prime-decomposition-list-ℕᵉ xᵉ Hᵉ yᵉ lᵉ Iᵉ)
      ( leq-eq-ℕᵉ
        ( xᵉ)
        ( 1ᵉ)
        ( invᵉ ( is-decomposition-list-is-prime-decomposition-list-ℕᵉ xᵉ nilᵉ Jᵉ))))
eq-prime-decomposition-list-ℕᵉ xᵉ Hᵉ nilᵉ (consᵉ yᵉ lᵉ) Iᵉ Jᵉ =
  ex-falsoᵉ
    ( contradiction-le-ℕᵉ
      ( 1ᵉ)
      ( xᵉ)
      ( le-one-is-nonempty-prime-decomposition-list-ℕᵉ xᵉ Hᵉ yᵉ lᵉ Jᵉ)
      ( leq-eq-ℕᵉ
        ( xᵉ)
        ( 1ᵉ)
        ( invᵉ (is-decomposition-list-is-prime-decomposition-list-ℕᵉ xᵉ nilᵉ Iᵉ))))
eq-prime-decomposition-list-ℕᵉ xᵉ Hᵉ (consᵉ yᵉ lᵉ) (consᵉ zᵉ pᵉ) Iᵉ Jᵉ =
  eq-Eq-listᵉ
    ( consᵉ yᵉ lᵉ)
    ( consᵉ zᵉ pᵉ)
    ( ( eq-head-prime-decomposition-list-ℕᵉ xᵉ Hᵉ yᵉ zᵉ lᵉ pᵉ Iᵉ Jᵉ) ,ᵉ
      ( Eq-eq-listᵉ
        ( lᵉ)
        ( pᵉ)
        ( eq-prime-decomposition-list-ℕᵉ
          ( quotient-div-ℕᵉ
            ( yᵉ)
            ( xᵉ)
            ( is-divisor-head-prime-decomposition-list-ℕᵉ xᵉ yᵉ lᵉ Iᵉ))
          ( leq-one-quotient-div-ℕᵉ
            ( yᵉ)
            ( xᵉ)
            ( is-divisor-head-prime-decomposition-list-ℕᵉ xᵉ yᵉ lᵉ Iᵉ)
            ( Hᵉ))
          ( lᵉ)
          ( pᵉ)
          ( ( is-sorted-tail-is-sorted-listᵉ
              ( ℕ-Decidable-Total-Orderᵉ)
              ( consᵉ yᵉ lᵉ)
              ( is-sorted-list-is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) Iᵉ)) ,ᵉ
            pr2ᵉ (is-prime-list-is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ yᵉ lᵉ) Iᵉ) ,ᵉ
            reflᵉ)
          ( ( is-sorted-tail-is-sorted-listᵉ
              ( ℕ-Decidable-Total-Orderᵉ)
              ( consᵉ zᵉ pᵉ)
              ( is-sorted-list-is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ zᵉ pᵉ) Jᵉ)) ,ᵉ
            pr2ᵉ (is-prime-list-is-prime-decomposition-list-ℕᵉ xᵉ (consᵉ zᵉ pᵉ) Jᵉ) ,ᵉ
            trᵉ
              ( λ yᵉ → is-decomposition-list-ℕᵉ yᵉ pᵉ)
              ( eq-quotient-div-eq-div-ℕᵉ
                ( zᵉ)
                ( yᵉ)
                ( xᵉ)
                ( is-nonzero-is-prime-ℕᵉ
                  ( zᵉ)
                  ( pr1ᵉ
                    ( is-prime-list-is-prime-decomposition-list-ℕᵉ
                      ( xᵉ)
                      ( consᵉ zᵉ pᵉ)
                      ( Jᵉ))))
                ( invᵉ (eq-head-prime-decomposition-list-ℕᵉ xᵉ Hᵉ yᵉ zᵉ lᵉ pᵉ Iᵉ Jᵉ))
                ( is-divisor-head-prime-decomposition-list-ℕᵉ xᵉ zᵉ pᵉ Jᵉ)
                ( is-divisor-head-prime-decomposition-list-ℕᵉ xᵉ yᵉ lᵉ Iᵉ))
              ( reflᵉ)))))

fundamental-theorem-arithmetic-list-ℕᵉ :
  (xᵉ : ℕᵉ) → (Hᵉ : leq-ℕᵉ 1 xᵉ) → is-contrᵉ (prime-decomposition-list-ℕᵉ xᵉ Hᵉ)
pr1ᵉ (fundamental-theorem-arithmetic-list-ℕᵉ xᵉ Hᵉ) =
  prime-decomposition-fundamental-theorem-arithmetic-list-ℕᵉ xᵉ Hᵉ
pr2ᵉ (fundamental-theorem-arithmetic-list-ℕᵉ xᵉ Hᵉ) dᵉ =
  eq-type-subtypeᵉ
    ( is-prime-decomposition-list-ℕ-Propᵉ xᵉ)
    ( eq-prime-decomposition-list-ℕᵉ
      ( xᵉ)
      ( Hᵉ)
      ( list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)
      ( pr1ᵉ dᵉ)
      ( is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕᵉ xᵉ Hᵉ)
      ( pr2ᵉ dᵉ))
```

### The sorted list associated with the concatenation of the prime decomposition of `n` and the prime decomposition of `m` is the prime decomposition of `n *ℕ m`

```agda
is-prime-list-concat-list-ℕᵉ :
  (pᵉ qᵉ : listᵉ ℕᵉ) → is-prime-list-ℕᵉ pᵉ → is-prime-list-ℕᵉ qᵉ →
  is-prime-list-ℕᵉ (concat-listᵉ pᵉ qᵉ)
is-prime-list-concat-list-ℕᵉ nilᵉ qᵉ Ppᵉ Pqᵉ = Pqᵉ
is-prime-list-concat-list-ℕᵉ (consᵉ xᵉ pᵉ) qᵉ Ppᵉ Pqᵉ =
  pr1ᵉ Ppᵉ ,ᵉ is-prime-list-concat-list-ℕᵉ pᵉ qᵉ (pr2ᵉ Ppᵉ) Pqᵉ

all-elements-is-prime-list-ℕᵉ :
  (pᵉ : listᵉ ℕᵉ) → UUᵉ lzero
all-elements-is-prime-list-ℕᵉ pᵉ = (xᵉ : ℕᵉ) → xᵉ ∈-listᵉ pᵉ → is-prime-ℕᵉ xᵉ

all-elements-is-prime-list-tail-ℕᵉ :
  (pᵉ : listᵉ ℕᵉ) (xᵉ : ℕᵉ) (Pᵉ : all-elements-is-prime-list-ℕᵉ (consᵉ xᵉ pᵉ)) →
  all-elements-is-prime-list-ℕᵉ pᵉ
all-elements-is-prime-list-tail-ℕᵉ pᵉ xᵉ Pᵉ yᵉ Iᵉ = Pᵉ yᵉ (is-in-tailᵉ yᵉ xᵉ pᵉ Iᵉ)

all-elements-is-prime-list-is-prime-list-ℕᵉ :
  (pᵉ : listᵉ ℕᵉ) → is-prime-list-ℕᵉ pᵉ → all-elements-is-prime-list-ℕᵉ pᵉ
all-elements-is-prime-list-is-prime-list-ℕᵉ (consᵉ xᵉ pᵉ) Pᵉ .xᵉ (is-headᵉ .xᵉ .pᵉ) =
  pr1ᵉ Pᵉ
all-elements-is-prime-list-is-prime-list-ℕᵉ
  ( consᵉ xᵉ pᵉ)
  ( Pᵉ)
  ( yᵉ)
  ( is-in-tailᵉ .yᵉ .xᵉ .pᵉ Iᵉ) =
  all-elements-is-prime-list-is-prime-list-ℕᵉ pᵉ (pr2ᵉ Pᵉ) yᵉ Iᵉ

is-prime-list-all-elements-is-prime-list-ℕᵉ :
  (pᵉ : listᵉ ℕᵉ) → all-elements-is-prime-list-ℕᵉ pᵉ → is-prime-list-ℕᵉ pᵉ
is-prime-list-all-elements-is-prime-list-ℕᵉ nilᵉ Pᵉ = raise-starᵉ
is-prime-list-all-elements-is-prime-list-ℕᵉ (consᵉ xᵉ pᵉ) Pᵉ =
  Pᵉ xᵉ (is-headᵉ xᵉ pᵉ) ,ᵉ
  is-prime-list-all-elements-is-prime-list-ℕᵉ
    ( pᵉ)
    ( all-elements-is-prime-list-tail-ℕᵉ pᵉ xᵉ Pᵉ)

is-prime-list-permute-list-ℕᵉ :
  (pᵉ : listᵉ ℕᵉ) (tᵉ : Permutationᵉ (length-listᵉ pᵉ)) → is-prime-list-ℕᵉ pᵉ →
  is-prime-list-ℕᵉ (permute-listᵉ pᵉ tᵉ)
is-prime-list-permute-list-ℕᵉ pᵉ tᵉ Pᵉ =
  is-prime-list-all-elements-is-prime-list-ℕᵉ
    ( permute-listᵉ pᵉ tᵉ)
    ( λ xᵉ Iᵉ → all-elements-is-prime-list-is-prime-list-ℕᵉ
      ( pᵉ)
      ( Pᵉ)
      ( xᵉ)
      ( is-in-list-is-in-permute-listᵉ
        ( pᵉ)
        ( tᵉ)
        ( xᵉ)
        ( Iᵉ)))

is-decomposition-list-concat-list-ℕᵉ :
  (nᵉ mᵉ : ℕᵉ) (pᵉ qᵉ : listᵉ ℕᵉ) →
  is-decomposition-list-ℕᵉ nᵉ pᵉ → is-decomposition-list-ℕᵉ mᵉ qᵉ →
  is-decomposition-list-ℕᵉ (nᵉ *ℕᵉ mᵉ) (concat-listᵉ pᵉ qᵉ)
is-decomposition-list-concat-list-ℕᵉ nᵉ mᵉ pᵉ qᵉ Dpᵉ Dqᵉ =
  ( eq-mul-list-concat-list-ℕᵉ pᵉ qᵉ ∙ᵉ
    ( apᵉ (mul-ℕᵉ (mul-list-ℕᵉ pᵉ)) Dqᵉ ∙ᵉ
      apᵉ (λ nᵉ → nᵉ *ℕᵉ mᵉ) Dpᵉ))

is-decomposition-list-permute-list-ℕᵉ :
  (nᵉ : ℕᵉ) (pᵉ : listᵉ ℕᵉ) (tᵉ : Permutationᵉ (length-listᵉ pᵉ)) →
  is-decomposition-list-ℕᵉ nᵉ pᵉ →
  is-decomposition-list-ℕᵉ nᵉ (permute-listᵉ pᵉ tᵉ)
is-decomposition-list-permute-list-ℕᵉ nᵉ pᵉ tᵉ Dᵉ =
  invᵉ (invariant-permutation-mul-list-ℕᵉ pᵉ tᵉ) ∙ᵉ Dᵉ

is-prime-decomposition-list-sort-concatenation-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) (Hᵉ : leq-ℕᵉ 1 xᵉ) (Iᵉ : leq-ℕᵉ 1 yᵉ) (pᵉ qᵉ : listᵉ ℕᵉ) →
  is-prime-decomposition-list-ℕᵉ xᵉ pᵉ →
  is-prime-decomposition-list-ℕᵉ yᵉ qᵉ →
  is-prime-decomposition-list-ℕᵉ
    (xᵉ *ℕᵉ yᵉ)
    ( insertion-sort-listᵉ
      ( ℕ-Decidable-Total-Orderᵉ)
      ( concat-listᵉ pᵉ qᵉ))
pr1ᵉ (is-prime-decomposition-list-sort-concatenation-ℕᵉ xᵉ yᵉ Hᵉ Iᵉ pᵉ qᵉ Dpᵉ Dqᵉ) =
  is-sorting-insertion-sort-listᵉ ℕ-Decidable-Total-Orderᵉ (concat-listᵉ pᵉ qᵉ)
pr1ᵉ
  ( pr2ᵉ
    ( is-prime-decomposition-list-sort-concatenation-ℕᵉ xᵉ yᵉ Hᵉ Iᵉ pᵉ qᵉ Dpᵉ Dqᵉ)) =
  trᵉ
    ( λ pᵉ → is-prime-list-ℕᵉ pᵉ)
    ( invᵉ
      ( eq-permute-list-permutation-insertion-sort-listᵉ
        ( ℕ-Decidable-Total-Orderᵉ)
        ( concat-listᵉ pᵉ qᵉ)))
    ( is-prime-list-permute-list-ℕᵉ
      ( concat-listᵉ pᵉ qᵉ)
      ( permutation-insertion-sort-listᵉ
        ( ℕ-Decidable-Total-Orderᵉ)
        ( concat-listᵉ pᵉ qᵉ))
      ( is-prime-list-concat-list-ℕᵉ
        ( pᵉ)
        ( qᵉ)
        ( is-prime-list-is-prime-decomposition-list-ℕᵉ xᵉ pᵉ Dpᵉ)
        ( is-prime-list-is-prime-decomposition-list-ℕᵉ yᵉ qᵉ Dqᵉ)))
pr2ᵉ
  ( pr2ᵉ
    ( is-prime-decomposition-list-sort-concatenation-ℕᵉ xᵉ yᵉ Hᵉ Iᵉ pᵉ qᵉ Dpᵉ Dqᵉ)) =
  trᵉ
    ( λ pᵉ → is-decomposition-list-ℕᵉ (xᵉ *ℕᵉ yᵉ) pᵉ)
    ( invᵉ
      ( eq-permute-list-permutation-insertion-sort-listᵉ
        ( ℕ-Decidable-Total-Orderᵉ)
        ( concat-listᵉ pᵉ qᵉ)))
    ( is-decomposition-list-permute-list-ℕᵉ
      ( xᵉ *ℕᵉ yᵉ)
      ( concat-listᵉ pᵉ qᵉ)
      ( permutation-insertion-sort-listᵉ
        ( ℕ-Decidable-Total-Orderᵉ)
        ( concat-listᵉ pᵉ qᵉ))
      ( is-decomposition-list-concat-list-ℕᵉ
        ( xᵉ)
        ( yᵉ)
        ( pᵉ)
        ( qᵉ)
        ( is-decomposition-list-is-prime-decomposition-list-ℕᵉ xᵉ pᵉ Dpᵉ)
        ( is-decomposition-list-is-prime-decomposition-list-ℕᵉ yᵉ qᵉ Dqᵉ)))

prime-decomposition-list-sort-concatenation-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) (Hᵉ : leq-ℕᵉ 1 xᵉ) (Iᵉ : leq-ℕᵉ 1 yᵉ) (pᵉ qᵉ : listᵉ ℕᵉ) →
  is-prime-decomposition-list-ℕᵉ xᵉ pᵉ →
  is-prime-decomposition-list-ℕᵉ yᵉ qᵉ →
  prime-decomposition-list-ℕᵉ (xᵉ *ℕᵉ yᵉ) (preserves-leq-mul-ℕᵉ 1 xᵉ 1 yᵉ Hᵉ Iᵉ)
pr1ᵉ (prime-decomposition-list-sort-concatenation-ℕᵉ xᵉ yᵉ Hᵉ Iᵉ pᵉ qᵉ Dpᵉ Dqᵉ) =
  insertion-sort-listᵉ ℕ-Decidable-Total-Orderᵉ (concat-listᵉ pᵉ qᵉ)
pr2ᵉ (prime-decomposition-list-sort-concatenation-ℕᵉ xᵉ yᵉ Hᵉ Iᵉ pᵉ qᵉ Dpᵉ Dqᵉ) =
  is-prime-decomposition-list-sort-concatenation-ℕᵉ xᵉ yᵉ Hᵉ Iᵉ pᵉ qᵉ Dpᵉ Dqᵉ
```