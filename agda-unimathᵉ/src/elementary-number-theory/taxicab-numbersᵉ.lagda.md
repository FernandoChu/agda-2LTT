# Taxicab numbers

```agda
module elementary-number-theory.taxicab-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.cubes-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonzero-natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ `n`-thᵉ
{{#conceptᵉ "taxicabᵉ number"ᵉ Agda=is-taxicab-number-ℕᵉ WD="taxicabᵉ number"ᵉ WDID=Q1462591ᵉ}}
`taxicabᵉ n`ᵉ isᵉ theᵉ smallestᵉ
[naturalᵉ number](elementary-number-theory.natural-numbers.mdᵉ) `x`ᵉ suchᵉ thatᵉ `x`ᵉ
isᵉ aᵉ [sum](elementary-number-theory.addition-natural-numbers.mdᵉ) ofᵉ twoᵉ
[cubes](elementary-number-theory.cubes-natural-numbers.mdᵉ) in `n`ᵉ
[distinct](foundation.negated-equality.mdᵉ) ways.ᵉ

**Note:**ᵉ Theᵉ definitionᵉ ofᵉ taxicabᵉ numbersᵉ onlyᵉ considersᵉ sumsᵉ ofᵉ
[positiveᵉ integers](elementary-number-theory.nonzero-natural-numbers.md).ᵉ Noteᵉ
thatᵉ ifᵉ `n`ᵉ isᵉ aᵉ cube,ᵉ i.e.,ᵉ ifᵉ `nᵉ ＝ᵉ c³`,ᵉ thenᵉ theᵉ onlyᵉ solutionsᵉ to theᵉ
equationᵉ

```text
  a³ᵉ +ᵉ b³ᵉ = c³ᵉ
```

haveᵉ eitherᵉ `aᵉ ＝ᵉ 0`ᵉ orᵉ `bᵉ ＝ᵉ 0`ᵉ byᵉ
[Fermat'sᵉ lastᵉ theorem](https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem).ᵉ
Thereforeᵉ `n`ᵉ canᵉ beᵉ writtenᵉ in atᵉ leastᵉ twoᵉ differentᵉ waysᵉ asᵉ aᵉ sumᵉ ofᵉ cubesᵉ ofᵉ
positiveᵉ naturalᵉ numbersᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ canᵉ beᵉ writtenᵉ in atᵉ leastᵉ twoᵉ
differentᵉ waysᵉ asᵉ aᵉ sumᵉ ofᵉ cubesᵉ ofᵉ arbitaryᵉ naturalᵉ numbers.ᵉ However,ᵉ theᵉ classᵉ
ofᵉ naturalᵉ numbersᵉ thatᵉ canᵉ beᵉ writtenᵉ in exactlyᵉ oneᵉ wayᵉ asᵉ aᵉ sumᵉ ofᵉ cubesᵉ isᵉ
differentᵉ whenᵉ weᵉ considerᵉ sumsᵉ ofᵉ cubesᵉ ofᵉ positiveᵉ naturalᵉ numbersᵉ orᵉ sumsᵉ ofᵉ
cubesᵉ ofᵉ arbitraryᵉ naturalᵉ numbers.ᵉ

## Definitions

### The type of decompositions of a natural number as a sum of cubes

```agda
sum-of-cubes-decomposition-ℕᵉ : ℕᵉ → UUᵉ lzero
sum-of-cubes-decomposition-ℕᵉ xᵉ =
  Σᵉ ( nonzero-ℕᵉ)
    ( λ yᵉ →
      Σᵉ ( nonzero-ℕᵉ)
        ( λ zᵉ →
          ( leq-ℕᵉ (nat-nonzero-ℕᵉ yᵉ) (nat-nonzero-ℕᵉ zᵉ)) ×ᵉ
          ( cube-ℕᵉ (nat-nonzero-ℕᵉ yᵉ) +ℕᵉ cube-ℕᵉ (nat-nonzero-ℕᵉ zᵉ) ＝ᵉ xᵉ)))
```

### The predicate of being a sum of two cubes in exactly `n` distinct ways

Aᵉ numberᵉ `x`ᵉ isᵉ aᵉ sumᵉ ofᵉ cubesᵉ in `n`ᵉ distinctᵉ waysᵉ ifᵉ thereᵉ isᵉ anᵉ equivalenceᵉ

```text
  Finᵉ nᵉ ≃ᵉ sum-of-cubes-decomposition-ℕᵉ xᵉ
```

fromᵉ theᵉ
[standardᵉ finiteᵉ type](univalent-combinatorics.standard-finite-types.mdᵉ) to theᵉ
typeᵉ `sum-of-cubes-decomposition-ℕᵉ x`ᵉ ofᵉ waysᵉ ofᵉ writingᵉ `x`ᵉ asᵉ aᵉ sumᵉ ofᵉ cubes.ᵉ

```agda
is-sum-of-cubes-in-number-of-distinct-ways-ℕᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
is-sum-of-cubes-in-number-of-distinct-ways-ℕᵉ nᵉ xᵉ =
  Finᵉ nᵉ ≃ᵉ sum-of-cubes-decomposition-ℕᵉ xᵉ
```

### The predicate of being the `n`-th taxicab number

```agda
is-taxicab-number-ℕᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
is-taxicab-number-ℕᵉ nᵉ xᵉ =
  is-sum-of-cubes-in-number-of-distinct-ways-ℕᵉ nᵉ xᵉ ×ᵉ
  ((yᵉ : ℕᵉ) → is-sum-of-cubes-in-number-of-distinct-ways-ℕᵉ nᵉ yᵉ → leq-ℕᵉ xᵉ yᵉ)
```

## See also

-ᵉ [Theᵉ Hardy-Ramanujanᵉ number](elementary-number-theory.hardy-ramanujan-number.mdᵉ)

## External links

-ᵉ [Taxicabᵉ numbers](https://en.wikipedia.org/wiki/Taxicab_numberᵉ) atᵉ Wikipediaᵉ
-ᵉ [Taxicabᵉ nubmers](https://oeis.org/A011541ᵉ) atᵉ theᵉ OEIS.ᵉ