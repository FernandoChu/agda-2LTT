# Dirichlet series of species of finite inhabited types

```agda
module species.dirichlet-series-species-of-finite-inhabited-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-finite-inhabited-typesᵉ

open import univalent-combinatorics.cycle-prime-decomposition-natural-numbersᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.inhabited-finite-typesᵉ
```

</details>

## Idea

Inᵉ classicalᵉ mathematics,ᵉ theᵉ Dirichletᵉ seriesᵉ ofᵉ aᵉ speciesᵉ ofᵉ finiteᵉ inhabitedᵉ
typesᵉ `T`ᵉ isᵉ theᵉ formalᵉ seriesᵉ in `s`ᵉ :

```text
Σᵉ (nᵉ : ℕ∖{0ᵉ}) (|T({1,...,n}|ᵉ n^(-sᵉ) /ᵉ n!ᵉ))
```

Ifᵉ `s`ᵉ isᵉ aᵉ negativeᵉ integer,ᵉ theᵉ categorifiedᵉ versionᵉ ofᵉ thisᵉ formulaᵉ isᵉ

```text
Σᵉ (Fᵉ : 𝔽ᵉ ∖ᵉ {∅}),ᵉ Tᵉ (Fᵉ) ×ᵉ (Sᵉ → Fᵉ)
```

Weᵉ canᵉ generalizeᵉ itᵉ to speciesᵉ ofᵉ typesᵉ asᵉ

```text
Σᵉ (Uᵉ : UUᵉ) (Tᵉ (Uᵉ) ×ᵉ (Sᵉ → Uᵉ))
```

Theᵉ interestingᵉ caseᵉ isᵉ whenᵉ `s`ᵉ isᵉ aᵉ positiveᵉ number.ᵉ Theᵉ categorifiedᵉ versionᵉ
ofᵉ thisᵉ formulaᵉ thenᵉ becomesᵉ

```text
Σᵉ ( nᵉ : ℕᵉ ∖ᵉ {0}),ᵉ
  ( Σᵉ (Fᵉ : UU-Finᵉ nᵉ) ,ᵉ Tᵉ (Fᵉ) ×ᵉ (Sᵉ → cycle-prime-decomposition-ℕᵉ (nᵉ))
```

Weᵉ haveᵉ pickedᵉ theᵉ concreteᵉ groupᵉ `cycle-prime-decomposition-ℕᵉ (n)`ᵉ becauseᵉ itᵉ
isᵉ closedᵉ underᵉ cartesianᵉ productᵉ andᵉ alsoᵉ becauseᵉ itsᵉ groupoidᵉ cardinalityᵉ isᵉ
equalᵉ to `1/n`.ᵉ

## Definition

```agda
dirichlet-series-species-Inhabited-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} → species-Inhabited-𝔽ᵉ l1ᵉ l2ᵉ → UUᵉ l3ᵉ →
  UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
dirichlet-series-species-Inhabited-𝔽ᵉ {l1ᵉ} Tᵉ Sᵉ =
  Σᵉ ( ℕᵉ)
    ( λ nᵉ →
      Σᵉ ( UU-Finᵉ l1ᵉ (succ-ℕᵉ nᵉ))
        ( λ Fᵉ →
          type-𝔽ᵉ
            ( Tᵉ
              ( type-UU-Finᵉ (succ-ℕᵉ nᵉ) Fᵉ ,ᵉ
                is-finite-and-inhabited-type-UU-Fin-succ-ℕᵉ nᵉ Fᵉ)) ×ᵉ
          Sᵉ → cycle-prime-decomposition-ℕᵉ (succ-ℕᵉ nᵉ) _))
```