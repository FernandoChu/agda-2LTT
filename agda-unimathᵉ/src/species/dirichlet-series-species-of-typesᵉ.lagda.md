# Dirichlet series of species of types

```agda
module species.dirichlet-series-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-typesᵉ
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

Weᵉ canᵉ generalizeᵉ theᵉ twoᵉ notionsᵉ to speciesᵉ ofᵉ typesᵉ in subuniverses.ᵉ Letᵉ `P`ᵉ
andᵉ `Q`ᵉ twoᵉ subuniverseᵉ suchᵉ thatᵉ `P`ᵉ isᵉ closedᵉ byᵉ cartesianᵉ product.ᵉ Letᵉ
`Hᵉ : Pᵉ → UU`ᵉ beᵉ aᵉ speciesᵉ suchᵉ thatᵉ forᵉ everyᵉ `Xᵉ ,ᵉ Yᵉ : P`ᵉ theᵉ followingᵉ equalityᵉ
isᵉ satisfiedᵉ `Hᵉ (Xᵉ ×ᵉ Yᵉ) ≃ᵉ Hᵉ Xᵉ ×ᵉ Hᵉ Y`.ᵉ Thenᵉ weᵉ canᵉ defineᵉ theᵉ `H`-Dirichletᵉ
seriesᵉ to anyᵉ speciesᵉ ofᵉ subuniverseᵉ `T`ᵉ byᵉ

```text
Σᵉ (Xᵉ : Pᵉ) (Tᵉ (Xᵉ) ×ᵉ (Sᵉ → Hᵉ (Xᵉ)))
```

Theᵉ conditionᵉ onᵉ `H`ᵉ ensureᵉ thatᵉ allᵉ theᵉ usualᵉ propertiesᵉ ofᵉ theᵉ Dirichletᵉ
seriesᵉ areᵉ satisfied.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Hᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (C1ᵉ : preserves-product-species-typesᵉ Hᵉ)
  (Tᵉ : species-typesᵉ l1ᵉ l3ᵉ)
  (Sᵉ : UUᵉ l4ᵉ)
  where

  dirichlet-series-species-typesᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  dirichlet-series-species-typesᵉ = Σᵉ (UUᵉ l1ᵉ) (λ Xᵉ → (Tᵉ Xᵉ) ×ᵉ (Sᵉ → Hᵉ (Xᵉ)))
```