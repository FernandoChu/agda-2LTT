# Finite discrete Σ-decompositions

```agda
module univalent-combinatorics.discrete-sigma-decompositionsᵉ where

open import foundation.discrete-sigma-decompositionsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.sigma-decompositionsᵉ
```

</details>

## Definitions

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : 𝔽ᵉ l1ᵉ)
  where

  discrete-Σ-Decomposition-𝔽ᵉ :
    Σ-Decomposition-𝔽ᵉ l1ᵉ l2ᵉ Aᵉ
  discrete-Σ-Decomposition-𝔽ᵉ =
    map-Σ-Decomposition-𝔽-subtype-is-finiteᵉ
      ( Aᵉ)
      ( ( discrete-Σ-Decompositionᵉ l2ᵉ (type-𝔽ᵉ Aᵉ)) ,ᵉ
        ( is-finite-type-𝔽ᵉ Aᵉ ,ᵉ
          λ xᵉ → is-finite-raise-unitᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ)
  (Dᵉ : Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  is-discrete-Prop-Σ-Decomposition-𝔽ᵉ :
    Propᵉ (l2ᵉ ⊔ l3ᵉ)
  is-discrete-Prop-Σ-Decomposition-𝔽ᵉ =
    Π-Propᵉ
      ( indexing-type-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ)
      ( λ xᵉ → is-contr-Propᵉ (cotype-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ xᵉ))

  is-discrete-Σ-Decomposition-𝔽ᵉ :
    UUᵉ (l2ᵉ ⊔ l3ᵉ)
  is-discrete-Σ-Decomposition-𝔽ᵉ =
    type-Propᵉ is-discrete-Prop-Σ-Decomposition-𝔽ᵉ

is-discrete-discrete-Σ-Decomposition-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) →
  is-discrete-Σ-Decomposition-𝔽ᵉ
    ( Aᵉ)
    ( discrete-Σ-Decomposition-𝔽ᵉ l2ᵉ Aᵉ)
is-discrete-discrete-Σ-Decomposition-𝔽ᵉ _ =
  is-discrete-discrete-Σ-Decompositionᵉ

type-discrete-Σ-Decomposition-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
type-discrete-Σ-Decomposition-𝔽ᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} Aᵉ =
  type-subtypeᵉ (is-discrete-Prop-Σ-Decomposition-𝔽ᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} Aᵉ)
```

## Propositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ)
  (Dᵉ : Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ)
  ( is-discreteᵉ : is-discrete-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ)
  where

  equiv-discrete-is-discrete-Σ-Decomposition-𝔽ᵉ :
    equiv-Σ-Decomposition-𝔽ᵉ
      ( Aᵉ)
      ( Dᵉ)
      ( discrete-Σ-Decomposition-𝔽ᵉ
        ( l4ᵉ)
        ( Aᵉ))
  equiv-discrete-is-discrete-Σ-Decomposition-𝔽ᵉ =
    equiv-discrete-is-discrete-Σ-Decompositionᵉ
      ( Σ-Decomposition-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ)
      ( is-discreteᵉ)

is-contr-type-discrete-Σ-Decomposition-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) →
  is-contrᵉ (type-discrete-Σ-Decomposition-𝔽ᵉ {l1ᵉ} {l1ᵉ} {l2ᵉ} Aᵉ)
pr1ᵉ ( is-contr-type-discrete-Σ-Decomposition-𝔽ᵉ {l1ᵉ} {l2ᵉ} Aᵉ) =
  ( discrete-Σ-Decomposition-𝔽ᵉ l2ᵉ Aᵉ ,ᵉ
    is-discrete-discrete-Σ-Decomposition-𝔽ᵉ Aᵉ)
pr2ᵉ ( is-contr-type-discrete-Σ-Decomposition-𝔽ᵉ {l1ᵉ} {l2ᵉ} Aᵉ) =
  ( λ xᵉ →
    eq-type-subtypeᵉ
      ( is-discrete-Prop-Σ-Decomposition-𝔽ᵉ Aᵉ)
      ( invᵉ
        ( eq-equiv-Σ-Decomposition-𝔽ᵉ
          ( Aᵉ)
          ( pr1ᵉ xᵉ)
          ( discrete-Σ-Decomposition-𝔽ᵉ l2ᵉ Aᵉ)
          ( equiv-discrete-is-discrete-Σ-Decomposition-𝔽ᵉ Aᵉ (pr1ᵉ xᵉ) (pr2ᵉ xᵉ)))))
```