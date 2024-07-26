# Finite trivial Σ-decompositions

```agda
module univalent-combinatorics.trivial-sigma-decompositionsᵉ where

open import foundation.trivial-sigma-decompositionsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-typesᵉ
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

  trivial-inhabited-Σ-Decomposition-𝔽ᵉ :
    (pᵉ : is-inhabitedᵉ (type-𝔽ᵉ Aᵉ)) → Σ-Decomposition-𝔽ᵉ l2ᵉ l1ᵉ Aᵉ
  trivial-inhabited-Σ-Decomposition-𝔽ᵉ pᵉ =
    map-Σ-Decomposition-𝔽-subtype-is-finiteᵉ
      ( Aᵉ)
      ( ( trivial-inhabited-Σ-Decompositionᵉ l2ᵉ (type-𝔽ᵉ Aᵉ) pᵉ) ,ᵉ
        ( is-finite-raise-unitᵉ ,ᵉ λ xᵉ → is-finite-type-𝔽ᵉ Aᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ)
  (Dᵉ : Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  is-trivial-Prop-Σ-Decomposition-𝔽ᵉ :
    Propᵉ l2ᵉ
  is-trivial-Prop-Σ-Decomposition-𝔽ᵉ =
    is-contr-Propᵉ (indexing-type-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ)

  is-trivial-Σ-Decomposition-𝔽ᵉ :
    UUᵉ (l2ᵉ)
  is-trivial-Σ-Decomposition-𝔽ᵉ =
    type-Propᵉ (is-trivial-Prop-Σ-Decomposition-𝔽ᵉ)

is-trivial-trivial-inhabited-Σ-Decomposition-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) (pᵉ : is-inhabitedᵉ (type-𝔽ᵉ Aᵉ)) →
  is-trivial-Σ-Decomposition-𝔽ᵉ
    ( Aᵉ)
    ( trivial-inhabited-Σ-Decomposition-𝔽ᵉ l2ᵉ Aᵉ pᵉ)
is-trivial-trivial-inhabited-Σ-Decomposition-𝔽ᵉ Aᵉ pᵉ =
  is-trivial-trivial-inhabited-Σ-Decompositionᵉ pᵉ

type-trivial-Σ-Decomposition-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
type-trivial-Σ-Decomposition-𝔽ᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} Aᵉ =
  type-subtypeᵉ (is-trivial-Prop-Σ-Decomposition-𝔽ᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} Aᵉ)
```

## Propositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ)
  (Dᵉ : Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ)
  (is-trivialᵉ : is-trivial-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ)
  where

  equiv-trivial-is-trivial-Σ-Decomposition-𝔽ᵉ :
    equiv-Σ-Decomposition-𝔽ᵉ
      ( Aᵉ)
      ( Dᵉ)
      ( trivial-inhabited-Σ-Decomposition-𝔽ᵉ
        ( l4ᵉ)
        ( Aᵉ)
        ( is-inhabited-base-type-is-trivial-Σ-Decompositionᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} {l4ᵉ}
          ( Σ-Decomposition-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ)
          ( is-trivialᵉ)))
  equiv-trivial-is-trivial-Σ-Decomposition-𝔽ᵉ =
    equiv-trivial-is-trivial-Σ-Decompositionᵉ
      ( Σ-Decomposition-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ)
      ( is-trivialᵉ)

is-contr-type-trivial-Σ-Decomposition-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) → (pᵉ : is-inhabitedᵉ (type-𝔽ᵉ Aᵉ)) →
  is-contrᵉ (type-trivial-Σ-Decomposition-𝔽ᵉ {l1ᵉ} {l2ᵉ} {l1ᵉ} Aᵉ)
pr1ᵉ ( is-contr-type-trivial-Σ-Decomposition-𝔽ᵉ {l1ᵉ} {l2ᵉ} Aᵉ pᵉ) =
  ( trivial-inhabited-Σ-Decomposition-𝔽ᵉ l2ᵉ Aᵉ pᵉ ,ᵉ
    is-trivial-trivial-inhabited-Σ-Decomposition-𝔽ᵉ Aᵉ pᵉ)
pr2ᵉ ( is-contr-type-trivial-Σ-Decomposition-𝔽ᵉ {l1ᵉ} {l2ᵉ} Aᵉ pᵉ) xᵉ =
  eq-type-subtypeᵉ
    ( is-trivial-Prop-Σ-Decomposition-𝔽ᵉ Aᵉ)
    ( invᵉ
      ( eq-equiv-Σ-Decomposition-𝔽ᵉ
        ( Aᵉ)
        ( pr1ᵉ xᵉ)
        ( trivial-inhabited-Σ-Decomposition-𝔽ᵉ l2ᵉ Aᵉ pᵉ)
        ( equiv-trivial-is-trivial-Σ-Decomposition-𝔽ᵉ Aᵉ (pr1ᵉ xᵉ) (pr2ᵉ xᵉ))))
```