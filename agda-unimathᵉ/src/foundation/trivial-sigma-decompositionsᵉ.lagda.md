# Trivial Σ-decompositions

```agda
module foundation.trivial-sigma-decompositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.inhabited-typesᵉ
open import foundation.sigma-decompositionsᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.empty-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Definitions

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ)
  where

  trivial-inhabited-Σ-Decompositionᵉ :
    (pᵉ : is-inhabitedᵉ Aᵉ) → Σ-Decompositionᵉ l2ᵉ l1ᵉ Aᵉ
  pr1ᵉ (trivial-inhabited-Σ-Decompositionᵉ pᵉ) = raise-unitᵉ l2ᵉ
  pr1ᵉ (pr2ᵉ (trivial-inhabited-Σ-Decompositionᵉ pᵉ)) = λ _ → (Aᵉ ,ᵉ pᵉ)
  pr2ᵉ (pr2ᵉ (trivial-inhabited-Σ-Decompositionᵉ pᵉ)) =
    inv-left-unit-law-Σ-is-contrᵉ
      ( is-contr-raise-unitᵉ)
      ( raise-starᵉ)

  trivial-empty-Σ-Decompositionᵉ :
    (pᵉ : is-emptyᵉ Aᵉ) → Σ-Decompositionᵉ lzero lzero Aᵉ
  pr1ᵉ (trivial-empty-Σ-Decompositionᵉ pᵉ) = emptyᵉ
  pr1ᵉ (pr2ᵉ (trivial-empty-Σ-Decompositionᵉ pᵉ)) = ex-falsoᵉ
  pr2ᵉ (pr2ᵉ (trivial-empty-Σ-Decompositionᵉ pᵉ)) =
    equiv-is-emptyᵉ
      ( pᵉ)
      ( map-left-absorption-Σᵉ _)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Dᵉ : Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  is-trivial-Prop-Σ-Decompositionᵉ : Propᵉ l2ᵉ
  is-trivial-Prop-Σ-Decompositionᵉ =
    is-contr-Propᵉ (indexing-type-Σ-Decompositionᵉ Dᵉ)

  is-trivial-Σ-Decompositionᵉ : UUᵉ l2ᵉ
  is-trivial-Σ-Decompositionᵉ = type-Propᵉ is-trivial-Prop-Σ-Decompositionᵉ

is-trivial-trivial-inhabited-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (pᵉ : is-inhabitedᵉ Aᵉ) →
  is-trivial-Σ-Decompositionᵉ (trivial-inhabited-Σ-Decompositionᵉ l2ᵉ Aᵉ pᵉ)
is-trivial-trivial-inhabited-Σ-Decompositionᵉ pᵉ = is-contr-raise-unitᵉ

type-trivial-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
type-trivial-Σ-Decompositionᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Aᵉ} =
  type-subtypeᵉ (is-trivial-Prop-Σ-Decompositionᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Aᵉ})
```

## Propositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Dᵉ : Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  ( is-trivialᵉ : is-trivial-Σ-Decompositionᵉ Dᵉ)
  where

  is-inhabited-base-type-is-trivial-Σ-Decompositionᵉ :
    is-inhabitedᵉ Aᵉ
  is-inhabited-base-type-is-trivial-Σ-Decompositionᵉ =
    map-equiv-trunc-Propᵉ
      ( inv-equivᵉ (matching-correspondence-Σ-Decompositionᵉ Dᵉ) ∘eᵉ
        inv-left-unit-law-Σ-is-contrᵉ is-trivialᵉ ( centerᵉ is-trivialᵉ))
      ( is-inhabited-cotype-Σ-Decompositionᵉ Dᵉ ( centerᵉ is-trivialᵉ))

  equiv-trivial-is-trivial-Σ-Decompositionᵉ :
    equiv-Σ-Decompositionᵉ Dᵉ
      ( trivial-inhabited-Σ-Decompositionᵉ
        ( l4ᵉ)
        ( Aᵉ)
        ( is-inhabited-base-type-is-trivial-Σ-Decompositionᵉ))
  pr1ᵉ equiv-trivial-is-trivial-Σ-Decompositionᵉ =
    ( map-equivᵉ (compute-raise-unitᵉ l4ᵉ) ∘ᵉ
      terminal-mapᵉ (indexing-type-Σ-Decompositionᵉ Dᵉ) ,ᵉ
      is-equiv-compᵉ
        ( map-equivᵉ (compute-raise-unitᵉ l4ᵉ))
        ( terminal-mapᵉ (indexing-type-Σ-Decompositionᵉ Dᵉ))
        ( is-equiv-terminal-map-is-contrᵉ is-trivialᵉ)
        ( is-equiv-map-equivᵉ ( compute-raise-unitᵉ l4ᵉ)))
  pr1ᵉ (pr2ᵉ equiv-trivial-is-trivial-Σ-Decompositionᵉ) =
    ( λ xᵉ →
      ( ( inv-equivᵉ (matching-correspondence-Σ-Decompositionᵉ Dᵉ)) ∘eᵉ
        ( inv-left-unit-law-Σ-is-contrᵉ is-trivialᵉ xᵉ)))
  pr2ᵉ (pr2ᵉ equiv-trivial-is-trivial-Σ-Decompositionᵉ) aᵉ =
    eq-pair-eq-fiberᵉ
      ( map-inv-eq-transpose-equivᵉ
        ( inv-equivᵉ (matching-correspondence-Σ-Decompositionᵉ Dᵉ))
        ( reflᵉ))

is-contr-type-trivial-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  (pᵉ : is-inhabitedᵉ Aᵉ) →
  is-contrᵉ (type-trivial-Σ-Decompositionᵉ {l1ᵉ} {l2ᵉ} {l1ᵉ} {Aᵉ})
pr1ᵉ ( is-contr-type-trivial-Σ-Decompositionᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} pᵉ) =
  ( trivial-inhabited-Σ-Decompositionᵉ l2ᵉ Aᵉ pᵉ ,ᵉ
    is-trivial-trivial-inhabited-Σ-Decompositionᵉ pᵉ)
pr2ᵉ ( is-contr-type-trivial-Σ-Decompositionᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} pᵉ) xᵉ =
  eq-type-subtypeᵉ
    ( is-trivial-Prop-Σ-Decompositionᵉ)
    ( invᵉ
      ( eq-equiv-Σ-Decompositionᵉ
        ( pr1ᵉ xᵉ)
        ( trivial-inhabited-Σ-Decompositionᵉ l2ᵉ Aᵉ pᵉ)
        ( equiv-trivial-is-trivial-Σ-Decompositionᵉ (pr1ᵉ xᵉ) (pr2ᵉ xᵉ))))
```