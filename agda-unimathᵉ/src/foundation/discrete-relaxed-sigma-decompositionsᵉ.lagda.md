# Discrete relaxed Σ-decompositions

```agda
module foundation.discrete-relaxed-sigma-decompositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.relaxed-sigma-decompositionsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Definition

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ)
  where

  discrete-Relaxed-Σ-Decompositionᵉ :
    Relaxed-Σ-Decompositionᵉ l1ᵉ l2ᵉ Aᵉ
  pr1ᵉ discrete-Relaxed-Σ-Decompositionᵉ = Aᵉ
  pr1ᵉ (pr2ᵉ discrete-Relaxed-Σ-Decompositionᵉ) aᵉ = raise-unitᵉ l2ᵉ
  pr2ᵉ (pr2ᵉ discrete-Relaxed-Σ-Decompositionᵉ) =
    inv-equivᵉ
      ( equiv-pr1ᵉ
        ( λ _ →
          is-contr-raise-unitᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Dᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  is-discrete-Prop-Relaxed-Σ-Decompositionᵉ : Propᵉ (l2ᵉ ⊔ l3ᵉ)
  is-discrete-Prop-Relaxed-Σ-Decompositionᵉ =
    Π-Propᵉ
      ( indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ)
      ( λ xᵉ → is-contr-Propᵉ (cotype-Relaxed-Σ-Decompositionᵉ Dᵉ xᵉ))

  is-discrete-Relaxed-Σ-Decompositionᵉ :
    UUᵉ (l2ᵉ ⊔ l3ᵉ)
  is-discrete-Relaxed-Σ-Decompositionᵉ =
    type-Propᵉ (is-discrete-Prop-Relaxed-Σ-Decompositionᵉ)

is-discrete-discrete-Relaxed-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  is-discrete-Relaxed-Σ-Decompositionᵉ (discrete-Relaxed-Σ-Decompositionᵉ l2ᵉ Aᵉ)
is-discrete-discrete-Relaxed-Σ-Decompositionᵉ = λ xᵉ → is-contr-raise-unitᵉ

type-discrete-Relaxed-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
type-discrete-Relaxed-Σ-Decompositionᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Aᵉ} =
  type-subtypeᵉ (is-discrete-Prop-Relaxed-Σ-Decompositionᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Aᵉ})
```

## Propositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Dᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  (is-discreteᵉ : is-discrete-Relaxed-Σ-Decompositionᵉ Dᵉ)
  where

  equiv-discrete-is-discrete-Relaxed-Σ-Decompositionᵉ :
    equiv-Relaxed-Σ-Decompositionᵉ Dᵉ (discrete-Relaxed-Σ-Decompositionᵉ l4ᵉ Aᵉ)
  pr1ᵉ equiv-discrete-is-discrete-Relaxed-Σ-Decompositionᵉ =
    ( inv-equivᵉ
      ( right-unit-law-Σ-is-contrᵉ is-discreteᵉ ∘eᵉ
        matching-correspondence-Relaxed-Σ-Decompositionᵉ Dᵉ))
  pr1ᵉ (pr2ᵉ equiv-discrete-is-discrete-Relaxed-Σ-Decompositionᵉ) xᵉ =
    ( map-equivᵉ (compute-raise-unitᵉ l4ᵉ) ∘ᵉ
      terminal-mapᵉ (cotype-Relaxed-Σ-Decompositionᵉ Dᵉ xᵉ) ,ᵉ
      is-equiv-compᵉ
        ( map-equivᵉ (compute-raise-unitᵉ l4ᵉ))
        ( terminal-mapᵉ (cotype-Relaxed-Σ-Decompositionᵉ Dᵉ xᵉ))
        ( is-equiv-terminal-map-is-contrᵉ (is-discreteᵉ xᵉ))
        ( is-equiv-map-equivᵉ ( compute-raise-unitᵉ l4ᵉ)))
  pr2ᵉ (pr2ᵉ equiv-discrete-is-discrete-Relaxed-Σ-Decompositionᵉ) aᵉ =
    eq-pair-Σᵉ
      ( apᵉ ( λ fᵉ → map-equivᵉ fᵉ aᵉ)
        ( ( left-inverse-law-equivᵉ
            ( equiv-pr1ᵉ is-discreteᵉ ∘eᵉ
              matching-correspondence-Relaxed-Σ-Decompositionᵉ Dᵉ)) ∙ᵉ
        ( ( invᵉ
            ( right-inverse-law-equivᵉ
              ( equiv-pr1ᵉ ( λ _ → is-contr-raise-unitᵉ)))))))
      ( eq-is-contrᵉ is-contr-raise-unitᵉ)

is-contr-type-discrete-Relaxed-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  is-contrᵉ (type-discrete-Relaxed-Σ-Decompositionᵉ {l1ᵉ} {l1ᵉ} {l2ᵉ} {Aᵉ})
pr1ᵉ ( is-contr-type-discrete-Relaxed-Σ-Decompositionᵉ {l1ᵉ} {l2ᵉ} {Aᵉ}) =
  ( discrete-Relaxed-Σ-Decompositionᵉ l2ᵉ Aᵉ ,ᵉ
    is-discrete-discrete-Relaxed-Σ-Decompositionᵉ)
pr2ᵉ ( is-contr-type-discrete-Relaxed-Σ-Decompositionᵉ {l1ᵉ} {l2ᵉ} {Aᵉ}) =
  ( λ xᵉ →
    eq-type-subtypeᵉ
      ( is-discrete-Prop-Relaxed-Σ-Decompositionᵉ)
      ( invᵉ
        ( eq-equiv-Relaxed-Σ-Decompositionᵉ
          ( pr1ᵉ xᵉ)
          ( discrete-Relaxed-Σ-Decompositionᵉ l2ᵉ Aᵉ)
          ( equiv-discrete-is-discrete-Relaxed-Σ-Decompositionᵉ
            ( pr1ᵉ xᵉ)
            ( pr2ᵉ xᵉ)))))
```