# The double negation modality

```agda
module foundation.double-negation-modalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.double-negationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.transport-along-identificationsᵉ

open import orthogonal-factorization-systems.local-typesᵉ
open import orthogonal-factorization-systems.modal-operatorsᵉ
open import orthogonal-factorization-systems.uniquely-eliminating-modalitiesᵉ
```

</details>

## Idea

Theᵉ [doubleᵉ negation](foundation.double-negation.mdᵉ) operationᵉ `¬¬`ᵉ isᵉ aᵉ
[modality](orthogonal-factorization-systems.higher-modalities.md).ᵉ

## Definition

### The double negation modality

```agda
operator-double-negation-modalityᵉ :
  (lᵉ : Level) → operator-modalityᵉ lᵉ lᵉ
operator-double-negation-modalityᵉ _ = ¬¬ᵉ_

unit-double-negation-modalityᵉ :
  {lᵉ : Level} → unit-modalityᵉ (operator-double-negation-modalityᵉ lᵉ)
unit-double-negation-modalityᵉ = intro-double-negationᵉ
```

## Properties

### The double negation modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-double-negation-modalityᵉ :
  {lᵉ : Level} →
  is-uniquely-eliminating-modalityᵉ (unit-double-negation-modalityᵉ {lᵉ})
is-uniquely-eliminating-modality-double-negation-modalityᵉ {lᵉ} {Aᵉ} Pᵉ =
  is-local-dependent-type-is-propᵉ
    ( unit-double-negation-modalityᵉ)
    ( operator-double-negation-modalityᵉ lᵉ ∘ᵉ Pᵉ)
    ( λ _ → is-prop-double-negationᵉ)
    ( λ fᵉ zᵉ →
      double-negation-extendᵉ
        ( λ (aᵉ : Aᵉ) →
          trᵉ
            ( ¬¬ᵉ_ ∘ᵉ Pᵉ)
            ( eq-is-propᵉ is-prop-double-negationᵉ)
            ( fᵉ aᵉ))
        ( zᵉ))
```

Thisᵉ proofᵉ followsᵉ Exampleᵉ 1.9ᵉ in {{#citeᵉ RSS20}}.ᵉ

## References

{{#bibliographyᵉ}}