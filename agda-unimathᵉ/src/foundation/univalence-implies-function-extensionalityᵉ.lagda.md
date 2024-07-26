# The univalence axiom implies function extensionality

```agda
module foundation.univalence-implies-function-extensionalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-inductionᵉ
open import foundation.function-extensionalityᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.weak-function-extensionalityᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Theᵉ [univalenceᵉ axiom](foundation-core.univalence.mdᵉ) impliesᵉ
[functionᵉ extensionality](foundation.function-extensionality.md).ᵉ

## Theorem

```agda
abstract
  weak-funext-univalenceᵉ : {lᵉ : Level} → weak-function-extensionality-Levelᵉ lᵉ lᵉ
  weak-funext-univalenceᵉ Aᵉ Bᵉ is-contr-Bᵉ =
    is-contr-retract-ofᵉ
      ( fiberᵉ (postcompᵉ Aᵉ pr1ᵉ) idᵉ)
      ( ( λ fᵉ → ((λ xᵉ → (xᵉ ,ᵉ fᵉ xᵉ)) ,ᵉ reflᵉ)) ,ᵉ
        ( λ hᵉ xᵉ → trᵉ Bᵉ (htpy-eqᵉ (pr2ᵉ hᵉ) xᵉ) (pr2ᵉ (pr1ᵉ hᵉ xᵉ))) ,ᵉ
        ( refl-htpyᵉ))
      ( is-contr-map-is-equivᵉ
        ( is-equiv-postcomp-univalenceᵉ Aᵉ (equiv-pr1ᵉ is-contr-Bᵉ))
        ( idᵉ))

abstract
  funext-univalenceᵉ :
    {lᵉ : Level} → function-extensionality-Levelᵉ lᵉ lᵉ
  funext-univalenceᵉ fᵉ = funext-weak-funextᵉ weak-funext-univalenceᵉ fᵉ
```