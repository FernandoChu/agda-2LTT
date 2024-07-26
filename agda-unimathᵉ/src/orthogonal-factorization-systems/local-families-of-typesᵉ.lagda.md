# Local families of types

```agda
module orthogonal-factorization-systems.local-families-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.local-typesᵉ
open import orthogonal-factorization-systems.orthogonal-mapsᵉ
```

</details>

## Idea

Aᵉ familyᵉ ofᵉ typesᵉ `Bᵉ : Aᵉ → UUᵉ l`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "local"ᵉ Disambiguation="familyᵉ ofᵉ types"ᵉ Agda=is-local-familyᵉ}} atᵉ
`fᵉ : Xᵉ → Y`,ᵉ orᵉ **`f`-local**,ᵉ ifᵉ everyᵉ
[fiber](foundation-core.fibers-of-maps.mdᵉ) is.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  (fᵉ : Xᵉ → Yᵉ) {Aᵉ : UUᵉ l3ᵉ} (Bᵉ : Aᵉ → UUᵉ l4ᵉ)
  where

  is-local-familyᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-local-familyᵉ = (xᵉ : Aᵉ) → is-localᵉ fᵉ (Bᵉ xᵉ)

  is-property-is-local-familyᵉ : is-propᵉ is-local-familyᵉ
  is-property-is-local-familyᵉ =
    is-prop-Πᵉ (λ xᵉ → is-property-is-equivᵉ (precompᵉ fᵉ (Bᵉ xᵉ)))

  is-local-family-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-local-family-Propᵉ = is-local-familyᵉ
  pr2ᵉ is-local-family-Propᵉ = is-property-is-local-familyᵉ
```

## Properties

### A family is `f`-local if and only if it is `f`-orthogonal

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

## See also

-ᵉ [Localᵉ maps](orthogonal-factorization-systems.local-maps.mdᵉ)
-ᵉ [Localizationsᵉ with respectᵉ to maps](orthogonal-factorization-systems.localizations-maps.mdᵉ)
-ᵉ [Localizationsᵉ with respectᵉ to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.mdᵉ)