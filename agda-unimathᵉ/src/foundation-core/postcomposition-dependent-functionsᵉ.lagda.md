# Postcomposition of dependent functions

```agda
module foundation-core.postcomposition-dependent-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ `A`ᵉ andᵉ aᵉ familyᵉ ofᵉ mapsᵉ `fᵉ : {aᵉ : Aᵉ} → Xᵉ aᵉ → Yᵉ a`,ᵉ theᵉ
{{#conceptᵉ "postcompositionᵉ function"ᵉ Disambiguation="ofᵉ dependentᵉ functionsᵉ byᵉ aᵉ familyᵉ ofᵉ maps"ᵉ Agda=postcomp-Πᵉ}}
ofᵉ dependentᵉ functionsᵉ `(aᵉ : Aᵉ) → Xᵉ a`ᵉ byᵉ theᵉ familyᵉ ofᵉ mapsᵉ `f`ᵉ

```text
  postcomp-Πᵉ Aᵉ fᵉ : ((aᵉ : Aᵉ) → Xᵉ aᵉ) → ((aᵉ : Aᵉ) → Yᵉ aᵉ)
```

isᵉ definedᵉ byᵉ `λᵉ hᵉ xᵉ → fᵉ (hᵉ x)`.ᵉ

Noteᵉ that,ᵉ sinceᵉ theᵉ definitionᵉ ofᵉ theᵉ familyᵉ ofᵉ mapsᵉ `f`ᵉ dependsᵉ onᵉ theᵉ baseᵉ
`A`,ᵉ postcompositionᵉ ofᵉ dependentᵉ functionsᵉ doesᵉ notᵉ generalizeᵉ
[postcompositionᵉ ofᵉ functions](foundation-core.postcomposition-functions.mdᵉ) in
theᵉ sameᵉ wayᵉ thatᵉ
[precompositionᵉ ofᵉ dependentᵉ functions](foundation-core.precomposition-dependent-functions.mdᵉ)
generalizesᵉ
[precompositionᵉ ofᵉ functions](foundation-core.precomposition-functions.md).ᵉ Ifᵉ
`A`ᵉ canᵉ varyᵉ whileᵉ keepingᵉ `f`ᵉ fixed,ᵉ weᵉ haveᵉ necessarilyᵉ reducedᵉ to theᵉ caseᵉ ofᵉ
[postcompositionᵉ ofᵉ functions](foundation-core.postcomposition-functions.md).ᵉ

## Definitions

### Postcomposition of dependent functions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) {Xᵉ : Aᵉ → UUᵉ l2ᵉ} {Yᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  postcomp-Πᵉ : ({aᵉ : Aᵉ} → Xᵉ aᵉ → Yᵉ aᵉ) → ((aᵉ : Aᵉ) → Xᵉ aᵉ) → ((aᵉ : Aᵉ) → Yᵉ aᵉ)
  postcomp-Πᵉ fᵉ = fᵉ ∘ᵉ_
```