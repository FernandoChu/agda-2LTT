# Dependent epimorphisms with respect to truncated types

```agda
module foundation.dependent-epimorphisms-with-respect-to-truncated-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.epimorphisms-with-respect-to-truncated-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.precomposition-dependent-functionsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Aᵉ **dependentᵉ `k`-epimorphism**ᵉ isᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ suchᵉ thatᵉ theᵉ
[precompositionᵉ function](foundation.precomposition-dependent-functions.mdᵉ)

```text
  -ᵉ ∘ᵉ fᵉ : ((bᵉ : Bᵉ) → Cᵉ bᵉ) → ((aᵉ : Aᵉ) → Cᵉ (fᵉ aᵉ))
```

isᵉ anᵉ [embedding](foundation-core.embeddings.mdᵉ) forᵉ everyᵉ familyᵉ `C`ᵉ ofᵉ
[`k`-types](foundation.truncated-types.mdᵉ) overᵉ `B`.ᵉ

Clearly,ᵉ everyᵉ dependentᵉ `k`-epimorphismᵉ isᵉ aᵉ
[`k`-epimorphism](foundation.epimorphisms-with-respect-to-truncated-types.md).ᵉ
Theᵉ converseᵉ isᵉ alsoᵉ true,ᵉ i.e.,ᵉ everyᵉ `k`-epimorphismᵉ isᵉ aᵉ dependentᵉ
`k`-epimorphism.ᵉ Thereforeᵉ itᵉ followsᵉ thatᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ
[`k`-acyclic](synthetic-homotopy-theory.truncated-acyclic-maps.mdᵉ) ifᵉ andᵉ onlyᵉ
ifᵉ itᵉ isᵉ aᵉ `k`-epimorphism,ᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ aᵉ dependentᵉ `k`-epimorphism.ᵉ

## Definitions

### The predicate of being a dependent `k`-epimorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-dependent-epimorphism-Truncated-Typeᵉ : (Aᵉ → Bᵉ) → UUωᵉ
  is-dependent-epimorphism-Truncated-Typeᵉ fᵉ =
    {lᵉ : Level} (Cᵉ : Bᵉ → Truncated-Typeᵉ lᵉ kᵉ) →
    is-embᵉ (precomp-Πᵉ fᵉ (λ bᵉ → type-Truncated-Typeᵉ (Cᵉ bᵉ)))
```

## Properties

### Every dependent `k`-epimorphism is a `k`-epimorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-epimorphism-is-dependent-epimorphism-Truncated-Typeᵉ :
    is-dependent-epimorphism-Truncated-Typeᵉ kᵉ fᵉ →
    is-epimorphism-Truncated-Typeᵉ kᵉ fᵉ
  is-epimorphism-is-dependent-epimorphism-Truncated-Typeᵉ eᵉ Xᵉ = eᵉ (λ _ → Xᵉ)
```

Theᵉ converseᵉ ofᵉ theᵉ above,ᵉ thatᵉ everyᵉ `k`-epimorphismᵉ isᵉ aᵉ dependentᵉ
`k`-epimorphism,ᵉ canᵉ beᵉ foundᵉ in theᵉ fileᵉ onᵉ
[`k`-acyclicᵉ maps](synthetic-homotopy-theory.truncated-acyclic-maps.md).ᵉ

## See also

-ᵉ [`k`-acyclicᵉ maps](synthetic-homotopy-theory.truncated-acyclic-maps.mdᵉ)
-ᵉ [Epimorphisms](foundation.epimorphisms.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to sets](foundation.epimorphisms-with-respect-to-sets.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to truncatedᵉ types](foundation.epimorphisms-with-respect-to-truncated-types.mdᵉ)