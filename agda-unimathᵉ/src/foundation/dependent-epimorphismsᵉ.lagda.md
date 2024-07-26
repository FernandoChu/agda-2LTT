# Dependent epimorphisms

```agda
module foundation.dependent-epimorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.epimorphismsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.precomposition-dependent-functionsᵉ
```

</details>

## Idea

Aᵉ **dependentᵉ epimorphism**ᵉ isᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ suchᵉ thatᵉ theᵉ
[precompositionᵉ function](foundation.precomposition-dependent-functions.mdᵉ)

```text
  -ᵉ ∘ᵉ fᵉ : ((bᵉ : Bᵉ) → Cᵉ bᵉ) → ((aᵉ : Aᵉ) → Cᵉ (fᵉ aᵉ))
```

isᵉ anᵉ [embedding](foundation-core.embeddings.mdᵉ) forᵉ everyᵉ typeᵉ familyᵉ `C`ᵉ overᵉ
`B`.ᵉ

Clearly,ᵉ everyᵉ dependentᵉ epimorphismᵉ isᵉ anᵉ
[epimorphism](foundation.epimorphisms.md).ᵉ Theᵉ converseᵉ isᵉ alsoᵉ true,ᵉ i.e.,ᵉ
everyᵉ epimorphismᵉ isᵉ aᵉ dependentᵉ epimorphism.ᵉ Thereforeᵉ itᵉ followsᵉ thatᵉ aᵉ mapᵉ
`fᵉ : Aᵉ → B`ᵉ isᵉ [acyclic](synthetic-homotopy-theory.acyclic-maps.mdᵉ) ifᵉ andᵉ onlyᵉ
ifᵉ itᵉ isᵉ anᵉ epimorphism,ᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ aᵉ dependentᵉ epimorphism.ᵉ

## Definitions

### The predicate of being a dependent epimorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-dependent-epimorphismᵉ : (Aᵉ → Bᵉ) → UUωᵉ
  is-dependent-epimorphismᵉ fᵉ =
    {lᵉ : Level} (Cᵉ : Bᵉ → UUᵉ lᵉ) → is-embᵉ (precomp-Πᵉ fᵉ Cᵉ)
```

## Properties

### Every dependent epimorphism is an epimorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-epimorphism-is-dependent-epimorphismᵉ :
    is-dependent-epimorphismᵉ fᵉ → is-epimorphismᵉ fᵉ
  is-epimorphism-is-dependent-epimorphismᵉ eᵉ Xᵉ = eᵉ (λ _ → Xᵉ)
```

Theᵉ converseᵉ ofᵉ theᵉ above,ᵉ thatᵉ everyᵉ epimorphismᵉ isᵉ aᵉ dependentᵉ epimorphism,ᵉ
canᵉ beᵉ foundᵉ in theᵉ fileᵉ onᵉ
[acyclicᵉ maps](synthetic-homotopy-theory.acyclic-maps.md).ᵉ

## See also

-ᵉ [Acyclicᵉ maps](synthetic-homotopy-theory.acyclic-maps.mdᵉ)
-ᵉ [Epimorphisms](foundation.epimorphisms.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to sets](foundation.epimorphisms-with-respect-to-sets.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to truncatedᵉ types](foundation.epimorphisms-with-respect-to-truncated-types.mdᵉ)