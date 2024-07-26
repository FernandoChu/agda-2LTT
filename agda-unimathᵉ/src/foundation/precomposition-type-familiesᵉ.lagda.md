# Precomposition of type families

```agda
module foundation.precomposition-type-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopy-inductionᵉ
open import foundation.transport-along-homotopiesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Anyᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ inducesᵉ aᵉ
{{#conceptᵉ "precompositionᵉ operation"ᵉ Disambiguation="typeᵉ families"ᵉ Agda=precomp-familyᵉ}}

```text
  (Bᵉ → 𝒰ᵉ) → (Aᵉ → 𝒰ᵉ)
```

givenᵉ byᵉ [precomposing](foundation-core.precomposition-functions.mdᵉ) anyᵉ
`Qᵉ : Bᵉ → 𝒰`ᵉ to `Qᵉ ∘ᵉ fᵉ : Aᵉ → 𝒰`.ᵉ

## Definitions

### The precomposition operation on type familes

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  precomp-familyᵉ : {lᵉ : Level} → (Bᵉ → UUᵉ lᵉ) → (Aᵉ → UUᵉ lᵉ)
  precomp-familyᵉ Qᵉ = Qᵉ ∘ᵉ fᵉ
```

## Properties

### Transport along homotopies in precomposed type families

[Transporting](foundation.transport-along-homotopies.mdᵉ) alongᵉ aᵉ
[homotopy](foundation.homotopies.mdᵉ) `Hᵉ : gᵉ ~ᵉ h`ᵉ in theᵉ familyᵉ `Qᵉ ∘ᵉ f`ᵉ givesᵉ usᵉ
aᵉ mapᵉ ofᵉ familiesᵉ ofᵉ elementsᵉ

```text
  ((aᵉ : Aᵉ) → Qᵉ (fᵉ (gᵉ aᵉ))) → ((aᵉ : Aᵉ) → Qᵉ (fᵉ (hᵉ aᵉ))) .ᵉ
```

Weᵉ showᵉ thatᵉ thisᵉ mapᵉ isᵉ homotopicᵉ to transportingᵉ alongᵉ
`fᵉ ·lᵉ Hᵉ : fᵉ ∘ᵉ gᵉ ~ᵉ fᵉ ∘ᵉ h`ᵉ in theᵉ familyᵉ `Q`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Qᵉ : Bᵉ → UUᵉ l3ᵉ)
  {Xᵉ : UUᵉ l4ᵉ} {gᵉ : Xᵉ → Aᵉ}
  where

  statement-tr-htpy-precomp-familyᵉ :
    {hᵉ : Xᵉ → Aᵉ} (Hᵉ : gᵉ ~ᵉ hᵉ) → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  statement-tr-htpy-precomp-familyᵉ Hᵉ =
    tr-htpyᵉ (λ _ → precomp-familyᵉ fᵉ Qᵉ) Hᵉ ~ᵉ tr-htpyᵉ (λ _ → Qᵉ) (fᵉ ·lᵉ Hᵉ)

  abstract
    tr-htpy-precomp-familyᵉ :
      {hᵉ : Xᵉ → Aᵉ} (Hᵉ : gᵉ ~ᵉ hᵉ) →
      statement-tr-htpy-precomp-familyᵉ Hᵉ
    tr-htpy-precomp-familyᵉ =
      ind-htpyᵉ gᵉ
        ( λ hᵉ → statement-tr-htpy-precomp-familyᵉ)
        ( refl-htpyᵉ)

    compute-tr-htpy-precomp-familyᵉ :
      tr-htpy-precomp-familyᵉ refl-htpyᵉ ＝ᵉ
      refl-htpyᵉ
    compute-tr-htpy-precomp-familyᵉ =
      compute-ind-htpyᵉ gᵉ
        ( λ hᵉ → statement-tr-htpy-precomp-familyᵉ)
        ( refl-htpyᵉ)
```