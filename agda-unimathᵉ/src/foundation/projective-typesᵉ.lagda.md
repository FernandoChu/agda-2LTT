# Projective types

```agda
module foundation.projective-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.connected-mapsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.setsᵉ
open import foundation-core.truncated-typesᵉ
```

</details>

## Idea

Aᵉ typeᵉ `X`ᵉ isᵉ saidᵉ to beᵉ **set-projective**ᵉ ifᵉ forᵉ everyᵉ surjectiveᵉ mapᵉ
`fᵉ : Aᵉ → B`ᵉ intoᵉ aᵉ setᵉ `B`ᵉ theᵉ postcompositionᵉ functionᵉ

```text
  (Xᵉ → Aᵉ) → (Xᵉ → Bᵉ)
```

isᵉ surjective.ᵉ Thisᵉ isᵉ equivalentᵉ to theᵉ conditionᵉ thatᵉ forᵉ everyᵉ equivalenceᵉ
relationᵉ `R`ᵉ onᵉ aᵉ typeᵉ `A`ᵉ theᵉ naturalᵉ mapᵉ

```text
  (Xᵉ → A)/~ᵉ → (Xᵉ → A/Rᵉ)
```

isᵉ anᵉ equivalence.ᵉ Theᵉ latterᵉ mapᵉ isᵉ alwaysᵉ anᵉ embedding,ᵉ andᵉ itᵉ isᵉ anᵉ
equivalenceᵉ forᵉ everyᵉ `X`,ᵉ `A`,ᵉ andᵉ `R`ᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ axiomᵉ ofᵉ choiceᵉ
holds.ᵉ

Theᵉ notionᵉ ofᵉ set-projectivenessᵉ generalizesᵉ to `n`-projectiveness,ᵉ forᵉ `nᵉ : ℕ`.ᵉ
Aᵉ typeᵉ `X`ᵉ isᵉ saidᵉ to beᵉ `k`-projectiveᵉ ifᵉ theᵉ postcompositionᵉ functionᵉ
`(Xᵉ → Aᵉ) → (Xᵉ → B)`ᵉ isᵉ surjectiveᵉ forᵉ everyᵉ `k-1`-connectedᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ intoᵉ
aᵉ `k`-truncatedᵉ typeᵉ `B`.ᵉ

## Definitions

### Set-projective types

```agda
is-set-projectiveᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
is-set-projectiveᵉ l2ᵉ l3ᵉ Xᵉ =
  (Aᵉ : UUᵉ l2ᵉ) (Bᵉ : Setᵉ l3ᵉ) (fᵉ : Aᵉ ↠ᵉ type-Setᵉ Bᵉ) →
  is-surjectiveᵉ (postcompᵉ Xᵉ (map-surjectionᵉ fᵉ))
```

### `k`-projective types

```agda
is-projectiveᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) (kᵉ : ℕᵉ) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
is-projectiveᵉ l2ᵉ l3ᵉ kᵉ Xᵉ =
  ( Aᵉ : UUᵉ l2ᵉ) (Bᵉ : Truncated-Typeᵉ l3ᵉ (truncation-level-ℕᵉ kᵉ))
  ( fᵉ :
    connected-mapᵉ
      ( truncation-level-minus-one-ℕᵉ kᵉ)
      ( Aᵉ)
      ( type-Truncated-Typeᵉ Bᵉ)) →
  is-surjectiveᵉ (postcompᵉ Xᵉ (map-connected-mapᵉ fᵉ))
```

## See also

-ᵉ Theᵉ naturalᵉ mapᵉ `(Xᵉ → A)/~ᵉ → (Xᵉ → A/R)`ᵉ wasᵉ studiedᵉ in
  [foundation.exponents-set-quotients](foundation.exponents-set-quotients.mdᵉ)