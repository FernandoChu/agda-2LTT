# The axiom of choice

```agda
module foundation.axiom-of-choiceᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.inhabited-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.projective-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.sectionsᵉ
open import foundation.split-surjective-mapsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.setsᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "axiomᵉ ofᵉ choice"ᵉ Agda=AC-0ᵉ}} assertsᵉ thatᵉ forᵉ everyᵉ familyᵉ ofᵉ
[inhabited](foundation.inhabited-types.mdᵉ) typesᵉ `B`ᵉ indexedᵉ byᵉ aᵉ
[set](foundation-core.sets.mdᵉ) `A`,ᵉ theᵉ typeᵉ ofᵉ sectionsᵉ ofᵉ thatᵉ familyᵉ
`(xᵉ : Aᵉ) → Bᵉ x`ᵉ isᵉ inhabited.ᵉ

## Definition

### The axiom of choice restricted to sets

```agda
AC-Setᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
AC-Setᵉ l1ᵉ l2ᵉ =
  (Aᵉ : Setᵉ l1ᵉ) (Bᵉ : type-Setᵉ Aᵉ → Setᵉ l2ᵉ) →
  ((xᵉ : type-Setᵉ Aᵉ) → is-inhabitedᵉ (type-Setᵉ (Bᵉ xᵉ))) →
  is-inhabitedᵉ ((xᵉ : type-Setᵉ Aᵉ) → type-Setᵉ (Bᵉ xᵉ))
```

### The axiom of choice

```agda
AC-0ᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
AC-0ᵉ l1ᵉ l2ᵉ =
  (Aᵉ : Setᵉ l1ᵉ) (Bᵉ : type-Setᵉ Aᵉ → UUᵉ l2ᵉ) →
  ((xᵉ : type-Setᵉ Aᵉ) → is-inhabitedᵉ (Bᵉ xᵉ)) →
  is-inhabitedᵉ ((xᵉ : type-Setᵉ Aᵉ) → Bᵉ xᵉ)
```

## Properties

### Every type is set-projective if and only if the axiom of choice holds

```agda
is-set-projective-AC-0ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} → AC-0ᵉ l2ᵉ (l1ᵉ ⊔ l2ᵉ) →
  (Xᵉ : UUᵉ l3ᵉ) → is-set-projectiveᵉ l1ᵉ l2ᵉ Xᵉ
is-set-projective-AC-0ᵉ acᵉ Xᵉ Aᵉ Bᵉ fᵉ hᵉ =
  map-trunc-Propᵉ
    ( ( map-Σᵉ
        ( λ gᵉ → ((map-surjectionᵉ fᵉ) ∘ᵉ gᵉ) ＝ᵉ hᵉ)
        ( precompᵉ hᵉ Aᵉ)
        ( λ sᵉ Hᵉ → htpy-postcompᵉ Xᵉ Hᵉ hᵉ)) ∘ᵉ
      ( section-is-split-surjectiveᵉ (map-surjectionᵉ fᵉ)))
    ( acᵉ Bᵉ (fiberᵉ (map-surjectionᵉ fᵉ)) (is-surjective-map-surjectionᵉ fᵉ))

AC-0-is-set-projectiveᵉ :
  {l1ᵉ l2ᵉ : Level} →
  ({lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-set-projectiveᵉ (l1ᵉ ⊔ l2ᵉ) l1ᵉ Xᵉ) →
  AC-0ᵉ l1ᵉ l2ᵉ
AC-0-is-set-projectiveᵉ Hᵉ Aᵉ Bᵉ Kᵉ =
  map-trunc-Propᵉ
    ( map-equivᵉ (equiv-Π-section-pr1ᵉ {Bᵉ = Bᵉ}) ∘ᵉ totᵉ (λ gᵉ → htpy-eqᵉ))
    ( Hᵉ ( type-Setᵉ Aᵉ)
        ( Σᵉ (type-Setᵉ Aᵉ) Bᵉ)
        ( Aᵉ)
        ( pr1ᵉ ,ᵉ (λ aᵉ → map-trunc-Propᵉ (map-inv-fiber-pr1ᵉ Bᵉ aᵉ) (Kᵉ aᵉ)))
        ( idᵉ))
```