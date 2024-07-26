# Epimorphisms with respect to maps into sets

```agda
module foundation.epimorphisms-with-respect-to-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.setsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.univalenceᵉ
```

</details>

## Idea

Anᵉ epimorphismᵉ with respectᵉ to mapsᵉ intoᵉ setsᵉ areᵉ mapsᵉ `fᵉ : Aᵉ → B`ᵉ suchᵉ thatᵉ forᵉ
everyᵉ setᵉ `C`ᵉ theᵉ precompositionᵉ functionᵉ `(Bᵉ → Cᵉ) → (Aᵉ → C)`ᵉ isᵉ anᵉ embedding.ᵉ

## Definition

```agda
is-epimorphism-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → Bᵉ) → UUωᵉ
is-epimorphism-Setᵉ fᵉ =
  {lᵉ : Level} (Cᵉ : Setᵉ lᵉ) → is-embᵉ (precompᵉ fᵉ (type-Setᵉ Cᵉ))
```

## Properties

### Surjective maps are epimorphisms with respect to maps into sets

```agda
abstract
  is-epimorphism-is-surjective-Setᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
    is-surjectiveᵉ fᵉ → is-epimorphism-Setᵉ fᵉ
  is-epimorphism-is-surjective-Setᵉ Hᵉ Cᵉ =
    is-emb-is-injectiveᵉ
      ( is-set-function-typeᵉ (is-set-type-Setᵉ Cᵉ))
      ( λ {gᵉ} {hᵉ} pᵉ →
        eq-htpyᵉ
          ( λ bᵉ →
            apply-universal-property-trunc-Propᵉ
              ( Hᵉ bᵉ)
              ( Id-Propᵉ Cᵉ (gᵉ bᵉ) (hᵉ bᵉ))
              ( λ uᵉ →
                ( invᵉ (apᵉ gᵉ (pr2ᵉ uᵉ))) ∙ᵉ
                ( htpy-eqᵉ pᵉ (pr1ᵉ uᵉ)) ∙ᵉ
                ( apᵉ hᵉ (pr2ᵉ uᵉ)))))
```

### Maps that are epimorphisms with respect to maps into sets are surjective

```agda
abstract
  is-surjective-is-epimorphism-Setᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
    is-epimorphism-Setᵉ fᵉ → is-surjectiveᵉ fᵉ
  is-surjective-is-epimorphism-Setᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} {fᵉ} Hᵉ bᵉ =
    map-equivᵉ
      ( equiv-eqᵉ
        ( apᵉ
          ( pr1ᵉ)
          ( htpy-eqᵉ
            ( is-injective-is-embᵉ
              ( Hᵉ (Prop-Setᵉ (l1ᵉ ⊔ l2ᵉ)))
              { gᵉ}
              { hᵉ}
              ( eq-htpyᵉ
                ( λ aᵉ →
                  eq-iffᵉ
                    ( λ _ → unit-trunc-Propᵉ (pairᵉ aᵉ reflᵉ))
                    ( λ _ → raise-starᵉ))))
            ( bᵉ))))
      ( raise-starᵉ)
    where
    gᵉ : Bᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
    gᵉ yᵉ = raise-unit-Propᵉ (l1ᵉ ⊔ l2ᵉ)
    hᵉ : Bᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
    hᵉ yᵉ = exists-structure-Propᵉ Aᵉ (λ xᵉ → fᵉ xᵉ ＝ᵉ yᵉ)
```

### There is at most one extension of a map into a set along a surjection

Forᵉ anyᵉ surjectiveᵉ mapᵉ `fᵉ : Aᵉ ↠ᵉ B`ᵉ andᵉ anyᵉ mapᵉ `gᵉ : Aᵉ → C`ᵉ intoᵉ aᵉ setᵉ `C`,ᵉ theᵉ
typeᵉ ofᵉ extensionsᵉ

```text
  Σᵉ (Bᵉ → Cᵉ) (λ hᵉ → gᵉ ~ᵉ hᵉ ∘ᵉ fᵉ)
```

ofᵉ `g`ᵉ alongᵉ `f`ᵉ isᵉ aᵉ proposition.ᵉ Inᵉ
[Theᵉ universalᵉ propertyᵉ ofᵉ setᵉ quotients](foundation.universal-property-set-quotients.mdᵉ)
weᵉ willᵉ showᵉ thatᵉ thisᵉ propositionᵉ isᵉ equivalentᵉ to theᵉ propositionᵉ

```text
  (aᵉ a'ᵉ : Aᵉ) → fᵉ aᵉ ＝ᵉ fᵉ a'ᵉ → gᵉ aᵉ ＝ᵉ gᵉ a'.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ ↠ᵉ Bᵉ)
  (Cᵉ : Setᵉ l3ᵉ) (gᵉ : Aᵉ → type-Setᵉ Cᵉ)
  where

  extension-along-surjection-Setᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  extension-along-surjection-Setᵉ =
    Σᵉ (Bᵉ → type-Setᵉ Cᵉ) (λ hᵉ → gᵉ ~ᵉ hᵉ ∘ᵉ map-surjectionᵉ fᵉ)

  abstract
    is-prop-extension-along-surjection-Setᵉ :
      is-propᵉ extension-along-surjection-Setᵉ
    is-prop-extension-along-surjection-Setᵉ =
      is-prop-equiv'ᵉ
        ( equiv-totᵉ (λ hᵉ → equiv-funextᵉ ∘eᵉ equiv-invᵉ _ gᵉ))
        ( is-prop-map-is-embᵉ
          ( is-epimorphism-is-surjective-Setᵉ
            ( is-surjective-map-surjectionᵉ fᵉ)
            ( Cᵉ))
          ( gᵉ))
```

## See also

-ᵉ [Acyclicᵉ maps](synthetic-homotopy-theory.acyclic-maps.mdᵉ)
-ᵉ [Dependentᵉ epimorphisms](foundation.dependent-epimorphisms.mdᵉ)
-ᵉ [Epimorphisms](foundation.epimorphisms.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to truncatedᵉ types](foundation.epimorphisms-with-respect-to-truncated-types.mdᵉ)
-ᵉ [Theᵉ universalᵉ propertyᵉ ofᵉ setᵉ quotients](foundation.universal-property-set-quotients.mdᵉ)