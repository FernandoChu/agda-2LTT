# Acyclic maps

```agda
module synthetic-homotopy-theory.acyclic-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.constant-mapsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-epimorphismsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.diagonal-maps-of-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.epimorphismsᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-fibers-of-mapsᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.pullbacksᵉ
open import foundation.retracts-of-mapsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-cartesian-product-typesᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.acyclic-typesᵉ
open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.codiagonals-of-mapsᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.suspensions-of-typesᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ saidᵉ to beᵉ **acyclic**ᵉ ifᵉ itsᵉ
[fibers](foundation-core.fibers-of-maps.mdᵉ) areᵉ
[acyclicᵉ types](synthetic-homotopy-theory.acyclic-types.md).ᵉ

## Definitions

### The predicate of being an acyclic map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-acyclic-map-Propᵉ : (Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-acyclic-map-Propᵉ fᵉ = Π-Propᵉ Bᵉ (λ bᵉ → is-acyclic-Propᵉ (fiberᵉ fᵉ bᵉ))

  is-acyclic-mapᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-acyclic-mapᵉ fᵉ = type-Propᵉ (is-acyclic-map-Propᵉ fᵉ)

  is-prop-is-acyclic-mapᵉ : (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (is-acyclic-mapᵉ fᵉ)
  is-prop-is-acyclic-mapᵉ fᵉ = is-prop-type-Propᵉ (is-acyclic-map-Propᵉ fᵉ)
```

## Properties

### A map is acyclic if and only if it is an [epimorphism](foundation.epimorphisms.md)

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-acyclic-map-is-epimorphismᵉ : is-epimorphismᵉ fᵉ → is-acyclic-mapᵉ fᵉ
  is-acyclic-map-is-epimorphismᵉ eᵉ bᵉ =
    is-contr-equivᵉ
      ( fiberᵉ (codiagonal-mapᵉ fᵉ) bᵉ)
      ( equiv-fiber-codiagonal-map-suspension-fiberᵉ fᵉ bᵉ)
      ( is-contr-map-is-equivᵉ
        ( is-equiv-codiagonal-map-is-epimorphismᵉ fᵉ eᵉ)
        ( bᵉ))

  is-epimorphism-is-acyclic-mapᵉ : is-acyclic-mapᵉ fᵉ → is-epimorphismᵉ fᵉ
  is-epimorphism-is-acyclic-mapᵉ acᵉ =
    is-epimorphism-is-equiv-codiagonal-mapᵉ fᵉ
      ( is-equiv-is-contr-mapᵉ
        ( λ bᵉ →
          is-contr-equivᵉ
            ( suspensionᵉ (fiberᵉ fᵉ bᵉ))
            ( inv-equivᵉ (equiv-fiber-codiagonal-map-suspension-fiberᵉ fᵉ bᵉ))
            ( acᵉ bᵉ)))
```

### A type is acyclic if and only if its terminal map is an acyclic map

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  is-acyclic-map-terminal-map-is-acyclicᵉ :
    is-acyclicᵉ Aᵉ → is-acyclic-mapᵉ (terminal-mapᵉ Aᵉ)
  is-acyclic-map-terminal-map-is-acyclicᵉ acᵉ uᵉ =
    is-acyclic-equivᵉ (equiv-fiber-terminal-mapᵉ uᵉ) acᵉ

  is-acyclic-is-acyclic-map-terminal-mapᵉ :
    is-acyclic-mapᵉ (terminal-mapᵉ Aᵉ) → is-acyclicᵉ Aᵉ
  is-acyclic-is-acyclic-map-terminal-mapᵉ acᵉ =
    is-acyclic-equivᵉ inv-equiv-fiber-terminal-map-starᵉ (acᵉ starᵉ)
```

### A type is acyclic if and only if the constant map from any type is an embedding

Moreᵉ precisely,ᵉ `A`ᵉ isᵉ acyclicᵉ ifᵉ andᵉ onlyᵉ ifᵉ forᵉ allᵉ typesᵉ `X`,ᵉ theᵉ mapᵉ

```text
  Δᵉ : Xᵉ → (Aᵉ → Xᵉ)
```

isᵉ anᵉ embedding.ᵉ

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  is-emb-diagonal-exponential-is-acyclicᵉ :
    is-acyclicᵉ Aᵉ →
    {l'ᵉ : Level} (Xᵉ : UUᵉ l'ᵉ) → is-embᵉ (diagonal-exponentialᵉ Xᵉ Aᵉ)
  is-emb-diagonal-exponential-is-acyclicᵉ acᵉ Xᵉ =
    is-emb-compᵉ
      ( precompᵉ (terminal-mapᵉ Aᵉ) Xᵉ)
      ( map-inv-left-unit-law-function-typeᵉ Xᵉ)
      ( is-epimorphism-is-acyclic-mapᵉ (terminal-mapᵉ Aᵉ)
        ( is-acyclic-map-terminal-map-is-acyclicᵉ Aᵉ acᵉ)
        ( Xᵉ))
      ( is-emb-is-equivᵉ (is-equiv-map-inv-left-unit-law-function-typeᵉ Xᵉ))

  is-acyclic-is-emb-diagonal-exponentialᵉ :
    ({l'ᵉ : Level} (Xᵉ : UUᵉ l'ᵉ) → is-embᵉ (diagonal-exponentialᵉ Xᵉ Aᵉ)) →
    is-acyclicᵉ Aᵉ
  is-acyclic-is-emb-diagonal-exponentialᵉ eᵉ =
    is-acyclic-is-acyclic-map-terminal-mapᵉ Aᵉ
      ( is-acyclic-map-is-epimorphismᵉ
        ( terminal-mapᵉ Aᵉ)
        ( λ Xᵉ →
          is-emb-triangle-is-equiv'ᵉ
            ( diagonal-exponentialᵉ Xᵉ Aᵉ)
            ( precompᵉ (terminal-mapᵉ Aᵉ) Xᵉ)
            ( map-inv-left-unit-law-function-typeᵉ Xᵉ)
            ( refl-htpyᵉ)
            ( is-equiv-map-inv-left-unit-law-function-typeᵉ Xᵉ)
            ( eᵉ Xᵉ)))
```

### A type is acyclic if and only if the constant map from any identity type is an equivalence

Moreᵉ precisely,ᵉ `A`ᵉ isᵉ acyclicᵉ ifᵉ andᵉ onlyᵉ ifᵉ forᵉ allᵉ typesᵉ `X`ᵉ andᵉ elementsᵉ
`x,yᵉ : X`,ᵉ theᵉ mapᵉ

```text
  Δᵉ : (xᵉ ＝ᵉ yᵉ) → (Aᵉ → xᵉ ＝ᵉ yᵉ)
```

isᵉ anᵉ equivalence.ᵉ

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  is-equiv-diagonal-exponential-Id-is-acyclicᵉ :
    is-acyclicᵉ Aᵉ →
    {l'ᵉ : Level} {Xᵉ : UUᵉ l'ᵉ} (xᵉ yᵉ : Xᵉ) →
    is-equivᵉ (diagonal-exponentialᵉ (xᵉ ＝ᵉ yᵉ) Aᵉ)
  is-equiv-diagonal-exponential-Id-is-acyclicᵉ acᵉ {Xᵉ = Xᵉ} xᵉ yᵉ =
    is-equiv-htpyᵉ
      ( htpy-eqᵉ ∘ᵉ apᵉ (diagonal-exponentialᵉ Xᵉ Aᵉ) {xᵉ} {yᵉ})
      ( htpy-ap-diagonal-exponential-htpy-eq-diagonal-exponential-Idᵉ xᵉ yᵉ Aᵉ)
      ( is-equiv-compᵉ
        ( htpy-eqᵉ)
        ( apᵉ (diagonal-exponentialᵉ Xᵉ Aᵉ))
        ( is-emb-diagonal-exponential-is-acyclicᵉ Aᵉ acᵉ Xᵉ xᵉ yᵉ)
        ( funextᵉ (diagonal-exponentialᵉ Xᵉ Aᵉ xᵉ) (diagonal-exponentialᵉ Xᵉ Aᵉ yᵉ)))

  is-acyclic-is-equiv-diagonal-exponential-Idᵉ :
    ( {l'ᵉ : Level} {Xᵉ : UUᵉ l'ᵉ} (xᵉ yᵉ : Xᵉ) →
      is-equivᵉ (diagonal-exponentialᵉ (xᵉ ＝ᵉ yᵉ) Aᵉ)) →
    is-acyclicᵉ Aᵉ
  is-acyclic-is-equiv-diagonal-exponential-Idᵉ hᵉ =
    is-acyclic-is-emb-diagonal-exponentialᵉ Aᵉ
      ( λ Xᵉ xᵉ yᵉ →
        is-equiv-right-factorᵉ
          ( htpy-eqᵉ)
          ( apᵉ (diagonal-exponentialᵉ Xᵉ Aᵉ))
          ( funextᵉ (diagonal-exponentialᵉ Xᵉ Aᵉ xᵉ) (diagonal-exponentialᵉ Xᵉ Aᵉ yᵉ))
          ( is-equiv-htpyᵉ
            ( diagonal-exponentialᵉ (xᵉ ＝ᵉ yᵉ) Aᵉ)
            ( htpy-diagonal-exponential-Id-ap-diagonal-exponential-htpy-eqᵉ
              ( xᵉ)
              ( yᵉ)
              ( Aᵉ))
            ( hᵉ xᵉ yᵉ)))
```

### A map is acyclic if and only if it is an [dependent epimorphism](foundation.dependent-epimorphisms.md)

Theᵉ followingᵉ diagramᵉ isᵉ aᵉ helpfulᵉ illustrationᵉ in theᵉ secondᵉ proofᵉ:

```text
                        precompᵉ fᵉ
       (bᵉ : Bᵉ) → Cᵉ bᵉ -------------ᵉ >ᵉ (aᵉ : Aᵉ) → Cᵉ (fᵉ aᵉ)
             |                               ∧ᵉ
             |                               |
     map-Πᵉ Δᵉ |                               | ≃ᵉ [precompᵉ with theᵉ equivalenceᵉ
             |                               |        Aᵉ ≃ᵉ Σᵉ Bᵉ (fiberᵉ fᵉ)     ]
             ∨ᵉ               ind-Σᵉ           |
 ((bᵉ : Bᵉ) → fiberᵉ fᵉ bᵉ → Cᵉ bᵉ) ---->ᵉ (sᵉ : Σᵉ Bᵉ (fiberᵉ fᵉ)) → Cᵉ (pr1ᵉ sᵉ)
                              ≃ᵉ
                          [curryingᵉ]
```

Theᵉ leftᵉ mapᵉ isᵉ anᵉ embeddingᵉ ifᵉ `f`ᵉ isᵉ anᵉ acyclicᵉ map,ᵉ becauseᵉ theᵉ diagonalᵉ isᵉ
anᵉ embeddingᵉ in thisᵉ case.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-acyclic-map-is-dependent-epimorphismᵉ :
    is-dependent-epimorphismᵉ fᵉ → is-acyclic-mapᵉ fᵉ
  is-acyclic-map-is-dependent-epimorphismᵉ eᵉ =
    is-acyclic-map-is-epimorphismᵉ fᵉ
      ( is-epimorphism-is-dependent-epimorphismᵉ fᵉ eᵉ)

  is-dependent-epimorphism-is-acyclic-mapᵉ :
    is-acyclic-mapᵉ fᵉ → is-dependent-epimorphismᵉ fᵉ
  is-dependent-epimorphism-is-acyclic-mapᵉ acᵉ Cᵉ =
    is-emb-compᵉ
      ( precomp-Πᵉ (map-inv-equiv-total-fiberᵉ fᵉ) (Cᵉ ∘ᵉ pr1ᵉ) ∘ᵉ ind-Σᵉ)
      ( map-Πᵉ (λ bᵉ → diagonal-exponentialᵉ (Cᵉ bᵉ) (fiberᵉ fᵉ bᵉ)))
      ( is-emb-compᵉ
        ( precomp-Πᵉ (map-inv-equiv-total-fiberᵉ fᵉ) (Cᵉ ∘ᵉ pr1ᵉ))
        ( ind-Σᵉ)
        ( is-emb-is-equivᵉ
          ( is-equiv-precomp-Π-is-equivᵉ
            ( is-equiv-map-inv-equiv-total-fiberᵉ fᵉ) (Cᵉ ∘ᵉ pr1ᵉ)))
        ( is-emb-is-equivᵉ is-equiv-ind-Σᵉ))
      ( is-emb-map-Πᵉ
        ( λ bᵉ →
          is-emb-diagonal-exponential-is-acyclicᵉ (fiberᵉ fᵉ bᵉ) (acᵉ bᵉ) (Cᵉ bᵉ)))
```

Inᵉ particular,ᵉ everyᵉ epimorphismᵉ isᵉ actuallyᵉ aᵉ dependentᵉ epimorphism.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-dependent-epimorphism-is-epimorphismᵉ :
    is-epimorphismᵉ fᵉ → is-dependent-epimorphismᵉ fᵉ
  is-dependent-epimorphism-is-epimorphismᵉ eᵉ =
    is-dependent-epimorphism-is-acyclic-mapᵉ fᵉ
      ( is-acyclic-map-is-epimorphismᵉ fᵉ eᵉ)
```

### The class of acyclic maps is closed under composition and has the right cancellation property

Sinceᵉ theᵉ acyclicᵉ mapsᵉ areᵉ preciselyᵉ theᵉ epimorphismsᵉ thisᵉ followsᵉ fromᵉ theᵉ
correspondingᵉ factsᵉ aboutᵉ [epimorphisms](foundation.epimorphisms.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ)
  where

  is-acyclic-map-compᵉ :
    is-acyclic-mapᵉ gᵉ → is-acyclic-mapᵉ fᵉ → is-acyclic-mapᵉ (gᵉ ∘ᵉ fᵉ)
  is-acyclic-map-compᵉ agᵉ afᵉ =
    is-acyclic-map-is-epimorphismᵉ (gᵉ ∘ᵉ fᵉ)
      ( is-epimorphism-compᵉ gᵉ fᵉ
        ( is-epimorphism-is-acyclic-mapᵉ gᵉ agᵉ)
        ( is-epimorphism-is-acyclic-mapᵉ fᵉ afᵉ))

  is-acyclic-map-left-factorᵉ :
    is-acyclic-mapᵉ (gᵉ ∘ᵉ fᵉ) → is-acyclic-mapᵉ fᵉ → is-acyclic-mapᵉ gᵉ
  is-acyclic-map-left-factorᵉ acᵉ afᵉ =
    is-acyclic-map-is-epimorphismᵉ gᵉ
      ( is-epimorphism-left-factorᵉ gᵉ fᵉ
        ( is-epimorphism-is-acyclic-mapᵉ (gᵉ ∘ᵉ fᵉ) acᵉ)
        ( is-epimorphism-is-acyclic-mapᵉ fᵉ afᵉ))
```

### Acyclic maps are closed under pushouts

**Proof:**ᵉ Supposeᵉ weᵉ haveᵉ aᵉ pushoutᵉ squareᵉ onᵉ theᵉ leftᵉ in theᵉ diagramᵉ

```text
        gᵉ          jᵉ
   Sᵉ ------->ᵉ Bᵉ ------->ᵉ Cᵉ
   |          |          |
 fᵉ |          | jᵉ        | idᵉ
   |          |          |
   ∨ᵉ        ⌜ᵉ ∨ᵉ          ∨ᵉ
   Aᵉ ------->ᵉ Cᵉ ------->ᵉ Cᵉ
        iᵉ          idᵉ
```

Thenᵉ `j`ᵉ isᵉ acyclicᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ rightᵉ squareᵉ isᵉ aᵉ pushout,ᵉ whichᵉ byᵉ
pushoutᵉ pasting,ᵉ isᵉ equivalentᵉ to theᵉ outerᵉ rectangleᵉ beingᵉ aᵉ pushout.ᵉ Forᵉ anᵉ
arbitraryᵉ typeᵉ `X`ᵉ andᵉ `f`ᵉ acyclic,ᵉ weᵉ noteᵉ thatᵉ theᵉ followingᵉ compositeᵉ
computesᵉ to theᵉ identityᵉ:

```text
          cocone-mapᵉ fᵉ (jᵉ ∘ᵉ gᵉ)
 (Cᵉ → Xᵉ) --------------------->ᵉ coconeᵉ fᵉ (jᵉ ∘ᵉ gᵉ) Xᵉ
                             ̇=ᵉ Σᵉ (lᵉ : Aᵉ → Xᵉ) ,ᵉ Σᵉ (rᵉ : Cᵉ → Xᵉ) ,ᵉ lᵉ ∘ᵉ fᵉ ~ᵉ rᵉ ∘ᵉ jᵉ ∘ᵉ gᵉ
     (usingᵉ theᵉ leftᵉ squareᵉ)
                             ≃ᵉ Σᵉ (lᵉ : Aᵉ → Xᵉ) ,ᵉ Σᵉ (rᵉ : Cᵉ → Xᵉ) ,ᵉ lᵉ ∘ᵉ fᵉ ~ᵉ rᵉ ∘ᵉ iᵉ ∘ᵉ fᵉ
   (sinceᵉ fᵉ isᵉ acyclic/epicᵉ)
                             ≃ᵉ Σᵉ (lᵉ : Aᵉ → Xᵉ) ,ᵉ Σᵉ (rᵉ : Cᵉ → Xᵉ) ,ᵉ lᵉ ~ᵉ rᵉ ∘ᵉ iᵉ
                             ≃ᵉ Σᵉ (rᵉ : Cᵉ → Xᵉ) ,ᵉ Σᵉ (lᵉ : Aᵉ → Xᵉ) ,ᵉ lᵉ ~ᵉ rᵉ ∘ᵉ iᵉ
      (contractingᵉ atᵉ rᵉ ∘ᵉ iᵉ)
                             ≃ᵉ (Cᵉ → Xᵉ)
```

Therefore,ᵉ `cocone-mapᵉ fᵉ (jᵉ ∘ᵉ g)`ᵉ isᵉ anᵉ equivalenceᵉ andᵉ theᵉ outerᵉ rectangleᵉ isᵉ
indeedᵉ aᵉ pushout.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  {Cᵉ : UUᵉ l4ᵉ} (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Cᵉ)
  where

  equiv-cocone-postcomp-vertical-map-coconeᵉ :
    is-acyclic-mapᵉ fᵉ →
    {l5ᵉ : Level} (Xᵉ : UUᵉ l5ᵉ) →
    coconeᵉ fᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ gᵉ) Xᵉ ≃ᵉ (Cᵉ → Xᵉ)
  equiv-cocone-postcomp-vertical-map-coconeᵉ acᵉ Xᵉ =
    equivalence-reasoningᵉ
        coconeᵉ fᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ gᵉ) Xᵉ
      ≃ᵉ coconeᵉ fᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ fᵉ) Xᵉ
        byᵉ
          equiv-totᵉ
          ( λ uᵉ →
            equiv-totᵉ
              ( λ vᵉ →
                equiv-concat-htpy'ᵉ
                  ( uᵉ ∘ᵉ fᵉ)
                  ( λ sᵉ → apᵉ vᵉ (inv-htpyᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ) sᵉ))))
      ≃ᵉ Σᵉ ( Aᵉ → Xᵉ)
          ( λ uᵉ →
            Σᵉ (Cᵉ → Xᵉ) (λ vᵉ → uᵉ ∘ᵉ fᵉ ＝ᵉ vᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ fᵉ))
        byᵉ equiv-totᵉ ( λ uᵉ → equiv-totᵉ ( λ vᵉ → equiv-eq-htpyᵉ))
      ≃ᵉ Σᵉ (Aᵉ → Xᵉ) (λ uᵉ → Σᵉ (Cᵉ → Xᵉ) (λ vᵉ → uᵉ ＝ᵉ vᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ))
        byᵉ
          equiv-totᵉ
          ( λ uᵉ →
            equiv-totᵉ
              ( λ vᵉ →
                inv-equiv-ap-is-embᵉ (is-epimorphism-is-acyclic-mapᵉ fᵉ acᵉ Xᵉ)))
      ≃ᵉ Σᵉ (Cᵉ → Xᵉ) (λ vᵉ → Σᵉ (Aᵉ → Xᵉ) (λ uᵉ → uᵉ ＝ᵉ vᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ))
        byᵉ
          equiv-left-swap-Σᵉ
      ≃ᵉ (Cᵉ → Xᵉ)
        byᵉ
          equiv-pr1ᵉ (λ vᵉ → is-torsorial-Id'ᵉ (vᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ))

  is-acyclic-map-vertical-map-cocone-is-pushoutᵉ :
    is-pushoutᵉ fᵉ gᵉ cᵉ →
    is-acyclic-mapᵉ fᵉ →
    is-acyclic-mapᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
  is-acyclic-map-vertical-map-cocone-is-pushoutᵉ poᵉ acᵉ =
    is-acyclic-map-is-epimorphismᵉ
      ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
      ( is-epimorphism-universal-property-pushoutᵉ
        ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
        ( universal-property-pushout-right-universal-property-pushout-rectangleᵉ
          ( fᵉ)
          ( gᵉ)
          ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
          ( cᵉ)
          ( cocone-codiagonal-mapᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ))
          ( universal-property-pushout-is-pushoutᵉ fᵉ gᵉ cᵉ poᵉ)
          ( λ Xᵉ →
            is-equiv-right-factorᵉ
              ( map-equivᵉ (equiv-cocone-postcomp-vertical-map-coconeᵉ acᵉ Xᵉ))
              ( cocone-mapᵉ fᵉ
                ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ gᵉ)
                ( cocone-comp-horizontalᵉ fᵉ gᵉ
                  ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( cᵉ)
                  ( cocone-codiagonal-mapᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ))))
              ( is-equiv-map-equivᵉ
                ( equiv-cocone-postcomp-vertical-map-coconeᵉ acᵉ Xᵉ))
              ( is-equiv-idᵉ))))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  {Cᵉ : UUᵉ l4ᵉ} (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Cᵉ)
  where

  is-acyclic-map-horizontal-map-cocone-is-pushoutᵉ :
    is-pushoutᵉ fᵉ gᵉ cᵉ →
    is-acyclic-mapᵉ gᵉ →
    is-acyclic-mapᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
  is-acyclic-map-horizontal-map-cocone-is-pushoutᵉ poᵉ =
    is-acyclic-map-vertical-map-cocone-is-pushoutᵉ gᵉ fᵉ
      ( swap-coconeᵉ fᵉ gᵉ Cᵉ cᵉ)
      ( is-pushout-swap-cocone-is-pushoutᵉ fᵉ gᵉ Cᵉ cᵉ poᵉ)
```

### Acyclic maps are closed under pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  is-acyclic-map-vertical-map-cone-is-pullbackᵉ :
    is-pullbackᵉ fᵉ gᵉ cᵉ →
    is-acyclic-mapᵉ gᵉ →
    is-acyclic-mapᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ)
  is-acyclic-map-vertical-map-cone-is-pullbackᵉ pbᵉ acᵉ aᵉ =
    is-acyclic-equivᵉ
      ( map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ aᵉ ,ᵉ
        is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ fᵉ gᵉ cᵉ pbᵉ aᵉ)
      ( acᵉ (fᵉ aᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  is-acyclic-map-horizontal-map-cone-is-pullbackᵉ :
    is-pullbackᵉ fᵉ gᵉ cᵉ →
    is-acyclic-mapᵉ fᵉ →
    is-acyclic-mapᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
  is-acyclic-map-horizontal-map-cone-is-pullbackᵉ pbᵉ =
    is-acyclic-map-vertical-map-cone-is-pullbackᵉ gᵉ fᵉ
      ( swap-coneᵉ fᵉ gᵉ cᵉ)
      ( is-pullback-swap-coneᵉ fᵉ gᵉ cᵉ pbᵉ)
```

### Acyclic types are closed under dependent pair types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  is-acyclic-Σᵉ :
    is-acyclicᵉ Aᵉ → ((aᵉ : Aᵉ) → is-acyclicᵉ (Bᵉ aᵉ)) → is-acyclicᵉ (Σᵉ Aᵉ Bᵉ)
  is-acyclic-Σᵉ ac-Aᵉ ac-Bᵉ =
    is-acyclic-is-acyclic-map-terminal-mapᵉ
      ( Σᵉ Aᵉ Bᵉ)
      ( is-acyclic-map-compᵉ
        ( terminal-mapᵉ Aᵉ)
        ( pr1ᵉ)
        ( is-acyclic-map-terminal-map-is-acyclicᵉ Aᵉ ac-Aᵉ)
        ( λ aᵉ → is-acyclic-equivᵉ (equiv-fiber-pr1ᵉ Bᵉ aᵉ) (ac-Bᵉ aᵉ)))
```

### Acyclic types are closed under binary products

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  is-acyclic-productᵉ :
    is-acyclicᵉ Aᵉ → is-acyclicᵉ Bᵉ → is-acyclicᵉ (Aᵉ ×ᵉ Bᵉ)
  is-acyclic-productᵉ ac-Aᵉ ac-Bᵉ =
    is-acyclic-is-acyclic-map-terminal-mapᵉ
      ( Aᵉ ×ᵉ Bᵉ)
      ( is-acyclic-map-compᵉ
        ( terminal-mapᵉ Bᵉ)
        ( pr2ᵉ)
        ( is-acyclic-map-terminal-map-is-acyclicᵉ Bᵉ ac-Bᵉ)
        ( is-acyclic-map-horizontal-map-cone-is-pullbackᵉ
          ( terminal-mapᵉ Aᵉ)
          ( terminal-mapᵉ Bᵉ)
          ( cone-cartesian-productᵉ Aᵉ Bᵉ)
          ( is-pullback-cartesian-productᵉ Aᵉ Bᵉ)
          ( is-acyclic-map-terminal-map-is-acyclicᵉ Aᵉ ac-Aᵉ)))
```

### Inhabited, locally acyclic types are acyclic

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  is-acyclic-inhabited-is-acyclic-Idᵉ :
    is-inhabitedᵉ Aᵉ →
    ((aᵉ bᵉ : Aᵉ) → is-acyclicᵉ (aᵉ ＝ᵉ bᵉ)) →
    is-acyclicᵉ Aᵉ
  is-acyclic-inhabited-is-acyclic-Idᵉ hᵉ l-acᵉ =
    apply-universal-property-trunc-Propᵉ hᵉ
      ( is-acyclic-Propᵉ Aᵉ)
      ( λ aᵉ →
        is-acyclic-is-acyclic-map-terminal-mapᵉ Aᵉ
          ( is-acyclic-map-left-factorᵉ
            ( terminal-mapᵉ Aᵉ)
            ( pointᵉ aᵉ)
            ( is-acyclic-map-terminal-map-is-acyclicᵉ unitᵉ is-acyclic-unitᵉ)
            ( λ bᵉ → is-acyclic-equivᵉ (compute-fiber-pointᵉ aᵉ bᵉ) (l-acᵉ aᵉ bᵉ))))
```

### Acyclic maps are closed under retracts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-acyclic-map-retract-ofᵉ :
    fᵉ retract-of-mapᵉ gᵉ → is-acyclic-mapᵉ gᵉ → is-acyclic-mapᵉ fᵉ
  is-acyclic-map-retract-ofᵉ Rᵉ acᵉ bᵉ =
    is-acyclic-retract-ofᵉ
      ( retract-fiber-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ)
      ( acᵉ (map-codomain-inclusion-retract-mapᵉ fᵉ gᵉ Rᵉ bᵉ))
```

## See also

-ᵉ [Dependentᵉ epimorphisms](foundation.dependent-epimorphisms.mdᵉ)
-ᵉ [Epimorphisms](foundation.epimorphisms.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to sets](foundation.epimorphisms-with-respect-to-sets.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to truncatedᵉ types](foundation.epimorphisms-with-respect-to-truncated-types.mdᵉ)

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}