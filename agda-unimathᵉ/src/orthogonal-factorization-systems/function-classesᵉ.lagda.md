# Function classes

```agda
module orthogonal-factorization-systems.function-classesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalence-inductionᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.pullbacksᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **(smallᵉ) functionᵉ class**ᵉ isᵉ aᵉ [subtype](foundation.subtypes.mdᵉ) ofᵉ theᵉ typeᵉ
ofᵉ allᵉ functionsᵉ in aᵉ givenᵉ universe.ᵉ

## Definitions

```agda
function-classᵉ : (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
function-classᵉ l1ᵉ l2ᵉ l3ᵉ = {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → subtypeᵉ l3ᵉ (Aᵉ → Bᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : function-classᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  is-in-function-classᵉ : {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → UUᵉ l3ᵉ
  is-in-function-classᵉ = is-in-subtypeᵉ Pᵉ

  is-prop-is-in-function-classᵉ :
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (is-in-function-classᵉ fᵉ)
  is-prop-is-in-function-classᵉ = is-prop-is-in-subtypeᵉ Pᵉ

  type-function-classᵉ : (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  type-function-classᵉ Aᵉ Bᵉ = type-subtypeᵉ (Pᵉ {Aᵉ} {Bᵉ})

  inclusion-function-classᵉ :
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → type-function-classᵉ Aᵉ Bᵉ → Aᵉ → Bᵉ
  inclusion-function-classᵉ = inclusion-subtypeᵉ Pᵉ

  is-emb-inclusion-function-classᵉ :
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → is-embᵉ (inclusion-function-classᵉ {Aᵉ} {Bᵉ})
  is-emb-inclusion-function-classᵉ = is-emb-inclusion-subtypeᵉ Pᵉ

  emb-function-classᵉ :
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → type-function-classᵉ Aᵉ Bᵉ ↪ᵉ (Aᵉ → Bᵉ)
  emb-function-classᵉ = emb-subtypeᵉ Pᵉ
```

### Function classes containing the identities

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : function-classᵉ l1ᵉ l1ᵉ l2ᵉ)
  where
  has-identity-maps-function-classᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  has-identity-maps-function-classᵉ =
    {Aᵉ : UUᵉ l1ᵉ} → is-in-function-classᵉ Pᵉ (idᵉ {Aᵉ = Aᵉ})

  has-identity-maps-function-class-Propᵉ : Propᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  has-identity-maps-function-class-Propᵉ =
    implicit-Π-Propᵉ (UUᵉ l1ᵉ) λ Aᵉ → Pᵉ (idᵉ {Aᵉ = Aᵉ})

  is-prop-has-identity-maps-function-classᵉ :
    is-propᵉ has-identity-maps-function-classᵉ
  is-prop-has-identity-maps-function-classᵉ =
    is-prop-type-Propᵉ has-identity-maps-function-class-Propᵉ
```

### Function classes containing the equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : function-classᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  has-equivalences-function-classᵉ : UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ)
  has-equivalences-function-classᵉ =
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ fᵉ → is-in-function-classᵉ Pᵉ fᵉ

  is-prop-has-equivalences-function-classᵉ :
    is-propᵉ has-equivalences-function-classᵉ
  is-prop-has-equivalences-function-classᵉ =
    is-prop-iterated-implicit-Πᵉ 2
      ( λ Aᵉ Bᵉ → is-prop-iterated-Πᵉ 2 (λ fᵉ _ → is-prop-is-in-function-classᵉ Pᵉ fᵉ))

  has-equivalences-function-class-Propᵉ : Propᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ has-equivalences-function-class-Propᵉ = has-equivalences-function-classᵉ
  pr2ᵉ has-equivalences-function-class-Propᵉ =
    is-prop-has-equivalences-function-classᵉ
```

### Composition closed function classes

Weᵉ sayᵉ aᵉ functionᵉ classᵉ isᵉ **compositionᵉ closed**ᵉ ifᵉ itᵉ isᵉ closedᵉ underᵉ takingᵉ
composites.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : function-classᵉ l1ᵉ l1ᵉ l2ᵉ)
  where

  is-closed-under-composition-function-classᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  is-closed-under-composition-function-classᵉ =
    {Aᵉ Bᵉ Cᵉ : UUᵉ l1ᵉ} (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Cᵉ) →
    is-in-function-classᵉ Pᵉ fᵉ → is-in-function-classᵉ Pᵉ gᵉ →
    is-in-function-classᵉ Pᵉ (gᵉ ∘ᵉ fᵉ)

  is-prop-is-closed-under-composition-function-classᵉ :
    is-propᵉ is-closed-under-composition-function-classᵉ
  is-prop-is-closed-under-composition-function-classᵉ =
    is-prop-iterated-implicit-Πᵉ 3
      ( λ Aᵉ Bᵉ Cᵉ →
        is-prop-iterated-Πᵉ 4
          ( λ fᵉ gᵉ _ _ → is-prop-is-in-function-classᵉ Pᵉ (gᵉ ∘ᵉ fᵉ)))

  is-closed-under-composition-function-class-Propᵉ : Propᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-closed-under-composition-function-class-Propᵉ =
    is-closed-under-composition-function-classᵉ
  pr2ᵉ is-closed-under-composition-function-class-Propᵉ =
    is-prop-is-closed-under-composition-function-classᵉ

composition-closed-function-classᵉ :
  (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
composition-closed-function-classᵉ l1ᵉ l2ᵉ =
  Σᵉ (function-classᵉ l1ᵉ l1ᵉ l2ᵉ) (is-closed-under-composition-function-classᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : composition-closed-function-classᵉ l1ᵉ l2ᵉ)
  where

  function-class-composition-closed-function-classᵉ : function-classᵉ l1ᵉ l1ᵉ l2ᵉ
  function-class-composition-closed-function-classᵉ = pr1ᵉ Pᵉ

  is-closed-under-composition-composition-closed-function-classᵉ :
    is-closed-under-composition-function-classᵉ
      ( function-class-composition-closed-function-classᵉ)
  is-closed-under-composition-composition-closed-function-classᵉ = pr2ᵉ Pᵉ
```

## Pullback-stable function classes

Aᵉ functionᵉ classᵉ isᵉ saidᵉ to beᵉ **pullback-stable**ᵉ ifᵉ givenᵉ aᵉ functionᵉ in it,ᵉ
thenᵉ itsᵉ pullbackᵉ alongᵉ anyᵉ mapᵉ isᵉ alsoᵉ in theᵉ functionᵉ class.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : function-classᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  is-pullback-stable-function-classᵉ :
    UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ)
  is-pullback-stable-function-classᵉ =
    {Xᵉ Aᵉ : UUᵉ l1ᵉ} {Bᵉ Cᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ)
    (cᵉ : coneᵉ fᵉ gᵉ Xᵉ) (pᵉ : is-pullbackᵉ fᵉ gᵉ cᵉ) →
    is-in-function-classᵉ Pᵉ fᵉ →
    is-in-function-classᵉ Pᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ)

  is-prop-is-pullback-stable-function-classᵉ :
    is-propᵉ (is-pullback-stable-function-classᵉ)
  is-prop-is-pullback-stable-function-classᵉ =
    is-prop-iterated-implicit-Πᵉ 4
    ( λ Xᵉ Aᵉ Bᵉ Cᵉ →
      is-prop-iterated-Πᵉ 5
        ( λ fᵉ gᵉ cᵉ pᵉ _ →
          is-prop-is-in-function-classᵉ Pᵉ
            ( horizontal-map-coneᵉ fᵉ gᵉ cᵉ)))

  is-pullback-stable-function-class-Propᵉ : Propᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ is-pullback-stable-function-class-Propᵉ =
    is-pullback-stable-function-classᵉ
  pr2ᵉ is-pullback-stable-function-class-Propᵉ =
    is-prop-is-pullback-stable-function-classᵉ

pullback-stable-function-classᵉ :
  (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
pullback-stable-function-classᵉ l1ᵉ l2ᵉ l3ᵉ =
  Σᵉ ( function-classᵉ l1ᵉ l2ᵉ l3ᵉ) (is-pullback-stable-function-classᵉ)
```

## Properties

### Having equivalences is equivalent to having identity maps for function classes in a fixed universe

Thisᵉ isᵉ aᵉ consequenceᵉ ofᵉ [univalence](foundation.univalence.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : function-classᵉ l1ᵉ l1ᵉ l2ᵉ)
  where

  has-identity-maps-has-equivalences-function-classᵉ :
    has-equivalences-function-classᵉ Pᵉ → has-identity-maps-function-classᵉ Pᵉ
  has-identity-maps-has-equivalences-function-classᵉ has-equivs-Pᵉ =
    has-equivs-Pᵉ idᵉ is-equiv-idᵉ

  htpy-has-identity-maps-function-classᵉ :
    has-identity-maps-function-classᵉ Pᵉ →
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} (pᵉ : Xᵉ ＝ᵉ Yᵉ) → is-in-function-classᵉ Pᵉ (map-eqᵉ pᵉ)
  htpy-has-identity-maps-function-classᵉ has-ids-Pᵉ {Xᵉ} reflᵉ = has-ids-Pᵉ

  has-equivalence-has-identity-maps-function-classᵉ :
    has-identity-maps-function-classᵉ Pᵉ →
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} (eᵉ : Xᵉ ≃ᵉ Yᵉ) → is-in-function-classᵉ Pᵉ (map-equivᵉ eᵉ)
  has-equivalence-has-identity-maps-function-classᵉ has-ids-Pᵉ {Xᵉ} {Yᵉ} eᵉ =
    trᵉ
      ( is-in-function-classᵉ Pᵉ)
      ( apᵉ pr1ᵉ (is-section-eq-equivᵉ eᵉ))
      ( htpy-has-identity-maps-function-classᵉ has-ids-Pᵉ (eq-equivᵉ eᵉ))

  has-equivalences-has-identity-maps-function-classᵉ :
    has-identity-maps-function-classᵉ Pᵉ → has-equivalences-function-classᵉ Pᵉ
  has-equivalences-has-identity-maps-function-classᵉ has-ids-Pᵉ fᵉ is-equiv-fᵉ =
    has-equivalence-has-identity-maps-function-classᵉ has-ids-Pᵉ (fᵉ ,ᵉ is-equiv-fᵉ)

  is-equiv-has-identity-maps-has-equivalences-function-classᵉ :
    is-equivᵉ has-identity-maps-has-equivalences-function-classᵉ
  is-equiv-has-identity-maps-has-equivalences-function-classᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-has-equivalences-function-classᵉ Pᵉ)
      ( is-prop-has-identity-maps-function-classᵉ Pᵉ)
      ( has-equivalences-has-identity-maps-function-classᵉ)

  equiv-has-identity-maps-has-equivalences-function-classᵉ :
    has-equivalences-function-classᵉ Pᵉ ≃ᵉ has-identity-maps-function-classᵉ Pᵉ
  pr1ᵉ equiv-has-identity-maps-has-equivalences-function-classᵉ =
    has-identity-maps-has-equivalences-function-classᵉ
  pr2ᵉ equiv-has-identity-maps-has-equivalences-function-classᵉ =
    is-equiv-has-identity-maps-has-equivalences-function-classᵉ

  is-equiv-has-equivalences-has-identity-maps-function-classᵉ :
    is-equivᵉ has-equivalences-has-identity-maps-function-classᵉ
  is-equiv-has-equivalences-has-identity-maps-function-classᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-has-identity-maps-function-classᵉ Pᵉ)
      ( is-prop-has-equivalences-function-classᵉ Pᵉ)
      ( has-identity-maps-has-equivalences-function-classᵉ)

  equiv-has-equivalences-has-identity-maps-function-classᵉ :
    has-identity-maps-function-classᵉ Pᵉ ≃ᵉ has-equivalences-function-classᵉ Pᵉ
  pr1ᵉ equiv-has-equivalences-has-identity-maps-function-classᵉ =
    has-equivalences-has-identity-maps-function-classᵉ
  pr2ᵉ equiv-has-equivalences-has-identity-maps-function-classᵉ =
    is-equiv-has-equivalences-has-identity-maps-function-classᵉ
```

### Function classes are closed under composition with equivalences

Thisᵉ isᵉ alsoᵉ aᵉ consequenceᵉ ofᵉ univalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : function-classᵉ l1ᵉ l2ᵉ l3ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-closed-under-precomp-equiv-function-classᵉ :
    {Cᵉ : UUᵉ l1ᵉ} (eᵉ : Aᵉ ≃ᵉ Cᵉ) →
    (fᵉ : Aᵉ → Bᵉ) → is-in-subtypeᵉ Pᵉ fᵉ → is-in-subtypeᵉ Pᵉ (fᵉ ∘ᵉ map-inv-equivᵉ eᵉ)
  is-closed-under-precomp-equiv-function-classᵉ eᵉ fᵉ xᵉ =
    ind-equivᵉ (λ _ xᵉ → is-in-subtypeᵉ Pᵉ (fᵉ ∘ᵉ map-inv-equivᵉ xᵉ)) xᵉ eᵉ

  is-closed-under-postcomp-equiv-function-classᵉ :
    {Dᵉ : UUᵉ l2ᵉ} (eᵉ : Bᵉ ≃ᵉ Dᵉ) →
    (fᵉ : Aᵉ → Bᵉ) → is-in-subtypeᵉ Pᵉ fᵉ → is-in-subtypeᵉ Pᵉ (map-equivᵉ eᵉ ∘ᵉ fᵉ)
  is-closed-under-postcomp-equiv-function-classᵉ eᵉ fᵉ xᵉ =
    ind-equivᵉ (λ _ xᵉ → is-in-subtypeᵉ Pᵉ (map-equivᵉ xᵉ ∘ᵉ fᵉ)) xᵉ eᵉ
```