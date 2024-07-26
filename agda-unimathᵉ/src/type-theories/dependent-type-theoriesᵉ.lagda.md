# Dependent type theories

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module type-theories.dependent-type-theoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ
```

</details>

## Idea

Weᵉ introduceᵉ theᵉ categoryᵉ ofᵉ dependentᵉ typeᵉ theories,ᵉ followingᵉ Voevodsky'sᵉ
notionᵉ ofᵉ $B$-systems.ᵉ Theᵉ categoryᵉ ofᵉ generalisedᵉ algebraicᵉ theoriesᵉ isᵉ definedᵉ
to beᵉ thisᵉ category.ᵉ Itᵉ shouldᵉ beᵉ equivalentᵉ to theᵉ categoryᵉ ofᵉ essentiallyᵉ
algebraicᵉ theories.ᵉ

## (Dependency) systems

(Dependencyᵉ) systemsᵉ areᵉ theᵉ structureᵉ aroundᵉ whichᵉ aᵉ dependentᵉ typeᵉ theoryᵉ isᵉ
built.ᵉ

```text
    Ã₀ᵉ       Ã₁ᵉ       Ã₂ᵉ
    |        |        |
    |        |        |
    ∨ᵉ        ∨ᵉ        ∨ᵉ
    A₀ᵉ <----ᵉ A₁ᵉ <----ᵉ A₂ᵉ <----ᵉ ⋯ᵉ
```

```agda
module dependentᵉ where

  record systemᵉ (l1ᵉ l2ᵉ : Level) : UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ) where
    coinductiveᵉ
    field
      typeᵉ : UUᵉ l1ᵉ
      elementᵉ : typeᵉ → UUᵉ l2ᵉ
      sliceᵉ : (Xᵉ : typeᵉ) → systemᵉ l1ᵉ l2ᵉ

  record fibered-systemᵉ
    {l1ᵉ l2ᵉ : Level} (l3ᵉ l4ᵉ : Level) (Aᵉ : systemᵉ l1ᵉ l2ᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ : system.typeᵉ Aᵉ → UUᵉ l3ᵉ
      elementᵉ : {Xᵉ : system.typeᵉ Aᵉ} → typeᵉ Xᵉ → system.elementᵉ Aᵉ Xᵉ → UUᵉ l4ᵉ
      sliceᵉ : {Xᵉ : system.typeᵉ Aᵉ} → typeᵉ Xᵉ →
                fibered-systemᵉ l3ᵉ l4ᵉ (system.sliceᵉ Aᵉ Xᵉ)

  record section-systemᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ : (Xᵉ : system.typeᵉ Aᵉ) → fibered-system.typeᵉ Bᵉ Xᵉ
      elementᵉ : {Xᵉ : system.typeᵉ Aᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
                fibered-system.elementᵉ Bᵉ (typeᵉ Xᵉ) xᵉ
      sliceᵉ : (Xᵉ : system.typeᵉ Aᵉ) →
                section-systemᵉ (fibered-system.sliceᵉ Bᵉ (typeᵉ Xᵉ))
```

### Heterogeneous homotopies of sections of fibered systems

willᵉ introduceᵉ homotopiesᵉ ofᵉ sectionsᵉ ofᵉ fiberedᵉ systems.ᵉ However,ᵉ in orderᵉ to
defineᵉ concatenationᵉ ofᵉ thoseᵉ homotopies,ᵉ weᵉ willᵉ firstᵉ defineᵉ heterogeneousᵉ
homotopiesᵉ ofᵉ sectionsᵉ ofᵉ fiberedᵉ systems.ᵉ

```agda
  tr-fibered-system-sliceᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ B'ᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    (αᵉ : Idᵉ Bᵉ B'ᵉ) (fᵉ : section-systemᵉ Bᵉ) (Xᵉ : system.typeᵉ Aᵉ) →
    Idᵉ
      ( fibered-system.sliceᵉ Bᵉ (section-system.typeᵉ fᵉ Xᵉ))
      ( fibered-system.sliceᵉ B'ᵉ
        ( section-system.typeᵉ (trᵉ section-systemᵉ αᵉ fᵉ) Xᵉ))
  tr-fibered-system-sliceᵉ reflᵉ fᵉ Xᵉ = reflᵉ

  Eq-fibered-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ B'ᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    (αᵉ : Idᵉ Bᵉ B'ᵉ) (fᵉ : section-systemᵉ Bᵉ) (gᵉ : section-systemᵉ B'ᵉ) →
    fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ
  fibered-system.typeᵉ (Eq-fibered-system'ᵉ {Aᵉ = Aᵉ} αᵉ fᵉ gᵉ) Xᵉ =
    Idᵉ
      ( section-system.typeᵉ (trᵉ section-systemᵉ αᵉ fᵉ) Xᵉ)
      ( section-system.typeᵉ gᵉ Xᵉ)
  fibered-system.elementᵉ (Eq-fibered-system'ᵉ {Aᵉ = Aᵉ} {Bᵉ} {B'ᵉ} αᵉ fᵉ gᵉ) pᵉ xᵉ =
    Idᵉ
      ( trᵉ
        ( λ tᵉ → fibered-system.elementᵉ B'ᵉ tᵉ xᵉ)
        ( pᵉ)
        ( section-system.elementᵉ (trᵉ section-systemᵉ αᵉ fᵉ) xᵉ))
      ( section-system.elementᵉ gᵉ xᵉ)
  fibered-system.sliceᵉ (Eq-fibered-system'ᵉ {Aᵉ = Aᵉ} {Bᵉ} {B'ᵉ} αᵉ fᵉ gᵉ) {Xᵉ} pᵉ =
    Eq-fibered-system'ᵉ
      ( tr-fibered-system-sliceᵉ αᵉ fᵉ Xᵉ ∙ᵉ apᵉ (fibered-system.sliceᵉ B'ᵉ) pᵉ)
      ( section-system.sliceᵉ fᵉ Xᵉ)
      ( section-system.sliceᵉ gᵉ Xᵉ)

  htpy-section-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ B'ᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    (αᵉ : Idᵉ Bᵉ B'ᵉ) (fᵉ : section-systemᵉ Bᵉ) (gᵉ : section-systemᵉ B'ᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-section-system'ᵉ {Aᵉ = Aᵉ} αᵉ fᵉ gᵉ =
    section-systemᵉ (Eq-fibered-system'ᵉ αᵉ fᵉ gᵉ)

  concat-htpy-section-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ B'ᵉ B''ᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {αᵉ : Idᵉ Bᵉ B'ᵉ} {βᵉ : Idᵉ B'ᵉ B''ᵉ} (γᵉ : Idᵉ Bᵉ B''ᵉ) (δᵉ : Idᵉ (αᵉ ∙ᵉ βᵉ) γᵉ)
    {fᵉ : section-systemᵉ Bᵉ} {gᵉ : section-systemᵉ B'ᵉ}
    {hᵉ : section-systemᵉ B''ᵉ}
    (Gᵉ : htpy-section-system'ᵉ αᵉ fᵉ gᵉ) (Hᵉ : htpy-section-system'ᵉ βᵉ gᵉ hᵉ) →
    htpy-section-system'ᵉ γᵉ fᵉ hᵉ
  section-system.typeᵉ
    ( concat-htpy-section-system'ᵉ {αᵉ = reflᵉ} {reflᵉ} reflᵉ reflᵉ Gᵉ Hᵉ) =
    section-system.typeᵉ Gᵉ ∙hᵉ section-system.typeᵉ Hᵉ
  section-system.elementᵉ
    ( concat-htpy-section-system'ᵉ
      {Bᵉ = Bᵉ} {αᵉ = reflᵉ} {reflᵉ} reflᵉ reflᵉ {fᵉ} Gᵉ Hᵉ) {Xᵉ} xᵉ =
    ( tr-concatᵉ
      { Bᵉ = λ tᵉ → fibered-system.elementᵉ Bᵉ tᵉ xᵉ}
      ( section-system.typeᵉ Gᵉ Xᵉ)
      ( section-system.typeᵉ Hᵉ Xᵉ)
      ( section-system.elementᵉ fᵉ xᵉ)) ∙ᵉ
    ( ( apᵉ
        ( trᵉ
          ( λ tᵉ → fibered-system.elementᵉ Bᵉ tᵉ xᵉ)
          ( section-system.typeᵉ Hᵉ Xᵉ))
        ( section-system.elementᵉ Gᵉ xᵉ)) ∙ᵉ
      ( section-system.elementᵉ Hᵉ xᵉ))
  section-system.sliceᵉ
    ( concat-htpy-section-system'ᵉ {Bᵉ = Bᵉ} {αᵉ = reflᵉ} {reflᵉ} reflᵉ reflᵉ Gᵉ Hᵉ) Xᵉ =
    concat-htpy-section-system'ᵉ
      ( apᵉ
        ( fibered-system.sliceᵉ Bᵉ)
        ( section-system.typeᵉ Gᵉ Xᵉ ∙ᵉ section-system.typeᵉ Hᵉ Xᵉ))
      ( invᵉ
        ( ap-concatᵉ
          ( fibered-system.sliceᵉ Bᵉ)
          ( section-system.typeᵉ Gᵉ Xᵉ)
          ( section-system.typeᵉ Hᵉ Xᵉ)))
      ( section-system.sliceᵉ Gᵉ Xᵉ)
      ( section-system.sliceᵉ Hᵉ Xᵉ)

  inv-htpy-section-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ B'ᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {αᵉ : Idᵉ Bᵉ B'ᵉ} (βᵉ : Idᵉ B'ᵉ Bᵉ) (γᵉ : Idᵉ (invᵉ αᵉ) βᵉ)
    {fᵉ : section-systemᵉ Bᵉ} {gᵉ : section-systemᵉ B'ᵉ} →
    htpy-section-system'ᵉ αᵉ fᵉ gᵉ → htpy-section-system'ᵉ βᵉ gᵉ fᵉ
  section-system.typeᵉ (inv-htpy-section-system'ᵉ {αᵉ = reflᵉ} .reflᵉ reflᵉ Hᵉ) Xᵉ =
    invᵉ (section-system.typeᵉ Hᵉ Xᵉ)
  section-system.elementᵉ
    ( inv-htpy-section-system'ᵉ {αᵉ = reflᵉ} .reflᵉ reflᵉ Hᵉ) {Xᵉ} xᵉ =
    eq-transpose-trᵉ
      ( section-system.typeᵉ Hᵉ Xᵉ)
      ( invᵉ (section-system.elementᵉ Hᵉ xᵉ))
  section-system.sliceᵉ
    ( inv-htpy-section-system'ᵉ {Bᵉ = Bᵉ} {αᵉ = reflᵉ} .reflᵉ reflᵉ Hᵉ) Xᵉ =
    inv-htpy-section-system'ᵉ
      ( apᵉ (fibered-system.sliceᵉ Bᵉ) (invᵉ (section-system.typeᵉ Hᵉ Xᵉ)))
      ( invᵉ (ap-invᵉ (fibered-system.sliceᵉ Bᵉ) (section-system.typeᵉ Hᵉ Xᵉ)))
      ( section-system.sliceᵉ Hᵉ Xᵉ)
```

### Nonhomogenous homotopies

Weᵉ specializeᵉ theᵉ aboveᵉ definitionsᵉ to nonhomogenousᵉ homotopies.ᵉ

```agda
  htpy-section-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    (fᵉ gᵉ : section-systemᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-section-systemᵉ {Aᵉ = Aᵉ} {Bᵉ} fᵉ gᵉ =
    htpy-section-system'ᵉ reflᵉ fᵉ gᵉ

  refl-htpy-section-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    (fᵉ : section-systemᵉ Bᵉ) → htpy-section-systemᵉ fᵉ fᵉ
  section-system.typeᵉ (refl-htpy-section-systemᵉ fᵉ) Xᵉ = reflᵉ
  section-system.elementᵉ (refl-htpy-section-systemᵉ fᵉ) xᵉ = reflᵉ
  section-system.sliceᵉ (refl-htpy-section-systemᵉ fᵉ) Xᵉ =
    refl-htpy-section-systemᵉ (section-system.sliceᵉ fᵉ Xᵉ)

  concat-htpy-section-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {fᵉ gᵉ hᵉ : section-systemᵉ Bᵉ} (Gᵉ : htpy-section-systemᵉ fᵉ gᵉ)
    (Hᵉ : htpy-section-systemᵉ gᵉ hᵉ) → htpy-section-systemᵉ fᵉ hᵉ
  concat-htpy-section-systemᵉ Gᵉ Hᵉ =
    concat-htpy-section-system'ᵉ reflᵉ reflᵉ Gᵉ Hᵉ

  inv-htpy-section-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {fᵉ gᵉ : section-systemᵉ Bᵉ} (Hᵉ : htpy-section-systemᵉ fᵉ gᵉ) →
    htpy-section-systemᵉ gᵉ fᵉ
  inv-htpy-section-systemᵉ Hᵉ = inv-htpy-section-system'ᵉ reflᵉ reflᵉ Hᵉ
```

### Total system of a fibered dependency system

```agda
  total-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : systemᵉ l1ᵉ l2ᵉ) (Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ) →
    systemᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
  system.typeᵉ (total-systemᵉ Aᵉ Bᵉ) =
    Σᵉ (system.typeᵉ Aᵉ) (fibered-system.typeᵉ Bᵉ)
  system.elementᵉ (total-systemᵉ Aᵉ Bᵉ) (pairᵉ Xᵉ Yᵉ) =
    Σᵉ (system.elementᵉ Aᵉ Xᵉ) (fibered-system.elementᵉ Bᵉ Yᵉ)
  system.sliceᵉ (total-systemᵉ Aᵉ Bᵉ) (pairᵉ Xᵉ Yᵉ) =
    total-systemᵉ (system.sliceᵉ Aᵉ Xᵉ) (fibered-system.sliceᵉ Bᵉ Yᵉ)
```

### Morphisms of systems

```agda
  constant-fibered-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : systemᵉ l1ᵉ l2ᵉ) (Bᵉ : systemᵉ l3ᵉ l4ᵉ) →
    fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ
  fibered-system.typeᵉ (constant-fibered-systemᵉ Aᵉ Bᵉ) Xᵉ = system.typeᵉ Bᵉ
  fibered-system.elementᵉ (constant-fibered-systemᵉ Aᵉ Bᵉ) Yᵉ xᵉ =
    system.elementᵉ Bᵉ Yᵉ
  fibered-system.sliceᵉ (constant-fibered-systemᵉ Aᵉ Bᵉ) {Xᵉ} Yᵉ =
    constant-fibered-systemᵉ (system.sliceᵉ Aᵉ Xᵉ) (system.sliceᵉ Bᵉ Yᵉ)

  hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : systemᵉ l1ᵉ l2ᵉ) (Bᵉ : systemᵉ l3ᵉ l4ᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-systemᵉ Aᵉ Bᵉ =
    section-systemᵉ (constant-fibered-systemᵉ Aᵉ Bᵉ)
```

### Homotopies of morphisms of systems

Homotopiesᵉ ofᵉ morphismsᵉ ofᵉ systemsᵉ areᵉ definedᵉ asᵉ anᵉ instance ofᵉ homotopiesᵉ ofᵉ
sectionsᵉ ofᵉ fiberedᵉ systems.ᵉ

```agda
  htpy-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    (fᵉ gᵉ : hom-systemᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-hom-systemᵉ fᵉ gᵉ = htpy-section-systemᵉ fᵉ gᵉ

  refl-htpy-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    (fᵉ : hom-systemᵉ Aᵉ Bᵉ) → htpy-hom-systemᵉ fᵉ fᵉ
  refl-htpy-hom-systemᵉ fᵉ =
    refl-htpy-section-systemᵉ fᵉ

  concat-htpy-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    {fᵉ gᵉ hᵉ : hom-systemᵉ Aᵉ Bᵉ} →
    htpy-hom-systemᵉ fᵉ gᵉ → htpy-hom-systemᵉ gᵉ hᵉ → htpy-hom-systemᵉ fᵉ hᵉ
  concat-htpy-hom-systemᵉ Gᵉ Hᵉ =
    concat-htpy-section-systemᵉ Gᵉ Hᵉ

  inv-htpy-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    {fᵉ gᵉ : hom-systemᵉ Aᵉ Bᵉ} → htpy-hom-systemᵉ fᵉ gᵉ → htpy-hom-systemᵉ gᵉ fᵉ
  inv-htpy-hom-systemᵉ Hᵉ = inv-htpy-section-systemᵉ Hᵉ
```

## The category of systems

Weᵉ showᵉ thatᵉ systemsᵉ formᵉ aᵉ category.ᵉ

```agda
  id-hom-systemᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : systemᵉ l1ᵉ l2ᵉ) → hom-systemᵉ Aᵉ Aᵉ
  section-system.typeᵉ (id-hom-systemᵉ Aᵉ) Xᵉ = Xᵉ
  section-system.elementᵉ (id-hom-systemᵉ Aᵉ) xᵉ = xᵉ
  section-system.sliceᵉ (id-hom-systemᵉ Aᵉ) Xᵉ = id-hom-systemᵉ (system.sliceᵉ Aᵉ Xᵉ)

  comp-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ} {Cᵉ : systemᵉ l5ᵉ l6ᵉ}
    (gᵉ : hom-systemᵉ Bᵉ Cᵉ) (fᵉ : hom-systemᵉ Aᵉ Bᵉ) → hom-systemᵉ Aᵉ Cᵉ
  section-system.typeᵉ (comp-hom-systemᵉ gᵉ fᵉ) =
    section-system.typeᵉ gᵉ ∘ᵉ section-system.typeᵉ fᵉ
  section-system.elementᵉ (comp-hom-systemᵉ gᵉ fᵉ) =
    ( section-system.elementᵉ gᵉ) ∘ᵉ (section-system.elementᵉ fᵉ)
  section-system.sliceᵉ (comp-hom-systemᵉ gᵉ fᵉ) Xᵉ =
    comp-hom-systemᵉ
      ( section-system.sliceᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ))
      ( section-system.sliceᵉ fᵉ Xᵉ)

  left-unit-law-comp-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    (fᵉ : hom-systemᵉ Aᵉ Bᵉ) →
    htpy-hom-systemᵉ (comp-hom-systemᵉ (id-hom-systemᵉ Bᵉ) fᵉ) fᵉ
  section-system.typeᵉ (left-unit-law-comp-hom-systemᵉ fᵉ) = refl-htpyᵉ
  section-system.elementᵉ (left-unit-law-comp-hom-systemᵉ fᵉ) = refl-htpyᵉ
  section-system.sliceᵉ (left-unit-law-comp-hom-systemᵉ fᵉ) Xᵉ =
    left-unit-law-comp-hom-systemᵉ (section-system.sliceᵉ fᵉ Xᵉ)

  right-unit-law-comp-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    (fᵉ : hom-systemᵉ Aᵉ Bᵉ) →
    htpy-hom-systemᵉ (comp-hom-systemᵉ fᵉ (id-hom-systemᵉ Aᵉ)) fᵉ
  section-system.typeᵉ (right-unit-law-comp-hom-systemᵉ fᵉ) = refl-htpyᵉ
  section-system.elementᵉ (right-unit-law-comp-hom-systemᵉ fᵉ) = refl-htpyᵉ
  section-system.sliceᵉ (right-unit-law-comp-hom-systemᵉ fᵉ) Xᵉ =
    right-unit-law-comp-hom-systemᵉ (section-system.sliceᵉ fᵉ Xᵉ)

  associative-comp-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    {Cᵉ : systemᵉ l5ᵉ l6ᵉ} {Dᵉ : systemᵉ l7ᵉ l8ᵉ} (hᵉ : hom-systemᵉ Cᵉ Dᵉ)
    (gᵉ : hom-systemᵉ Bᵉ Cᵉ) (fᵉ : hom-systemᵉ Aᵉ Bᵉ) →
    htpy-hom-systemᵉ
      ( comp-hom-systemᵉ (comp-hom-systemᵉ hᵉ gᵉ) fᵉ)
      ( comp-hom-systemᵉ hᵉ (comp-hom-systemᵉ gᵉ fᵉ))
  section-system.typeᵉ (associative-comp-hom-systemᵉ hᵉ gᵉ fᵉ) = refl-htpyᵉ
  section-system.elementᵉ (associative-comp-hom-systemᵉ hᵉ gᵉ fᵉ) = refl-htpyᵉ
  section-system.sliceᵉ (associative-comp-hom-systemᵉ hᵉ gᵉ fᵉ) Xᵉ =
    associative-comp-hom-systemᵉ
      ( section-system.sliceᵉ hᵉ
        ( section-system.typeᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ)))
      ( section-system.sliceᵉ gᵉ ( section-system.typeᵉ fᵉ Xᵉ))
      ( section-system.sliceᵉ fᵉ Xᵉ)

  left-whisker-comp-hom-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ B'ᵉ : systemᵉ l3ᵉ l4ᵉ}
    {Cᵉ C'ᵉ : systemᵉ l5ᵉ l6ᵉ} {gᵉ : hom-systemᵉ Bᵉ Cᵉ} {g'ᵉ : hom-systemᵉ B'ᵉ C'ᵉ}
    (pᵉ : Idᵉ Bᵉ B'ᵉ)
    {p'ᵉ : Idᵉ (constant-fibered-systemᵉ Aᵉ Bᵉ) (constant-fibered-systemᵉ Aᵉ B'ᵉ)}
    (αᵉ : Idᵉ (apᵉ (constant-fibered-systemᵉ Aᵉ) pᵉ) p'ᵉ)
    (qᵉ : Idᵉ Cᵉ C'ᵉ)
    {q'ᵉ : Idᵉ (constant-fibered-systemᵉ Aᵉ Cᵉ) (constant-fibered-systemᵉ Aᵉ C'ᵉ)}
    (βᵉ : Idᵉ (apᵉ (constant-fibered-systemᵉ Aᵉ) qᵉ) q'ᵉ)
    (rᵉ : Idᵉ (trᵉ (λ tᵉ → tᵉ) (ap-binaryᵉ hom-systemᵉ pᵉ qᵉ) gᵉ) g'ᵉ)
    {fᵉ : hom-systemᵉ Aᵉ Bᵉ} {f'ᵉ : hom-systemᵉ Aᵉ B'ᵉ} →
    htpy-section-system'ᵉ p'ᵉ fᵉ f'ᵉ →
    htpy-section-system'ᵉ q'ᵉ (comp-hom-systemᵉ gᵉ fᵉ) (comp-hom-systemᵉ g'ᵉ f'ᵉ)
  section-system.typeᵉ
    ( left-whisker-comp-hom-system'ᵉ {gᵉ = gᵉ} reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ Hᵉ) Xᵉ =
    apᵉ (section-system.typeᵉ gᵉ) (section-system.typeᵉ Hᵉ Xᵉ)
  section-system.elementᵉ
    ( left-whisker-comp-hom-system'ᵉ
      {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} {gᵉ = gᵉ} reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ {fᵉ} {f'ᵉ} Hᵉ) {Xᵉ} xᵉ =
    ( tr-apᵉ
      ( section-system.typeᵉ gᵉ)
      ( λ X'ᵉ → section-system.elementᵉ gᵉ {X'ᵉ})
      ( section-system.typeᵉ Hᵉ Xᵉ)
      ( section-system.elementᵉ fᵉ xᵉ)) ∙ᵉ
    ( apᵉ (section-system.elementᵉ gᵉ) (section-system.elementᵉ Hᵉ xᵉ))
  section-system.sliceᵉ
    ( left-whisker-comp-hom-system'ᵉ
      {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} {Cᵉ = Cᵉ} {gᵉ = gᵉ} reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ Hᵉ) Xᵉ =
    left-whisker-comp-hom-system'ᵉ
      ( apᵉ (system.sliceᵉ Bᵉ) (section-system.typeᵉ Hᵉ Xᵉ))
      ( invᵉ
        ( ap-compᵉ
          ( constant-fibered-systemᵉ (system.sliceᵉ Aᵉ Xᵉ))
          ( system.sliceᵉ Bᵉ)
          ( section-system.typeᵉ Hᵉ Xᵉ)))
      ( apᵉ (system.sliceᵉ Cᵉ ∘ᵉ section-system.typeᵉ gᵉ) (section-system.typeᵉ Hᵉ Xᵉ))
      ( ( apᵉ
          ( apᵉ (constant-fibered-systemᵉ (system.sliceᵉ Aᵉ Xᵉ)))
          ( ap-compᵉ
            ( system.sliceᵉ Cᵉ)
            ( section-system.typeᵉ gᵉ)
            ( section-system.typeᵉ Hᵉ Xᵉ))) ∙ᵉ
        ( invᵉ
          ( ap-compᵉ
            ( constant-fibered-systemᵉ (system.sliceᵉ Aᵉ Xᵉ))
            ( system.sliceᵉ Cᵉ)
            ( apᵉ (section-system.typeᵉ gᵉ) (section-system.typeᵉ Hᵉ Xᵉ)))))
      ( γᵉ (section-system.typeᵉ Hᵉ Xᵉ))
      ( section-system.sliceᵉ Hᵉ Xᵉ)
      where
      γᵉ : {Yᵉ Y'ᵉ : system.typeᵉ Bᵉ} (pᵉ : Idᵉ Yᵉ Y'ᵉ) →
          Idᵉ
            ( trᵉ
              ( λ tᵉ → tᵉ)
              ( ap-binaryᵉ hom-systemᵉ
                ( apᵉ (system.sliceᵉ Bᵉ) pᵉ)
                ( apᵉ (system.sliceᵉ Cᵉ ∘ᵉ section-system.typeᵉ gᵉ) pᵉ))
              ( section-system.sliceᵉ gᵉ Yᵉ))
            ( section-system.sliceᵉ gᵉ Y'ᵉ)
      γᵉ reflᵉ = reflᵉ

  left-whisker-comp-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    {Cᵉ : systemᵉ l5ᵉ l6ᵉ} (gᵉ : hom-systemᵉ Bᵉ Cᵉ) {fᵉ f'ᵉ : hom-systemᵉ Aᵉ Bᵉ} →
    htpy-hom-systemᵉ fᵉ f'ᵉ →
    htpy-hom-systemᵉ (comp-hom-systemᵉ gᵉ fᵉ) (comp-hom-systemᵉ gᵉ f'ᵉ)
  left-whisker-comp-hom-systemᵉ gᵉ Hᵉ =
    left-whisker-comp-hom-system'ᵉ reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ Hᵉ

  right-whisker-comp-hom-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    {Cᵉ C'ᵉ : systemᵉ l5ᵉ l6ᵉ} (pᵉ : Idᵉ Cᵉ C'ᵉ) {gᵉ : hom-systemᵉ Bᵉ Cᵉ}
    {g'ᵉ : hom-systemᵉ Bᵉ C'ᵉ}
    {p'ᵉ : Idᵉ (constant-fibered-systemᵉ Bᵉ Cᵉ) (constant-fibered-systemᵉ Bᵉ C'ᵉ)}
    (αᵉ : Idᵉ (apᵉ (constant-fibered-systemᵉ Bᵉ) pᵉ) p'ᵉ)
    {q'ᵉ : Idᵉ (constant-fibered-systemᵉ Aᵉ Cᵉ) (constant-fibered-systemᵉ Aᵉ C'ᵉ)}
    (βᵉ : Idᵉ (apᵉ (constant-fibered-systemᵉ Aᵉ) pᵉ) q'ᵉ)
    (Hᵉ : htpy-section-system'ᵉ p'ᵉ gᵉ g'ᵉ) →
    (fᵉ : hom-systemᵉ Aᵉ Bᵉ) →
    htpy-section-system'ᵉ q'ᵉ (comp-hom-systemᵉ gᵉ fᵉ) (comp-hom-systemᵉ g'ᵉ fᵉ)
  section-system.typeᵉ (right-whisker-comp-hom-system'ᵉ reflᵉ reflᵉ reflᵉ Hᵉ fᵉ) Xᵉ =
    section-system.typeᵉ Hᵉ (section-system.typeᵉ fᵉ Xᵉ)
  section-system.elementᵉ
    ( right-whisker-comp-hom-system'ᵉ reflᵉ reflᵉ reflᵉ Hᵉ fᵉ) xᵉ =
    section-system.elementᵉ Hᵉ (section-system.elementᵉ fᵉ xᵉ)
  section-system.sliceᵉ
    ( right-whisker-comp-hom-system'ᵉ
      {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} {Cᵉ = Cᵉ} reflᵉ reflᵉ reflᵉ Hᵉ fᵉ) Xᵉ =
    right-whisker-comp-hom-system'ᵉ
      ( apᵉ (system.sliceᵉ Cᵉ) (section-system.typeᵉ Hᵉ (section-system.typeᵉ fᵉ Xᵉ)))
      ( invᵉ
        ( ap-compᵉ
          ( constant-fibered-systemᵉ (system.sliceᵉ Bᵉ (section-system.typeᵉ fᵉ Xᵉ)))
          ( system.sliceᵉ Cᵉ)
          ( section-system.typeᵉ Hᵉ (section-system.typeᵉ fᵉ Xᵉ))))
      ( invᵉ
        ( ap-compᵉ
          ( constant-fibered-systemᵉ (system.sliceᵉ Aᵉ Xᵉ))
          ( system.sliceᵉ Cᵉ)
          ( section-system.typeᵉ Hᵉ (section-system.typeᵉ fᵉ Xᵉ))))
      ( section-system.sliceᵉ Hᵉ (section-system.typeᵉ fᵉ Xᵉ))
      ( section-system.sliceᵉ fᵉ Xᵉ)

  right-whisker-comp-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    {Cᵉ : systemᵉ l5ᵉ l6ᵉ} {gᵉ g'ᵉ : hom-systemᵉ Bᵉ Cᵉ}
    (Hᵉ : htpy-section-systemᵉ gᵉ g'ᵉ) →
    (fᵉ : hom-systemᵉ Aᵉ Bᵉ) →
    htpy-section-systemᵉ (comp-hom-systemᵉ gᵉ fᵉ) (comp-hom-systemᵉ g'ᵉ fᵉ)
  right-whisker-comp-hom-systemᵉ Hᵉ fᵉ =
    right-whisker-comp-hom-system'ᵉ reflᵉ reflᵉ reflᵉ Hᵉ fᵉ
```

---ᵉ

## Structures on dependent type theories

Dependentᵉ typeᵉ theoriesᵉ areᵉ systemsᵉ equippedᵉ with weakeningᵉ andᵉ substitutionᵉ
structure,ᵉ andᵉ with theᵉ structureᵉ ofᵉ genericᵉ elementsᵉ (theᵉ variableᵉ rule).ᵉ

### Weakening structure on systems

```agda
  record weakeningᵉ {l1ᵉ l2ᵉ : Level} (Aᵉ : systemᵉ l1ᵉ l2ᵉ) : UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ : (Xᵉ : system.typeᵉ Aᵉ) → hom-systemᵉ Aᵉ (system.sliceᵉ Aᵉ Xᵉ)
      sliceᵉ : (Xᵉ : system.typeᵉ Aᵉ) → weakeningᵉ (system.sliceᵉ Aᵉ Xᵉ)
```

### Morphisms preserving weakening structure

Weᵉ stateᵉ whatᵉ itᵉ meansᵉ forᵉ aᵉ morphismᵉ to preserveᵉ weakeningᵉ structure.ᵉ

```agda
  record preserves-weakeningᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    (WAᵉ : weakeningᵉ Aᵉ) (WBᵉ : weakeningᵉ Bᵉ) (hᵉ : hom-systemᵉ Aᵉ Bᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        htpy-hom-systemᵉ
          ( comp-hom-systemᵉ
            ( section-system.sliceᵉ hᵉ Xᵉ)
            ( weakening.typeᵉ WAᵉ Xᵉ))
          ( comp-hom-systemᵉ
            ( weakening.typeᵉ WBᵉ (section-system.typeᵉ hᵉ Xᵉ))
            ( hᵉ))
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        preserves-weakeningᵉ
          ( weakening.sliceᵉ WAᵉ Xᵉ)
          ( weakening.sliceᵉ WBᵉ (section-system.typeᵉ hᵉ Xᵉ))
          ( section-system.sliceᵉ hᵉ Xᵉ)
```

### Substitution structure on systems

Weᵉ introduceᵉ substitutionᵉ structureᵉ onᵉ aᵉ system.ᵉ

```agda
  record substitutionᵉ {l1ᵉ l2ᵉ : Level} (Aᵉ : systemᵉ l1ᵉ l2ᵉ) :
    UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
        hom-systemᵉ (system.sliceᵉ Aᵉ Xᵉ) Aᵉ
      sliceᵉ : (Xᵉ : system.typeᵉ Aᵉ) → substitutionᵉ (system.sliceᵉ Aᵉ Xᵉ)
```

### Morphisms preserving substitution structure

Weᵉ stateᵉ whatᵉ itᵉ meansᵉ forᵉ aᵉ morphismᵉ to preserveᵉ substitutionᵉ structure.ᵉ

```agda
  record preserves-substitutionᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    (SAᵉ : substitutionᵉ Aᵉ) (SBᵉ : substitutionᵉ Bᵉ) (hᵉ : hom-systemᵉ Aᵉ Bᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
        htpy-hom-systemᵉ
          ( comp-hom-systemᵉ
            ( hᵉ)
            ( substitution.typeᵉ SAᵉ xᵉ))
          ( comp-hom-systemᵉ
            ( substitution.typeᵉ SBᵉ
              ( section-system.elementᵉ hᵉ xᵉ))
            ( section-system.sliceᵉ hᵉ Xᵉ))
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        preserves-substitutionᵉ
          ( substitution.sliceᵉ SAᵉ Xᵉ)
          ( substitution.sliceᵉ SBᵉ (section-system.typeᵉ hᵉ Xᵉ))
          ( section-system.sliceᵉ hᵉ Xᵉ)
```

### The structure of a generic element on a system equipped with weakening structure

Weᵉ introduceᵉ theᵉ structureᵉ ofᵉ aᵉ genericᵉ elementᵉ onᵉ aᵉ systemᵉ equippedᵉ with
weakeningᵉ structure.ᵉ

```agda
  record generic-elementᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Wᵉ : weakeningᵉ Aᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        system.elementᵉ
          ( system.sliceᵉ Aᵉ Xᵉ)
            ( section-system.typeᵉ (weakening.typeᵉ Wᵉ Xᵉ) Xᵉ)
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) → generic-elementᵉ (weakening.sliceᵉ Wᵉ Xᵉ)

  record preserves-generic-elementᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} (δAᵉ : generic-elementᵉ WAᵉ)
    {WBᵉ : weakeningᵉ Bᵉ} (δBᵉ : generic-elementᵉ WBᵉ)
    {hᵉ : hom-systemᵉ Aᵉ Bᵉ} (Whᵉ : preserves-weakeningᵉ WAᵉ WBᵉ hᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        Idᵉ ( trᵉ
              ( system.elementᵉ (system.sliceᵉ Bᵉ (section-system.typeᵉ hᵉ Xᵉ)))
              ( section-system.typeᵉ
                ( preserves-weakening.typeᵉ Whᵉ Xᵉ)
                ( Xᵉ))
              ( section-system.elementᵉ
                ( section-system.sliceᵉ hᵉ Xᵉ)
                ( generic-element.typeᵉ δAᵉ Xᵉ)))
            ( generic-element.typeᵉ δBᵉ (section-system.typeᵉ hᵉ Xᵉ))
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        preserves-generic-elementᵉ
          ( generic-element.sliceᵉ δAᵉ Xᵉ)
          ( generic-element.sliceᵉ δBᵉ (section-system.typeᵉ hᵉ Xᵉ))
          ( preserves-weakening.sliceᵉ Whᵉ Xᵉ)
```

### Weakening and substitution morphisms preserve weakening, substitution, and generic elements

Inᵉ aᵉ dependentᵉ typeᵉ theory,ᵉ everyᵉ weakeningᵉ morphismᵉ andᵉ everyᵉ substitutionᵉ
morphismᵉ preserveᵉ bothᵉ theᵉ weakeningᵉ andᵉ substitutionᵉ structure,ᵉ andᵉ theyᵉ alsoᵉ
preserveᵉ genericᵉ elements.ᵉ

Forᵉ example,ᵉ theᵉ ruleᵉ thatᵉ statesᵉ thatᵉ weakeningᵉ preservesᵉ weakeningᵉ (onᵉ typesᵉ)
canᵉ beᵉ displayedᵉ asᵉ followsᵉ:

```text
        Γᵉ ⊢ᵉ Aᵉ typeᵉ          Γ,Δᵉ ⊢ᵉ Bᵉ typeᵉ          Γ,Δ,Εᵉ ⊢ᵉ Cᵉ typeᵉ
  ------------------------------------------------------------------------ᵉ
  Γ,A,W(A,Δ),W(A,B),W(W(A,B),W(A,Eᵉ)) ⊢ᵉ W(W(A,B),W(A,C))=W(A,W(B,Cᵉ)) typeᵉ
```

Furthermore,ᵉ thereᵉ areᵉ lawsᵉ thatᵉ stateᵉ thatᵉ substitutionᵉ byᵉ `aᵉ : A`ᵉ cancelsᵉ
weakeningᵉ byᵉ `A`,ᵉ thatᵉ substitutingᵉ a:Aᵉ in theᵉ genericᵉ elementᵉ ofᵉ `A`ᵉ givesᵉ usᵉ
theᵉ elementᵉ aᵉ back,ᵉ andᵉ thatᵉ substitutingᵉ byᵉ theᵉ genericᵉ elementᵉ ofᵉ `A`ᵉ cancelsᵉ
weakeningᵉ byᵉ `A`.ᵉ

Weᵉ willᵉ nowᵉ stateᵉ theseᵉ laws.ᵉ

```agda
  record weakening-preserves-weakeningᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Wᵉ : weakeningᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        preserves-weakeningᵉ Wᵉ (weakening.sliceᵉ Wᵉ Xᵉ) (weakening.typeᵉ Wᵉ Xᵉ)
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        weakening-preserves-weakeningᵉ (weakening.sliceᵉ Wᵉ Xᵉ)

  record substitution-preserves-substitutionᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Sᵉ : substitutionᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
        preserves-substitutionᵉ
          ( substitution.sliceᵉ Sᵉ Xᵉ)
          ( Sᵉ)
          ( substitution.typeᵉ Sᵉ xᵉ)
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        substitution-preserves-substitutionᵉ (substitution.sliceᵉ Sᵉ Xᵉ)

  record weakening-preserves-substitutionᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Sᵉ : substitutionᵉ Aᵉ) (Wᵉ : weakeningᵉ Aᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        preserves-substitutionᵉ
          ( Sᵉ)
          ( substitution.sliceᵉ Sᵉ Xᵉ)
          ( weakening.typeᵉ Wᵉ Xᵉ)
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        weakening-preserves-substitutionᵉ
          ( substitution.sliceᵉ Sᵉ Xᵉ)
          ( weakening.sliceᵉ Wᵉ Xᵉ)

  record substitution-preserves-weakeningᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Wᵉ : weakeningᵉ Aᵉ) (Sᵉ : substitutionᵉ Aᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
        preserves-weakeningᵉ
          ( weakening.sliceᵉ Wᵉ Xᵉ)
          ( Wᵉ)
          ( substitution.typeᵉ Sᵉ xᵉ)
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        substitution-preserves-weakeningᵉ
          ( weakening.sliceᵉ Wᵉ Xᵉ)
          ( substitution.sliceᵉ Sᵉ Xᵉ)

  record weakening-preserves-generic-elementᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Wᵉ : weakeningᵉ Aᵉ)
    (WWᵉ : weakening-preserves-weakeningᵉ Wᵉ) (δᵉ : generic-elementᵉ Wᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        preserves-generic-elementᵉ
          ( δᵉ)
          ( generic-element.sliceᵉ δᵉ Xᵉ)
          ( weakening-preserves-weakening.typeᵉ WWᵉ Xᵉ)
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        weakening-preserves-generic-elementᵉ
          ( weakening.sliceᵉ Wᵉ Xᵉ)
          ( weakening-preserves-weakening.sliceᵉ WWᵉ Xᵉ)
          ( generic-element.sliceᵉ δᵉ Xᵉ)

  record substitution-preserves-generic-elementᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Wᵉ : weakeningᵉ Aᵉ)
    (δᵉ : generic-elementᵉ Wᵉ) (Sᵉ : substitutionᵉ Aᵉ)
    (SWᵉ : substitution-preserves-weakeningᵉ Wᵉ Sᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
        preserves-generic-elementᵉ
          ( generic-element.sliceᵉ δᵉ Xᵉ)
          ( δᵉ)
          ( substitution-preserves-weakening.typeᵉ SWᵉ xᵉ)
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        substitution-preserves-generic-elementᵉ
          ( weakening.sliceᵉ Wᵉ Xᵉ)
          ( generic-element.sliceᵉ δᵉ Xᵉ)
          ( substitution.sliceᵉ Sᵉ Xᵉ)
          ( substitution-preserves-weakening.sliceᵉ SWᵉ Xᵉ)

  record substitution-cancels-weakeningᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Wᵉ : weakeningᵉ Aᵉ) (Sᵉ : substitutionᵉ Aᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
        htpy-hom-systemᵉ
          ( comp-hom-systemᵉ
            ( substitution.typeᵉ Sᵉ xᵉ)
            ( weakening.typeᵉ Wᵉ Xᵉ))
          ( id-hom-systemᵉ Aᵉ)
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        substitution-cancels-weakeningᵉ
          ( weakening.sliceᵉ Wᵉ Xᵉ)
          ( substitution.sliceᵉ Sᵉ Xᵉ)

  record generic-element-is-identityᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Wᵉ : weakeningᵉ Aᵉ) (Sᵉ : substitutionᵉ Aᵉ)
    (δᵉ : generic-elementᵉ Wᵉ) (S!Wᵉ : substitution-cancels-weakeningᵉ Wᵉ Sᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
        Idᵉ
          ( trᵉ
            ( system.elementᵉ Aᵉ)
            ( section-system.typeᵉ
              ( substitution-cancels-weakening.typeᵉ S!Wᵉ xᵉ) Xᵉ)
            ( section-system.elementᵉ
              ( substitution.typeᵉ Sᵉ xᵉ)
              ( generic-element.typeᵉ δᵉ Xᵉ)))
          ( xᵉ)
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        generic-element-is-identityᵉ
          ( weakening.sliceᵉ Wᵉ Xᵉ)
          ( substitution.sliceᵉ Sᵉ Xᵉ)
          ( generic-element.sliceᵉ δᵉ Xᵉ)
          ( substitution-cancels-weakening.sliceᵉ S!Wᵉ Xᵉ)

  record substitution-by-generic-elementᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Wᵉ : weakeningᵉ Aᵉ) (Sᵉ : substitutionᵉ Aᵉ)
    (δᵉ : generic-elementᵉ Wᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        htpy-hom-systemᵉ
          ( comp-hom-systemᵉ
            ( substitution.typeᵉ
              ( substitution.sliceᵉ Sᵉ Xᵉ)
              ( generic-element.typeᵉ δᵉ Xᵉ))
            ( weakening.typeᵉ
              ( weakening.sliceᵉ Wᵉ Xᵉ)
              ( section-system.typeᵉ (weakening.typeᵉ Wᵉ Xᵉ) Xᵉ)))
          ( id-hom-systemᵉ (system.sliceᵉ Aᵉ Xᵉ))
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        substitution-by-generic-elementᵉ
          ( weakening.sliceᵉ Wᵉ Xᵉ)
          ( substitution.sliceᵉ Sᵉ Xᵉ)
          ( generic-element.sliceᵉ δᵉ Xᵉ)
```

### Complete definition of a dependent type theory

Weᵉ completeᵉ theᵉ definitionᵉ ofᵉ aᵉ dependentᵉ typeᵉ theory.ᵉ

```agda
  record type-theoryᵉ
    (l1ᵉ l2ᵉ : Level) : UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
    where
    field
      sysᵉ : systemᵉ l1ᵉ l2ᵉ
      Wᵉ : weakeningᵉ sysᵉ
      Sᵉ : substitutionᵉ sysᵉ
      δᵉ : generic-elementᵉ Wᵉ
      WWᵉ : weakening-preserves-weakeningᵉ Wᵉ
      SSᵉ : substitution-preserves-substitutionᵉ Sᵉ
      WSᵉ : weakening-preserves-substitutionᵉ Sᵉ Wᵉ
      SWᵉ : substitution-preserves-weakeningᵉ Wᵉ Sᵉ
      Wδᵉ : weakening-preserves-generic-elementᵉ Wᵉ WWᵉ δᵉ
      Sδᵉ : substitution-preserves-generic-elementᵉ Wᵉ δᵉ Sᵉ SWᵉ
      S!Wᵉ : substitution-cancels-weakeningᵉ Wᵉ Sᵉ
      δidᵉ : generic-element-is-identityᵉ Wᵉ Sᵉ δᵉ S!Wᵉ
      Sδ!ᵉ : substitution-by-generic-elementᵉ Wᵉ Sᵉ δᵉ

  closed-type-dttᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) → UUᵉ l1ᵉ
  closed-type-dttᵉ Aᵉ = system.typeᵉ (type-theory.sysᵉ Aᵉ)

  global-element-dttᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) → closed-type-dttᵉ Aᵉ → UUᵉ l2ᵉ
  global-element-dttᵉ Aᵉ = system.elementᵉ (type-theory.sysᵉ Aᵉ)

  weakening-dttᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) (Xᵉ : closed-type-dttᵉ Aᵉ) →
    hom-systemᵉ
      ( type-theory.sysᵉ Aᵉ)
      ( system.sliceᵉ (type-theory.sysᵉ Aᵉ) Xᵉ)
  weakening-dttᵉ Aᵉ = weakening.typeᵉ (type-theory.Wᵉ Aᵉ)
```

### The slice of a dependent type theory

Weᵉ introduceᵉ theᵉ sliceᵉ ofᵉ aᵉ dependentᵉ typeᵉ theory.ᵉ

```agda
  slice-dttᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ)
    (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ)) →
    type-theoryᵉ l1ᵉ l2ᵉ
  type-theory.sysᵉ (slice-dttᵉ Aᵉ Xᵉ) =
    system.sliceᵉ (type-theory.sysᵉ Aᵉ) Xᵉ
  type-theory.Wᵉ (slice-dttᵉ Aᵉ Xᵉ) =
    weakening.sliceᵉ (type-theory.Wᵉ Aᵉ) Xᵉ
  type-theory.Sᵉ (slice-dttᵉ Aᵉ Xᵉ) =
    substitution.sliceᵉ (type-theory.Sᵉ Aᵉ) Xᵉ
  type-theory.δᵉ (slice-dttᵉ Aᵉ Xᵉ) =
    generic-element.sliceᵉ (type-theory.δᵉ Aᵉ) Xᵉ
  type-theory.WWᵉ (slice-dttᵉ Aᵉ Xᵉ) =
    weakening-preserves-weakening.sliceᵉ (type-theory.WWᵉ Aᵉ) Xᵉ
  type-theory.SSᵉ (slice-dttᵉ Aᵉ Xᵉ) =
    substitution-preserves-substitution.sliceᵉ (type-theory.SSᵉ Aᵉ) Xᵉ
  type-theory.WSᵉ (slice-dttᵉ Aᵉ Xᵉ) =
    weakening-preserves-substitution.sliceᵉ (type-theory.WSᵉ Aᵉ) Xᵉ
  type-theory.SWᵉ (slice-dttᵉ Aᵉ Xᵉ) =
    substitution-preserves-weakening.sliceᵉ (type-theory.SWᵉ Aᵉ) Xᵉ
  type-theory.Wδᵉ (slice-dttᵉ Aᵉ Xᵉ) =
    weakening-preserves-generic-element.sliceᵉ (type-theory.Wδᵉ Aᵉ) Xᵉ
  type-theory.Sδᵉ (slice-dttᵉ Aᵉ Xᵉ) =
    substitution-preserves-generic-element.sliceᵉ (type-theory.Sδᵉ Aᵉ) Xᵉ
  type-theory.S!Wᵉ (slice-dttᵉ Aᵉ Xᵉ) =
    substitution-cancels-weakening.sliceᵉ (type-theory.S!Wᵉ Aᵉ) Xᵉ
  type-theory.δidᵉ (slice-dttᵉ Aᵉ Xᵉ) =
    generic-element-is-identity.sliceᵉ (type-theory.δidᵉ Aᵉ) Xᵉ
  type-theory.Sδ!ᵉ (slice-dttᵉ Aᵉ Xᵉ) =
    substitution-by-generic-element.sliceᵉ (type-theory.Sδ!ᵉ Aᵉ) Xᵉ
```

### Morphisms of dependent type theories

```agda
  record hom-dttᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) (Bᵉ : type-theoryᵉ l3ᵉ l4ᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    field
      sysᵉ :
        hom-systemᵉ
          ( type-theory.sysᵉ Aᵉ)
          ( type-theory.sysᵉ Bᵉ)
      Wᵉ :
        preserves-weakeningᵉ
          ( type-theory.Wᵉ Aᵉ)
          ( type-theory.Wᵉ Bᵉ)
          ( sysᵉ)
      Sᵉ :
        preserves-substitutionᵉ
          ( type-theory.Sᵉ Aᵉ)
          ( type-theory.Sᵉ Bᵉ)
          ( sysᵉ)
      δᵉ :
        preserves-generic-elementᵉ
          ( type-theory.δᵉ Aᵉ)
          ( type-theory.δᵉ Bᵉ)
          ( Wᵉ)

  hom-slice-dttᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ} {Bᵉ : type-theoryᵉ l3ᵉ l4ᵉ}
    (fᵉ : hom-dttᵉ Aᵉ Bᵉ) (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ)) →
    hom-dttᵉ
      ( slice-dttᵉ Aᵉ Xᵉ)
      ( slice-dttᵉ Bᵉ (section-system.typeᵉ (hom-dtt.sysᵉ fᵉ) Xᵉ))
  hom-dtt.sysᵉ (hom-slice-dttᵉ fᵉ Xᵉ) =
    section-system.sliceᵉ (hom-dtt.sysᵉ fᵉ) Xᵉ
  hom-dtt.Wᵉ (hom-slice-dttᵉ fᵉ Xᵉ) =
    preserves-weakening.sliceᵉ (hom-dtt.Wᵉ fᵉ) Xᵉ
  hom-dtt.Sᵉ (hom-slice-dttᵉ fᵉ Xᵉ) =
    preserves-substitution.sliceᵉ (hom-dtt.Sᵉ fᵉ) Xᵉ
  hom-dtt.δᵉ (hom-slice-dttᵉ fᵉ Xᵉ) =
    preserves-generic-element.sliceᵉ (hom-dtt.δᵉ fᵉ) Xᵉ
```

### The identity morphism of a dependent type theory

```agda
  preserves-weakening-id-hom-systemᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Wᵉ : weakeningᵉ Aᵉ) →
    preserves-weakeningᵉ Wᵉ Wᵉ (id-hom-systemᵉ Aᵉ)
  preserves-weakening.typeᵉ (preserves-weakening-id-hom-systemᵉ Wᵉ) Xᵉ =
    concat-htpy-hom-systemᵉ
      ( left-unit-law-comp-hom-systemᵉ (weakening.typeᵉ Wᵉ Xᵉ))
      ( inv-htpy-hom-systemᵉ
        ( right-unit-law-comp-hom-systemᵉ (weakening.typeᵉ Wᵉ Xᵉ)))
  preserves-weakening.sliceᵉ (preserves-weakening-id-hom-systemᵉ Wᵉ) Xᵉ =
    preserves-weakening-id-hom-systemᵉ (weakening.sliceᵉ Wᵉ Xᵉ)

  preserves-substitution-id-hom-systemᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Sᵉ : substitutionᵉ Aᵉ) →
    preserves-substitutionᵉ Sᵉ Sᵉ (id-hom-systemᵉ Aᵉ)
  preserves-substitution.typeᵉ (preserves-substitution-id-hom-systemᵉ Sᵉ) xᵉ =
    concat-htpy-hom-systemᵉ
      ( left-unit-law-comp-hom-systemᵉ (substitution.typeᵉ Sᵉ xᵉ))
      ( inv-htpy-hom-systemᵉ
        ( right-unit-law-comp-hom-systemᵉ (substitution.typeᵉ Sᵉ xᵉ)))
  preserves-substitution.sliceᵉ (preserves-substitution-id-hom-systemᵉ Sᵉ) Xᵉ =
    preserves-substitution-id-hom-systemᵉ (substitution.sliceᵉ Sᵉ Xᵉ)

  preserves-generic-element-id-hom-systemᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Wᵉ : weakeningᵉ Aᵉ}
    (δᵉ : generic-elementᵉ Wᵉ) →
    preserves-generic-elementᵉ δᵉ δᵉ
      ( preserves-weakening-id-hom-systemᵉ Wᵉ)
  preserves-generic-element.typeᵉ
    ( preserves-generic-element-id-hom-systemᵉ δᵉ) Xᵉ = reflᵉ
  preserves-generic-element.sliceᵉ
    ( preserves-generic-element-id-hom-systemᵉ δᵉ) Xᵉ =
    preserves-generic-element-id-hom-systemᵉ (generic-element.sliceᵉ δᵉ Xᵉ)

  id-hom-dttᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) → hom-dttᵉ Aᵉ Aᵉ
  hom-dtt.sysᵉ (id-hom-dttᵉ Aᵉ) =
    id-hom-systemᵉ (type-theory.sysᵉ Aᵉ)
  hom-dtt.Wᵉ (id-hom-dttᵉ Aᵉ) =
    preserves-weakening-id-hom-systemᵉ (type-theory.Wᵉ Aᵉ)
  hom-dtt.Sᵉ (id-hom-dttᵉ Aᵉ) =
    preserves-substitution-id-hom-systemᵉ (type-theory.Sᵉ Aᵉ)
  hom-dtt.δᵉ (id-hom-dttᵉ Aᵉ) =
    preserves-generic-element-id-hom-systemᵉ (type-theory.δᵉ Aᵉ)
```

### The composition of morphisms of type theories

```agda
  preserves-weakening-comp-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    {Cᵉ : systemᵉ l5ᵉ l6ᵉ} {gᵉ : hom-systemᵉ Bᵉ Cᵉ} {fᵉ : hom-systemᵉ Aᵉ Bᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} {WBᵉ : weakeningᵉ Bᵉ} {WCᵉ : weakeningᵉ Cᵉ} →
    preserves-weakeningᵉ WBᵉ WCᵉ gᵉ → preserves-weakeningᵉ WAᵉ WBᵉ fᵉ →
    preserves-weakeningᵉ WAᵉ WCᵉ (comp-hom-systemᵉ gᵉ fᵉ)
  preserves-weakening.typeᵉ
    ( preserves-weakening-comp-hom-systemᵉ {gᵉ = gᵉ} {fᵉ} {WAᵉ} {WBᵉ} {WCᵉ} Wgᵉ Wfᵉ)
    ( Xᵉ) =
    concat-htpy-hom-systemᵉ
      ( associative-comp-hom-systemᵉ
        ( section-system.sliceᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ))
        ( section-system.sliceᵉ fᵉ Xᵉ)
        ( weakening.typeᵉ WAᵉ Xᵉ))
      ( concat-htpy-hom-systemᵉ
        ( left-whisker-comp-hom-systemᵉ
          ( section-system.sliceᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ))
          ( preserves-weakening.typeᵉ Wfᵉ Xᵉ))
        ( concat-htpy-hom-systemᵉ
          ( inv-htpy-hom-systemᵉ
            ( associative-comp-hom-systemᵉ
              ( section-system.sliceᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ))
              ( weakening.typeᵉ WBᵉ (section-system.typeᵉ fᵉ Xᵉ))
              ( fᵉ)))
          ( concat-htpy-hom-systemᵉ
            ( right-whisker-comp-hom-systemᵉ
              ( preserves-weakening.typeᵉ Wgᵉ (section-system.typeᵉ fᵉ Xᵉ))
              ( fᵉ))
            ( associative-comp-hom-systemᵉ
              ( weakening.typeᵉ WCᵉ
                ( section-system.typeᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ)))
              ( gᵉ)
              ( fᵉ)))))
  preserves-weakening.sliceᵉ
    ( preserves-weakening-comp-hom-systemᵉ {fᵉ = fᵉ} Wgᵉ Wfᵉ) Xᵉ =
    preserves-weakening-comp-hom-systemᵉ
      ( preserves-weakening.sliceᵉ Wgᵉ (section-system.typeᵉ fᵉ Xᵉ))
      ( preserves-weakening.sliceᵉ Wfᵉ Xᵉ)

  preserves-substitution-comp-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    {Cᵉ : systemᵉ l5ᵉ l6ᵉ} {gᵉ : hom-systemᵉ Bᵉ Cᵉ} {fᵉ : hom-systemᵉ Aᵉ Bᵉ}
    {SAᵉ : substitutionᵉ Aᵉ} {SBᵉ : substitutionᵉ Bᵉ} {SCᵉ : substitutionᵉ Cᵉ} →
    preserves-substitutionᵉ SBᵉ SCᵉ gᵉ → preserves-substitutionᵉ SAᵉ SBᵉ fᵉ →
    preserves-substitutionᵉ SAᵉ SCᵉ (comp-hom-systemᵉ gᵉ fᵉ)
  preserves-substitution.typeᵉ
    ( preserves-substitution-comp-hom-systemᵉ
      {gᵉ = gᵉ} {fᵉ} {SAᵉ} {SBᵉ} {SCᵉ} Sgᵉ Sfᵉ) {Xᵉ} xᵉ =
    concat-htpy-hom-systemᵉ
      ( associative-comp-hom-systemᵉ gᵉ fᵉ (substitution.typeᵉ SAᵉ xᵉ))
      ( concat-htpy-hom-systemᵉ
        ( left-whisker-comp-hom-systemᵉ gᵉ
          ( preserves-substitution.typeᵉ Sfᵉ xᵉ))
        ( concat-htpy-hom-systemᵉ
          ( inv-htpy-hom-systemᵉ
            ( associative-comp-hom-systemᵉ gᵉ
              ( substitution.typeᵉ SBᵉ
                ( section-system.elementᵉ fᵉ xᵉ))
              ( section-system.sliceᵉ fᵉ Xᵉ)))
          ( concat-htpy-hom-systemᵉ
            ( right-whisker-comp-hom-systemᵉ
              ( preserves-substitution.typeᵉ Sgᵉ
                ( section-system.elementᵉ fᵉ xᵉ))
              ( section-system.sliceᵉ fᵉ Xᵉ))
            ( associative-comp-hom-systemᵉ
              ( substitution.typeᵉ SCᵉ
                ( section-system.elementᵉ gᵉ (section-system.elementᵉ fᵉ xᵉ)))
              ( section-system.sliceᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ))
              ( section-system.sliceᵉ fᵉ Xᵉ)))))
  preserves-substitution.sliceᵉ
    ( preserves-substitution-comp-hom-systemᵉ {fᵉ = fᵉ} Sgᵉ Sfᵉ) Xᵉ =
    preserves-substitution-comp-hom-systemᵉ
      ( preserves-substitution.sliceᵉ Sgᵉ (section-system.typeᵉ fᵉ Xᵉ))
      ( preserves-substitution.sliceᵉ Sfᵉ Xᵉ)

  preserves-generic-element-comp-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    {Cᵉ : systemᵉ l5ᵉ l6ᵉ} {gᵉ : hom-systemᵉ Bᵉ Cᵉ} {fᵉ : hom-systemᵉ Aᵉ Bᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} {WBᵉ : weakeningᵉ Bᵉ} {WCᵉ : weakeningᵉ Cᵉ} →
    {δAᵉ : generic-elementᵉ WAᵉ} {δBᵉ : generic-elementᵉ WBᵉ}
    {δCᵉ : generic-elementᵉ WCᵉ} →
    {Wgᵉ : preserves-weakeningᵉ WBᵉ WCᵉ gᵉ} {Wfᵉ : preserves-weakeningᵉ WAᵉ WBᵉ fᵉ} →
    (δgᵉ : preserves-generic-elementᵉ δBᵉ δCᵉ Wgᵉ)
    (δfᵉ : preserves-generic-elementᵉ δAᵉ δBᵉ Wfᵉ) →
    preserves-generic-elementᵉ
      δAᵉ δCᵉ (preserves-weakening-comp-hom-systemᵉ Wgᵉ Wfᵉ)
  preserves-generic-element.typeᵉ
    ( preserves-generic-element-comp-hom-systemᵉ
      {Aᵉ = Aᵉ} {Bᵉ} {Cᵉ} {gᵉ} {fᵉ} {WAᵉ} {WBᵉ} {WCᵉ} {δAᵉ} {δBᵉ} {δCᵉ} {Wgᵉ} {Wfᵉ} δgᵉ δfᵉ) Xᵉ =
    ( apᵉ
      ( λ tᵉ →
        trᵉ
          ( system.elementᵉ
            ( system.sliceᵉ Cᵉ (section-system.typeᵉ (comp-hom-systemᵉ gᵉ fᵉ) Xᵉ)))
          ( tᵉ)
          ( section-system.elementᵉ
            ( section-system.sliceᵉ (comp-hom-systemᵉ gᵉ fᵉ) Xᵉ)
            ( generic-element.typeᵉ δAᵉ Xᵉ)))
      ( left-whisker-concatᵉ αᵉ right-unitᵉ)) ∙ᵉ
    ( ( tr-concatᵉ
        { Bᵉ =
          system.elementᵉ
            ( system.sliceᵉ Cᵉ (section-system.typeᵉ (comp-hom-systemᵉ gᵉ fᵉ) Xᵉ))}
        ( αᵉ)
        ( βᵉ)
        ( section-system.elementᵉ
          ( section-system.sliceᵉ (comp-hom-systemᵉ gᵉ fᵉ) Xᵉ)
          ( generic-element.typeᵉ δAᵉ Xᵉ))) ∙ᵉ
      ( ( apᵉ
          ( trᵉ
            ( system.elementᵉ
              ( system.sliceᵉ Cᵉ
                ( section-system.typeᵉ (comp-hom-systemᵉ gᵉ fᵉ) Xᵉ)))
            ( βᵉ))
          ( ( γᵉ ( section-system.typeᵉ (preserves-weakening.typeᵉ Wfᵉ Xᵉ) Xᵉ)
                ( section-system.elementᵉ
                  ( section-system.sliceᵉ fᵉ Xᵉ)
                  ( generic-element.typeᵉ δAᵉ Xᵉ))) ∙ᵉ
            ( apᵉ
              ( section-system.elementᵉ
                ( section-system.sliceᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ)))
              ( preserves-generic-element.typeᵉ δfᵉ Xᵉ)))) ∙ᵉ
        ( preserves-generic-element.typeᵉ δgᵉ (section-system.typeᵉ fᵉ Xᵉ))))
    where
    αᵉ =
      apᵉ
        ( section-system.typeᵉ
          ( section-system.sliceᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ)))
        ( section-system.typeᵉ (preserves-weakening.typeᵉ Wfᵉ Xᵉ) Xᵉ)
    βᵉ =
      section-system.typeᵉ
        ( preserves-weakening.typeᵉ Wgᵉ (section-system.typeᵉ fᵉ Xᵉ))
        ( section-system.typeᵉ fᵉ Xᵉ)
    γᵉ :
      { Yᵉ : system.typeᵉ (system.sliceᵉ Bᵉ (section-system.typeᵉ fᵉ Xᵉ))}
      ( pᵉ :
        Idᵉ
          ( Yᵉ)
          ( section-system.typeᵉ
            ( comp-hom-systemᵉ
              ( weakening.typeᵉ WBᵉ (section-system.typeᵉ fᵉ Xᵉ))
              ( fᵉ))
            ( Xᵉ)))
      ( uᵉ : system.elementᵉ (system.sliceᵉ Bᵉ (section-system.typeᵉ fᵉ Xᵉ)) Yᵉ) →
        Idᵉ
          ( trᵉ
            ( system.elementᵉ
              ( system.sliceᵉ
                ( Cᵉ)
                ( section-system.typeᵉ (comp-hom-systemᵉ gᵉ fᵉ) Xᵉ)))
            ( apᵉ
              ( section-system.typeᵉ
                ( section-system.sliceᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ)))
              ( pᵉ))
            ( section-system.elementᵉ
              ( section-system.sliceᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ))
              ( uᵉ)))
          ( section-system.elementᵉ
            ( section-system.sliceᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ))
            ( trᵉ
              ( system.elementᵉ (system.sliceᵉ Bᵉ (section-system.typeᵉ fᵉ Xᵉ)))
              ( pᵉ)
              ( uᵉ)))
    γᵉ reflᵉ uᵉ = reflᵉ
  preserves-generic-element.sliceᵉ
    ( preserves-generic-element-comp-hom-systemᵉ {fᵉ = fᵉ} δgᵉ δfᵉ) Xᵉ =
    preserves-generic-element-comp-hom-systemᵉ
      ( preserves-generic-element.sliceᵉ δgᵉ (section-system.typeᵉ fᵉ Xᵉ))
      ( preserves-generic-element.sliceᵉ δfᵉ Xᵉ)

  comp-hom-dttᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
    {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ} {Bᵉ : type-theoryᵉ l3ᵉ l4ᵉ}
    {Cᵉ : type-theoryᵉ l5ᵉ l6ᵉ} →
    hom-dttᵉ Bᵉ Cᵉ → hom-dttᵉ Aᵉ Bᵉ → hom-dttᵉ Aᵉ Cᵉ
  hom-dtt.sysᵉ (comp-hom-dttᵉ gᵉ fᵉ) =
    comp-hom-systemᵉ (hom-dtt.sysᵉ gᵉ) (hom-dtt.sysᵉ fᵉ)
  hom-dtt.Wᵉ (comp-hom-dttᵉ gᵉ fᵉ) =
    preserves-weakening-comp-hom-systemᵉ (hom-dtt.Wᵉ gᵉ) (hom-dtt.Wᵉ fᵉ)
  hom-dtt.Sᵉ (comp-hom-dttᵉ gᵉ fᵉ) =
    preserves-substitution-comp-hom-systemᵉ (hom-dtt.Sᵉ gᵉ) (hom-dtt.Sᵉ fᵉ)
  hom-dtt.δᵉ (comp-hom-dttᵉ gᵉ fᵉ) =
    preserves-generic-element-comp-hom-systemᵉ (hom-dtt.δᵉ gᵉ) (hom-dtt.δᵉ fᵉ)
```

### Homotopies of morphisms of dependent type theories

```agda
  htpy-hom-dttᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ} {Bᵉ : type-theoryᵉ l3ᵉ l4ᵉ}
    (fᵉ gᵉ : hom-dttᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-hom-dttᵉ fᵉ gᵉ = htpy-hom-systemᵉ (hom-dtt.sysᵉ fᵉ) (hom-dtt.sysᵉ gᵉ)

  left-unit-law-comp-hom-dttᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ} {Bᵉ : type-theoryᵉ l3ᵉ l4ᵉ}
    (fᵉ : hom-dttᵉ Aᵉ Bᵉ) → htpy-hom-dttᵉ (comp-hom-dttᵉ (id-hom-dttᵉ Bᵉ) fᵉ) fᵉ
  left-unit-law-comp-hom-dttᵉ fᵉ =
    left-unit-law-comp-hom-systemᵉ (hom-dtt.sysᵉ fᵉ)

  right-unit-law-comp-hom-dttᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ} {Bᵉ : type-theoryᵉ l3ᵉ l4ᵉ}
    (fᵉ : hom-dttᵉ Aᵉ Bᵉ) → htpy-hom-dttᵉ (comp-hom-dttᵉ fᵉ (id-hom-dttᵉ Aᵉ)) fᵉ
  right-unit-law-comp-hom-dttᵉ fᵉ =
    right-unit-law-comp-hom-systemᵉ (hom-dtt.sysᵉ fᵉ)

  associative-comp-hom-dttᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
    {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ} {Bᵉ : type-theoryᵉ l3ᵉ l4ᵉ}
    {Cᵉ : type-theoryᵉ l5ᵉ l6ᵉ} {Dᵉ : type-theoryᵉ l7ᵉ l8ᵉ}
    (hᵉ : hom-dttᵉ Cᵉ Dᵉ) (gᵉ : hom-dttᵉ Bᵉ Cᵉ) (fᵉ : hom-dttᵉ Aᵉ Bᵉ) →
    htpy-hom-dttᵉ
      ( comp-hom-dttᵉ (comp-hom-dttᵉ hᵉ gᵉ) fᵉ)
      ( comp-hom-dttᵉ hᵉ (comp-hom-dttᵉ gᵉ fᵉ))
  associative-comp-hom-dttᵉ hᵉ gᵉ fᵉ =
    associative-comp-hom-systemᵉ
      (hom-dtt.sysᵉ hᵉ) (hom-dtt.sysᵉ gᵉ) (hom-dtt.sysᵉ fᵉ)
```

---ᵉ

### Simple type theories

```agda
  record is-simple-type-theoryᵉ
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) : UUᵉ l1ᵉ
    where
    coinductiveᵉ
    field
      typeᵉ :
        (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ)) →
        is-equivᵉ
          ( section-system.typeᵉ
            ( weakening.typeᵉ (type-theory.Wᵉ Aᵉ) Xᵉ))
      sliceᵉ :
        (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ)) →
        is-simple-type-theoryᵉ (slice-dttᵉ Aᵉ Xᵉ)

  record simple-type-theoryᵉ (l1ᵉ l2ᵉ : Level) : UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
    where
    field
      dttᵉ : type-theoryᵉ l1ᵉ l2ᵉ
      is-simpleᵉ : is-simple-type-theoryᵉ dttᵉ
```

### The condition that the action on elements of a morphism of dependent type theories is an equivalence

Weᵉ introduceᵉ theᵉ conditionᵉ thatᵉ theᵉ actionᵉ onᵉ elementsᵉ ofᵉ aᵉ morphismᵉ ofᵉ
dependentᵉ typeᵉ theoriesᵉ isᵉ anᵉ equivalence.ᵉ

```agda
  record is-equiv-on-elements-hom-systemᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : systemᵉ l1ᵉ l2ᵉ) (Bᵉ : systemᵉ l3ᵉ l4ᵉ)
    (hᵉ : hom-systemᵉ Aᵉ Bᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) → is-equivᵉ (section-system.elementᵉ hᵉ {Xᵉ})
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        is-equiv-on-elements-hom-systemᵉ
          ( system.sliceᵉ Aᵉ Xᵉ)
          ( system.sliceᵉ Bᵉ (section-system.typeᵉ hᵉ Xᵉ))
          ( section-system.sliceᵉ hᵉ Xᵉ)
```

### Unary type theories

```agda
  record unary-type-theoryᵉ
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) : UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
    where
    field
      dttᵉ : type-theoryᵉ l1ᵉ l2ᵉ
      is-simpleᵉ : is-simple-type-theoryᵉ Aᵉ
      is-unaryᵉ :
        (Xᵉ Yᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ)) →
        is-equiv-on-elements-hom-systemᵉ
          ( system.sliceᵉ (type-theory.sysᵉ Aᵉ) Yᵉ)
          ( system.sliceᵉ
            ( system.sliceᵉ (type-theory.sysᵉ Aᵉ) Xᵉ)
            ( section-system.typeᵉ
              ( weakening.typeᵉ (type-theory.Wᵉ Aᵉ) Xᵉ) Yᵉ))
          ( section-system.sliceᵉ
            ( weakening.typeᵉ (type-theory.Wᵉ Aᵉ) Xᵉ)
            ( Yᵉ))
```

### Proof irrelevant type theories

```agda
  record is-proof-irrelevant-type-theoryᵉ
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ)) →
        is-propᵉ (system.elementᵉ (type-theory.sysᵉ Aᵉ) Xᵉ)
      sliceᵉ :
        (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ)) →
        is-proof-irrelevant-type-theoryᵉ (slice-dttᵉ Aᵉ Xᵉ)
```

---ᵉ

```agda
  system-Sliceᵉ : {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → systemᵉ (lsuc lᵉ) lᵉ
  system.typeᵉ (system-Sliceᵉ {lᵉ} Xᵉ) = Xᵉ → UUᵉ lᵉ
  system.elementᵉ (system-Sliceᵉ Xᵉ) Yᵉ = (xᵉ : Xᵉ) → Yᵉ xᵉ
  system.sliceᵉ (system-Sliceᵉ Xᵉ) Yᵉ = system-Sliceᵉ (Σᵉ Xᵉ Yᵉ)

  {-ᵉ
  hom-system-weakening-system-Sliceᵉ :
    {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) (Yᵉ : Xᵉ → UUᵉ lᵉ) →
    hom-systemᵉ (system-Sliceᵉ Xᵉ) (system-Sliceᵉ (Σᵉ Xᵉ Yᵉ))
  section-system.typeᵉ (hom-system-weakening-system-Sliceᵉ Xᵉ Yᵉ) Zᵉ (pairᵉ xᵉ yᵉ) =
    Zᵉ xᵉ
  section-system.elementᵉ
    (hom-system-weakening-system-Sliceᵉ Xᵉ Yᵉ) Zᵉ gᵉ (pairᵉ xᵉ yᵉ) =
    gᵉ xᵉ
  section-system.typeᵉ
    (section-system.sliceᵉ (hom-system-weakening-system-Sliceᵉ Xᵉ Yᵉ) Zᵉ)
    Wᵉ (pairᵉ (pairᵉ xᵉ yᵉ) zᵉ) =
    Wᵉ (pairᵉ xᵉ zᵉ)
  section-system.elementᵉ
    (section-system.sliceᵉ (hom-system-weakening-system-Sliceᵉ Xᵉ Yᵉ) Zᵉ)
    Wᵉ hᵉ (pairᵉ (pairᵉ xᵉ yᵉ) zᵉ) =
    hᵉ (pairᵉ xᵉ zᵉ)
  section-system.sliceᵉ
    (section-system.sliceᵉ (hom-system-weakening-system-Sliceᵉ Xᵉ Yᵉ) Zᵉ) Wᵉ =
    {!section-system.sliceᵉ (hom-system-weakening-system-Sliceᵉ Xᵉ Yᵉ) ?!ᵉ}

  weakening-system-Sliceᵉ :
    {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → weakeningᵉ (system-Sliceᵉ Xᵉ)
  weakening.typeᵉ (weakening-system-Sliceᵉ Xᵉ) Yᵉ =
    hom-system-weakening-system-Sliceᵉ Xᵉ Yᵉ
  weakening.sliceᵉ (weakening-system-Sliceᵉ Xᵉ) = {!!ᵉ}

  system-UUᵉ : (lᵉ : Level) → systemᵉ (lsuc lᵉ) lᵉ
  system.typeᵉ (system-UUᵉ lᵉ) = UUᵉ lᵉ
  system.elementᵉ (system-UUᵉ lᵉ) Xᵉ = Xᵉ
  system.sliceᵉ (system-UUᵉ lᵉ) Xᵉ = system-Sliceᵉ Xᵉ

  weakening-type-UUᵉ :
    {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) →
    hom-systemᵉ (system-UUᵉ lᵉ) (system.sliceᵉ (system-UUᵉ lᵉ) Xᵉ)
  section-system.typeᵉ (weakening-type-UUᵉ Xᵉ) Yᵉ xᵉ = Yᵉ
  section-system.elementᵉ (weakening-type-UUᵉ Xᵉ) Yᵉ yᵉ xᵉ = yᵉ
  section-system.sliceᵉ (weakening-type-UUᵉ Xᵉ) Yᵉ = {!!ᵉ}

  weakening-UUᵉ : (lᵉ : Level) → weakeningᵉ (system-UUᵉ lᵉ)
  section-system.typeᵉ (weakening.typeᵉ (weakening-UUᵉ lᵉ) Xᵉ) Yᵉ xᵉ = Yᵉ
  section-system.elementᵉ (weakening.typeᵉ (weakening-UUᵉ lᵉ) Xᵉ) Yᵉ yᵉ xᵉ = yᵉ
  section-system.typeᵉ
    (section-system.sliceᵉ (weakening.typeᵉ (weakening-UUᵉ lᵉ) Xᵉ) Yᵉ) Zᵉ tᵉ =
    Zᵉ (pr2ᵉ tᵉ)
  section-system.elementᵉ
    ( section-system.sliceᵉ (weakening.typeᵉ (weakening-UUᵉ lᵉ) Xᵉ) Yᵉ) Zᵉ fᵉ tᵉ =
    fᵉ (pr2ᵉ tᵉ)
  section-system.sliceᵉ
    (section-system.sliceᵉ (weakening.typeᵉ (weakening-UUᵉ lᵉ) Xᵉ) Yᵉ) Zᵉ =
    {!!ᵉ}
  section-system.typeᵉ
    ( weakening.typeᵉ (weakening.sliceᵉ (weakening-UUᵉ lᵉ) Xᵉ) Yᵉ) Zᵉ (pairᵉ xᵉ yᵉ) =
    Zᵉ xᵉ
  section-system.elementᵉ
    ( weakening.typeᵉ (weakening.sliceᵉ (weakening-UUᵉ lᵉ) Xᵉ) Yᵉ) Zᵉ fᵉ (pairᵉ xᵉ yᵉ) =
    fᵉ xᵉ
  section-system.sliceᵉ
    (weakening.typeᵉ (weakening.sliceᵉ (weakening-UUᵉ lᵉ) Xᵉ) Yᵉ) Zᵉ =
    {!!ᵉ}
  weakening.sliceᵉ (weakening.sliceᵉ (weakening-UUᵉ lᵉ) Xᵉ) Yᵉ =
    weakening.sliceᵉ (weakening-UUᵉ lᵉ) (Σᵉ Xᵉ Yᵉ)
-ᵉ}
```

---ᵉ

### Dependent type theories with Π-types

Weᵉ defineᵉ whatᵉ itᵉ meansᵉ forᵉ aᵉ dependentᵉ typeᵉ theoryᵉ to haveᵉ Π-types.ᵉ

```agda
  record function-typesᵉ
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      sysᵉ :
        (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ)) →
        hom-dttᵉ (slice-dttᵉ Aᵉ Xᵉ) Aᵉ
      appᵉ :
        (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ)) →
        is-equiv-on-elements-hom-systemᵉ
          ( type-theory.sysᵉ (slice-dttᵉ Aᵉ Xᵉ))
          ( type-theory.sysᵉ Aᵉ)
          ( hom-dtt.sysᵉ (sysᵉ Xᵉ))
      sliceᵉ :
        (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ)) →
        function-typesᵉ (slice-dttᵉ Aᵉ Xᵉ)

  {-ᵉ
  record preserves-function-typesᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ}
    {Bᵉ : type-theoryᵉ l3ᵉ l4ᵉ} (ΠAᵉ : function-typesᵉ Aᵉ)
    (ΠBᵉ : function-typesᵉ Bᵉ) (hᵉ : hom-dttᵉ Aᵉ Bᵉ) : UUᵉ {!!ᵉ}
    where
    coinductiveᵉ
    field
      sysᵉ   : {!!ᵉ}
      sliceᵉ : {!!ᵉ}
  -ᵉ}
```

---ᵉ

```agda
  record natural-numbersᵉ
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) (Πᵉ : function-typesᵉ Aᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    field
      Nᵉ : closed-type-dttᵉ Aᵉ
      zeroᵉ : global-element-dttᵉ Aᵉ Nᵉ
      succᵉ :
        global-element-dttᵉ Aᵉ
          ( section-system.typeᵉ
            ( hom-dtt.sysᵉ (function-types.sysᵉ Πᵉ Nᵉ))
            ( section-system.typeᵉ
              ( weakening.typeᵉ (type-theory.Wᵉ Aᵉ) Nᵉ)
              ( Nᵉ)))

  {-ᵉ
  natural-numbers-sliceᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) (Πᵉ : function-typesᵉ Aᵉ)
    (Nᵉ : natural-numbersᵉ Aᵉ Πᵉ) (Xᵉ : closed-type-dttᵉ Aᵉ) →
    natural-numbersᵉ (slice-dttᵉ Aᵉ Xᵉ) (function-types.sliceᵉ Πᵉ Xᵉ)
  natural-numbers.Nᵉ (natural-numbers-sliceᵉ Aᵉ Πᵉ Nᵉ Xᵉ) =
    section-system.typeᵉ
      ( weakening.typeᵉ (type-theory.Wᵉ Aᵉ) Xᵉ)
      ( natural-numbers.Nᵉ Nᵉ)
  natural-numbers.zeroᵉ (natural-numbers-sliceᵉ Aᵉ Πᵉ Nᵉ Xᵉ) =
    section-system.elementᵉ
      ( weakening.typeᵉ (type-theory.Wᵉ Aᵉ) Xᵉ)
      ( natural-numbers.Nᵉ Nᵉ)
      ( natural-numbers.zeroᵉ Nᵉ)
  natural-numbers.succᵉ (natural-numbers-sliceᵉ Aᵉ Πᵉ Nᵉ Xᵉ) =
    trᵉ ( system.elementᵉ (type-theory.sysᵉ (slice-dttᵉ Aᵉ Xᵉ)))
       {!ᵉ (section-system.typeᵉ
          (preserves-weakening.typeᵉ
          (hom-dtt.Wᵉ (function-types.sysᵉ Πᵉ (natural-numbers.Nᵉ Nᵉ))) ?ᵉ) ?)!ᵉ}
    {-ᵉ
    Idᵉ ( section-system.typeᵉ
         ( weakening.typeᵉ (type-theory.Wᵉ Aᵉ) Xᵉ)
         ( section-system.typeᵉ
           ( hom-dtt.sysᵉ (function-types.sysᵉ Πᵉ (natural-numbers.Nᵉ Nᵉ)))
           ( section-system.typeᵉ
             ( weakening.typeᵉ (type-theory.Wᵉ Aᵉ) (natural-numbers.Nᵉ Nᵉ))
             (natural-numbers.Nᵉ Nᵉ))))
       ( section-system.typeᵉ
         ( hom-dtt.sysᵉ
           ( function-types.sysᵉ (function-types.sliceᵉ Πᵉ Xᵉ)
             ( natural-numbers.Nᵉ (natural-numbers-sliceᵉ Aᵉ Πᵉ Nᵉ Xᵉ))))
         ( section-system.typeᵉ
           ( weakening.typeᵉ
             ( type-theory.Wᵉ (slice-dttᵉ Aᵉ Xᵉ))
             ( natural-numbers.Nᵉ (natural-numbers-sliceᵉ Aᵉ Πᵉ Nᵉ Xᵉ)))
           ( natural-numbers.Nᵉ (natural-numbers-sliceᵉ Aᵉ Πᵉ Nᵉ Xᵉ))))
  -ᵉ}
       ( section-system.elementᵉ
         ( weakening.typeᵉ (type-theory.Wᵉ Aᵉ) Xᵉ)
         ( section-system.typeᵉ
           ( hom-dtt.sysᵉ (function-types.sysᵉ Πᵉ (natural-numbers.Nᵉ Nᵉ)))
           ( section-system.typeᵉ
             ( weakening.typeᵉ (type-theory.Wᵉ Aᵉ) (natural-numbers.Nᵉ Nᵉ))
             ( natural-numbers.Nᵉ Nᵉ)))
         ( natural-numbers.succᵉ Nᵉ))
  -ᵉ}
```

---ᵉ

```agda
  {-ᵉ
  concat-htpy-hom-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ B'ᵉ B''ᵉ : systemᵉ l3ᵉ l4ᵉ}
    (pᵉ : Idᵉ Bᵉ B'ᵉ) (qᵉ : Idᵉ B'ᵉ B''ᵉ) {fᵉ : hom-systemᵉ Aᵉ Bᵉ} {gᵉ : hom-systemᵉ Aᵉ B'ᵉ}
    {hᵉ : hom-systemᵉ Aᵉ B''ᵉ} → htpy-hom-system'ᵉ pᵉ fᵉ gᵉ → htpy-hom-system'ᵉ qᵉ gᵉ hᵉ →
    htpy-hom-system'ᵉ (pᵉ ∙ᵉ qᵉ) fᵉ hᵉ
  htpy-hom-system'.typeᵉ (concat-htpy-hom-system'ᵉ reflᵉ reflᵉ Hᵉ Kᵉ) =
    htpy-hom-system'.typeᵉ Hᵉ ∙hᵉ htpy-hom-system'.typeᵉ Kᵉ
  htpy-hom-system'.elementᵉ
    ( concat-htpy-hom-system'ᵉ {Aᵉ = Aᵉ} {Bᵉ} {.Bᵉ} reflᵉ reflᵉ {fᵉ} Hᵉ Kᵉ) Xᵉ xᵉ =
    ( ( tr-concatᵉ
        ( section-system.typeᵉ Hᵉ Xᵉ)
        ( section-system.typeᵉ Kᵉ Xᵉ)
        ( section-system.elementᵉ (trᵉ (hom-systemᵉ Aᵉ) reflᵉ fᵉ) Xᵉ xᵉ)) ∙ᵉ
      ( apᵉ
        ( trᵉ (system.elementᵉ Bᵉ) (section-system.typeᵉ Kᵉ Xᵉ))
        ( section-system.elementᵉ Hᵉ Xᵉ xᵉ))) ∙ᵉ
    ( section-system.elementᵉ Kᵉ Xᵉ xᵉ)
  htpy-hom-system'.sliceᵉ (concat-htpy-hom-system'ᵉ pᵉ qᵉ Hᵉ Kᵉ) = {!!ᵉ}

  concat-htpy-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    {fᵉ gᵉ hᵉ : hom-systemᵉ Aᵉ Bᵉ} (Hᵉ : htpy-hom-systemᵉ fᵉ gᵉ)
    (Kᵉ : htpy-hom-systemᵉ gᵉ hᵉ) → htpy-hom-systemᵉ fᵉ hᵉ
  htpy-hom-system'.typeᵉ (concat-htpy-hom-systemᵉ Hᵉ Kᵉ) =
    section-system.typeᵉ Hᵉ ∙hᵉ section-system.typeᵉ Kᵉ
  htpy-hom-system'.elementᵉ
    ( concat-htpy-hom-systemᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} {fᵉ} Hᵉ Kᵉ) Xᵉ xᵉ =
    ( ( tr-concatᵉ
        ( section-system.typeᵉ Hᵉ Xᵉ)
        ( section-system.typeᵉ Kᵉ Xᵉ)
        ( section-system.elementᵉ (trᵉ (hom-systemᵉ Aᵉ) reflᵉ fᵉ) Xᵉ xᵉ)) ∙ᵉ
      ( apᵉ
        ( trᵉ (system.elementᵉ Bᵉ) (section-system.typeᵉ Kᵉ Xᵉ))
        ( section-system.elementᵉ Hᵉ Xᵉ xᵉ))) ∙ᵉ
    ( section-system.elementᵉ Kᵉ Xᵉ xᵉ)
  htpy-hom-system'.sliceᵉ (concat-htpy-hom-systemᵉ Hᵉ Kᵉ) Xᵉ = {!!ᵉ}
  -ᵉ}
```

---ᵉ

## Contexts in a dependent type theory

Weᵉ interpretᵉ contextsᵉ in aᵉ dependentᵉ typeᵉ theory.ᵉ

```agda
module c-systemᵉ where

  open dependentᵉ

  data contextᵉ
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) : UUᵉ l1ᵉ
    where
    empty-ctxᵉ : contextᵉ Aᵉ
    extension-ctxᵉ :
      (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ))
      (Γᵉ : contextᵉ (slice-dttᵉ Aᵉ Xᵉ)) → contextᵉ Aᵉ
```

### The action on contexts of a morphism of dependent type theories

```agda
  context-homᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ}
    {Bᵉ : type-theoryᵉ l3ᵉ l4ᵉ} (fᵉ : hom-dttᵉ Aᵉ Bᵉ) →
    contextᵉ Aᵉ → contextᵉ Bᵉ
  context-homᵉ fᵉ empty-ctxᵉ = empty-ctxᵉ
  context-homᵉ fᵉ (extension-ctxᵉ Xᵉ Γᵉ) =
    extension-ctxᵉ
      ( section-system.typeᵉ (hom-dtt.sysᵉ fᵉ) Xᵉ)
      ( context-homᵉ (hom-slice-dttᵉ fᵉ Xᵉ) Γᵉ)
```

### Elements of contexts

```agda
{-ᵉ
  data element-contextᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ} :
    (Γᵉ : contextᵉ Aᵉ) → UUᵉ {!substitution.typeᵉ (type-theory.Sᵉ Aᵉ) !ᵉ}
    where
    element-empty-contextᵉ : element-contextᵉ empty-ctxᵉ
    element-extension-ctxᵉ :
      {!(Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ))
        (Γᵉ : contextᵉ (slice-dttᵉ Aᵉ Xᵉ))
        (xᵉ : system.elementᵉ (type-theory.sysᵉ Aᵉ) Xᵉ)
        (yᵉ : element-contextᵉ
              (context-homᵉ (substitution.typeᵉ (type-theory.Sᵉ Aᵉ) xᵉ) Γᵉ)) →
        element-contextᵉ (extension-ctxᵉ Xᵉ Γ)!ᵉ}
-ᵉ}
```

### Interpreting types in context in a dependent type theory

```agda
  typeᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) →
    contextᵉ Aᵉ → UUᵉ l1ᵉ
  typeᵉ Aᵉ empty-ctxᵉ = system.typeᵉ (type-theory.sysᵉ Aᵉ)
  typeᵉ Aᵉ (extension-ctxᵉ Xᵉ Γᵉ) = typeᵉ (slice-dttᵉ Aᵉ Xᵉ) Γᵉ
```

### Interpreting elements of types in context in a dependent type theory

```agda
  elementᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) (Γᵉ : contextᵉ Aᵉ)
    (Yᵉ : typeᵉ Aᵉ Γᵉ) → UUᵉ l2ᵉ
  elementᵉ Aᵉ empty-ctxᵉ = system.elementᵉ (type-theory.sysᵉ Aᵉ)
  elementᵉ Aᵉ (extension-ctxᵉ Xᵉ Γᵉ) = elementᵉ (slice-dttᵉ Aᵉ Xᵉ) Γᵉ

  sliceᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) (Γᵉ : contextᵉ Aᵉ) →
    type-theoryᵉ l1ᵉ l2ᵉ
  sliceᵉ Aᵉ empty-ctxᵉ = Aᵉ
  sliceᵉ Aᵉ (extension-ctxᵉ Xᵉ Γᵉ) = sliceᵉ (slice-dttᵉ Aᵉ Xᵉ) Γᵉ

  dependent-contextᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) (Γᵉ : contextᵉ Aᵉ) →
    UUᵉ l1ᵉ
  dependent-contextᵉ Aᵉ Γᵉ = contextᵉ (sliceᵉ Aᵉ Γᵉ)

{-ᵉ
  weakening-by-type-contextᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ}
    (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ)) →
    contextᵉ Aᵉ → contextᵉ (slice-dttᵉ Aᵉ Xᵉ)
  weakening-by-type-contextᵉ {Aᵉ = Aᵉ} Xᵉ Δᵉ =
    context-homᵉ {!weakening.typeᵉ (type-theory.Wᵉ Aᵉ) X!ᵉ} Δᵉ
-ᵉ}

  weakening-type-contextᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) (Γᵉ : contextᵉ Aᵉ) →
    system.typeᵉ (type-theory.sysᵉ Aᵉ) →
    system.typeᵉ (type-theory.sysᵉ (sliceᵉ Aᵉ Γᵉ))
  weakening-type-contextᵉ Aᵉ empty-ctxᵉ Yᵉ = Yᵉ
  weakening-type-contextᵉ Aᵉ (extension-ctxᵉ Xᵉ Γᵉ) Yᵉ =
    weakening-type-contextᵉ (slice-dttᵉ Aᵉ Xᵉ) Γᵉ
      ( section-system.typeᵉ
        ( weakening.typeᵉ (type-theory.Wᵉ Aᵉ) Xᵉ) Yᵉ)

{-ᵉ
  weakening-contextᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) (Γᵉ : contextᵉ Aᵉ) →
    contextᵉ Aᵉ → contextᵉ (sliceᵉ Aᵉ Γᵉ)
  weakening-contextᵉ Aᵉ empty-ctxᵉ Δᵉ = Δᵉ
  weakening-contextᵉ Aᵉ (extension-ctxᵉ Xᵉ Γᵉ) empty-ctxᵉ = empty-ctxᵉ
  weakening-contextᵉ Aᵉ (extension-ctxᵉ Xᵉ Γᵉ) (extension-ctxᵉ Yᵉ Δᵉ) =
    extension-ctxᵉ
      ( weakening-type-contextᵉ Aᵉ (extension-ctxᵉ Xᵉ Γᵉ) Yᵉ)
      ( weakening-contextᵉ {!!ᵉ} {!!ᵉ} {!!ᵉ})
-ᵉ}
```