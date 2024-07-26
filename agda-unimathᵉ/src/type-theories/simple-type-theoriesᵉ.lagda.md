# Simple type theories

```agda
{-# OPTIONSᵉ --guardednessᵉ --allow-unsolved-metasᵉ #-}

module type-theories.simple-type-theoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Simpleᵉ typeᵉ theoriesᵉ areᵉ typeᵉ theoriesᵉ thatᵉ haveᵉ noᵉ typeᵉ dependency.ᵉ Theᵉ
categoryᵉ ofᵉ simpleᵉ typeᵉ theoriesᵉ isᵉ equivalentᵉ to theᵉ categoryᵉ ofᵉ multisortedᵉ
algebraicᵉ theories.ᵉ

## Definitions

```agda
module simpleᵉ where

  record systemᵉ
    {l1ᵉ : Level} (l2ᵉ : Level) (Tᵉ : UUᵉ l1ᵉ) : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ : Tᵉ → UUᵉ l2ᵉ
      sliceᵉ : (Xᵉ : Tᵉ) → systemᵉ l2ᵉ Tᵉ

  record fibered-systemᵉ
    {l1ᵉ l2ᵉ l3ᵉ : Level} (l4ᵉ : Level) {Tᵉ : UUᵉ l1ᵉ} (Sᵉ : Tᵉ → UUᵉ l2ᵉ)
    (Aᵉ : systemᵉ l3ᵉ Tᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ lsuc l4ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ : {Xᵉ : Tᵉ} → Sᵉ Xᵉ → system.elementᵉ Aᵉ Xᵉ → UUᵉ l4ᵉ
      sliceᵉ : {Xᵉ : Tᵉ} → Sᵉ Xᵉ → fibered-systemᵉ l4ᵉ Sᵉ (system.sliceᵉ Aᵉ Xᵉ)

  record section-systemᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} {Sᵉ : Tᵉ → UUᵉ l2ᵉ} {Aᵉ : systemᵉ l3ᵉ Tᵉ}
    (Bᵉ : fibered-systemᵉ l4ᵉ Sᵉ Aᵉ) (fᵉ : (Xᵉ : Tᵉ) → Sᵉ Xᵉ) : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ :
        {Xᵉ : Tᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
        fibered-system.elementᵉ Bᵉ (fᵉ Xᵉ) xᵉ
      sliceᵉ : (Xᵉ : Tᵉ) → section-systemᵉ (fibered-system.sliceᵉ Bᵉ (fᵉ Xᵉ)) fᵉ

  ------------------------------------------------------------------------------ᵉ
```

Weᵉ willᵉ introduceᵉ homotopiesᵉ ofᵉ sectionsᵉ ofᵉ fiberedᵉ systems.ᵉ However,ᵉ in orderᵉ
to defineᵉ concatenationᵉ ofᵉ thoseᵉ homotopies,ᵉ weᵉ willᵉ firstᵉ defineᵉ heterogeneousᵉ
homotopiesᵉ ofᵉ sectionsᵉ ofᵉ fiberedᵉ systems.ᵉ

```agda
  Eq-fibered-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : systemᵉ l2ᵉ Tᵉ} {Sᵉ : Tᵉ → UUᵉ l3ᵉ}
    {Bᵉ B'ᵉ : fibered-systemᵉ l4ᵉ Sᵉ Aᵉ} (αᵉ : Idᵉ Bᵉ B'ᵉ) {fᵉ f'ᵉ : (Xᵉ : Tᵉ) → Sᵉ Xᵉ}
    (gᵉ : section-systemᵉ Bᵉ fᵉ) (g'ᵉ : section-systemᵉ B'ᵉ f'ᵉ) →
    fibered-systemᵉ l4ᵉ (λ tᵉ → Idᵉ (fᵉ tᵉ) (f'ᵉ tᵉ)) Aᵉ
  fibered-system.elementᵉ (Eq-fibered-system'ᵉ {Bᵉ = Bᵉ} reflᵉ {fᵉ} gᵉ g'ᵉ) {Xᵉ} pᵉ xᵉ =
    Idᵉ
      ( trᵉ
        ( λ uᵉ → fibered-system.elementᵉ Bᵉ uᵉ xᵉ)
        ( pᵉ)
        ( section-system.elementᵉ gᵉ xᵉ))
      ( section-system.elementᵉ g'ᵉ xᵉ)
  fibered-system.sliceᵉ (Eq-fibered-system'ᵉ {Bᵉ = Bᵉ} reflᵉ gᵉ g'ᵉ) {Xᵉ} pᵉ =
    Eq-fibered-system'ᵉ
      ( apᵉ (fibered-system.sliceᵉ Bᵉ) pᵉ)
      ( section-system.sliceᵉ gᵉ Xᵉ)
      ( section-system.sliceᵉ g'ᵉ Xᵉ)

  htpy-section-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : systemᵉ l2ᵉ Tᵉ} {Sᵉ : Tᵉ → UUᵉ l3ᵉ}
    {Bᵉ B'ᵉ : fibered-systemᵉ l4ᵉ Sᵉ Aᵉ} (αᵉ : Idᵉ Bᵉ B'ᵉ) {fᵉ f'ᵉ : (Xᵉ : Tᵉ) → Sᵉ Xᵉ}
    (Hᵉ : fᵉ ~ᵉ f'ᵉ) (gᵉ : section-systemᵉ Bᵉ fᵉ) (g'ᵉ : section-systemᵉ B'ᵉ f'ᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  htpy-section-system'ᵉ αᵉ Hᵉ gᵉ g'ᵉ =
    section-systemᵉ (Eq-fibered-system'ᵉ αᵉ gᵉ g'ᵉ) Hᵉ

  concat-htpy-section-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : systemᵉ l2ᵉ Tᵉ} {Sᵉ : Tᵉ → UUᵉ l3ᵉ}
    {Bᵉ B'ᵉ B''ᵉ : fibered-systemᵉ l4ᵉ Sᵉ Aᵉ} {αᵉ : Idᵉ Bᵉ B'ᵉ} {βᵉ : Idᵉ B'ᵉ B''ᵉ}
    (γᵉ : Idᵉ Bᵉ B''ᵉ) (δᵉ : Idᵉ (αᵉ ∙ᵉ βᵉ) γᵉ) {fᵉ f'ᵉ f''ᵉ : (Xᵉ : Tᵉ) → Sᵉ Xᵉ}
    {Hᵉ : fᵉ ~ᵉ f'ᵉ} {H'ᵉ : f'ᵉ ~ᵉ f''ᵉ} {gᵉ : section-systemᵉ Bᵉ fᵉ}
    {g'ᵉ : section-systemᵉ B'ᵉ f'ᵉ} {g''ᵉ : section-systemᵉ B''ᵉ f''ᵉ}
    (Kᵉ : htpy-section-system'ᵉ αᵉ Hᵉ gᵉ g'ᵉ)
    (K'ᵉ : htpy-section-system'ᵉ βᵉ H'ᵉ g'ᵉ g''ᵉ) →
    htpy-section-system'ᵉ γᵉ (Hᵉ ∙hᵉ H'ᵉ) gᵉ g''ᵉ
  section-system.elementᵉ
    ( concat-htpy-section-system'ᵉ
      {Bᵉ = Bᵉ} {αᵉ = reflᵉ} {reflᵉ} .reflᵉ reflᵉ {Hᵉ = Hᵉ} {H'ᵉ} {gᵉ} Kᵉ K'ᵉ) {Xᵉ} xᵉ =
    ( tr-concatᵉ
      { Bᵉ = λ tᵉ → fibered-system.elementᵉ Bᵉ tᵉ xᵉ}
      ( Hᵉ Xᵉ)
      ( H'ᵉ Xᵉ)
      ( section-system.elementᵉ gᵉ xᵉ)) ∙ᵉ
    ( ( apᵉ
        ( trᵉ
          ( λ tᵉ → fibered-system.elementᵉ Bᵉ tᵉ xᵉ)
          ( H'ᵉ Xᵉ))
        ( section-system.elementᵉ Kᵉ xᵉ)) ∙ᵉ
      ( section-system.elementᵉ K'ᵉ xᵉ))
  section-system.sliceᵉ
    ( concat-htpy-section-system'ᵉ
      {Bᵉ = Bᵉ} {αᵉ = reflᵉ} {reflᵉ} .reflᵉ reflᵉ {Hᵉ = Hᵉ} {H'ᵉ} Kᵉ K'ᵉ) Xᵉ =
    concat-htpy-section-system'ᵉ
      ( apᵉ (fibered-system.sliceᵉ Bᵉ) (Hᵉ Xᵉ ∙ᵉ H'ᵉ Xᵉ))
      ( invᵉ (ap-concatᵉ (fibered-system.sliceᵉ Bᵉ) (Hᵉ Xᵉ) (H'ᵉ Xᵉ)))
      ( section-system.sliceᵉ Kᵉ Xᵉ)
      ( section-system.sliceᵉ K'ᵉ Xᵉ)

  inv-htpy-section-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : systemᵉ l2ᵉ Tᵉ} {Sᵉ : Tᵉ → UUᵉ l3ᵉ}
    {Bᵉ B'ᵉ : fibered-systemᵉ l4ᵉ Sᵉ Aᵉ}
    {αᵉ : Idᵉ Bᵉ B'ᵉ} (βᵉ : Idᵉ B'ᵉ Bᵉ) (γᵉ : Idᵉ (invᵉ αᵉ) βᵉ)
    {fᵉ f'ᵉ : (Xᵉ : Tᵉ) → Sᵉ Xᵉ} {gᵉ : section-systemᵉ Bᵉ fᵉ}
    {g'ᵉ : section-systemᵉ B'ᵉ f'ᵉ} {Hᵉ : fᵉ ~ᵉ f'ᵉ} →
    htpy-section-system'ᵉ αᵉ Hᵉ gᵉ g'ᵉ → htpy-section-system'ᵉ βᵉ (inv-htpyᵉ Hᵉ) g'ᵉ gᵉ
  section-system.elementᵉ
    ( inv-htpy-section-system'ᵉ {αᵉ = reflᵉ} .reflᵉ reflᵉ {Hᵉ = Hᵉ} Kᵉ) {Xᵉ} xᵉ =
    eq-transpose-trᵉ
      ( Hᵉ Xᵉ)
      ( invᵉ (section-system.elementᵉ Kᵉ xᵉ))
  section-system.sliceᵉ
    ( inv-htpy-section-system'ᵉ {Bᵉ = Bᵉ} {αᵉ = reflᵉ} .reflᵉ reflᵉ {Hᵉ = Hᵉ} Kᵉ) Xᵉ =
    inv-htpy-section-system'ᵉ
      ( apᵉ (fibered-system.sliceᵉ Bᵉ) (invᵉ (Hᵉ Xᵉ)))
      ( invᵉ (ap-invᵉ (fibered-system.sliceᵉ Bᵉ) (Hᵉ Xᵉ)))
      ( section-system.sliceᵉ Kᵉ Xᵉ)
```

### Nonhomogenous homotopies

Weᵉ specializeᵉ theᵉ aboveᵉ definitionsᵉ to nonhomogenousᵉ homotopies.ᵉ

```agda
  htpy-section-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : systemᵉ l2ᵉ Tᵉ} {Sᵉ : Tᵉ → UUᵉ l3ᵉ}
    {Bᵉ : fibered-systemᵉ l4ᵉ Sᵉ Aᵉ} {fᵉ f'ᵉ : (Xᵉ : Tᵉ) → Sᵉ Xᵉ} →
    (fᵉ ~ᵉ f'ᵉ) → section-systemᵉ Bᵉ fᵉ → section-systemᵉ Bᵉ f'ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  htpy-section-systemᵉ Hᵉ gᵉ g'ᵉ = htpy-section-system'ᵉ reflᵉ Hᵉ gᵉ g'ᵉ

  refl-htpy-section-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : systemᵉ l2ᵉ Tᵉ} {Sᵉ : Tᵉ → UUᵉ l3ᵉ}
    {Bᵉ : fibered-systemᵉ l4ᵉ Sᵉ Aᵉ} {fᵉ : (Xᵉ : Tᵉ) → Sᵉ Xᵉ}
    (gᵉ : section-systemᵉ Bᵉ fᵉ) → htpy-section-systemᵉ refl-htpyᵉ gᵉ gᵉ
  section-system.elementᵉ (refl-htpy-section-systemᵉ gᵉ) = refl-htpyᵉ
  section-system.sliceᵉ (refl-htpy-section-systemᵉ gᵉ) Xᵉ =
    refl-htpy-section-systemᵉ (section-system.sliceᵉ gᵉ Xᵉ)

  concat-htpy-section-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : systemᵉ l2ᵉ Tᵉ} {Sᵉ : Tᵉ → UUᵉ l3ᵉ}
    {Bᵉ : fibered-systemᵉ l4ᵉ Sᵉ Aᵉ} {fᵉ f'ᵉ f''ᵉ : (Xᵉ : Tᵉ) → Sᵉ Xᵉ}
    {gᵉ : section-systemᵉ Bᵉ fᵉ} {g'ᵉ : section-systemᵉ Bᵉ f'ᵉ}
    {g''ᵉ : section-systemᵉ Bᵉ f''ᵉ} {Hᵉ : fᵉ ~ᵉ f'ᵉ} {H'ᵉ : f'ᵉ ~ᵉ f''ᵉ} →
    htpy-section-systemᵉ Hᵉ gᵉ g'ᵉ → htpy-section-systemᵉ H'ᵉ g'ᵉ g''ᵉ →
    htpy-section-systemᵉ (Hᵉ ∙hᵉ H'ᵉ) gᵉ g''ᵉ
  concat-htpy-section-systemᵉ Kᵉ K'ᵉ =
    concat-htpy-section-system'ᵉ reflᵉ reflᵉ Kᵉ K'ᵉ

  inv-htpy-section-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : systemᵉ l2ᵉ Tᵉ} {Sᵉ : Tᵉ → UUᵉ l3ᵉ}
    {Bᵉ : fibered-systemᵉ l4ᵉ Sᵉ Aᵉ} {fᵉ f'ᵉ : (Xᵉ : Tᵉ) → Sᵉ Xᵉ}
    {gᵉ : section-systemᵉ Bᵉ fᵉ} {g'ᵉ : section-systemᵉ Bᵉ f'ᵉ} {Hᵉ : fᵉ ~ᵉ f'ᵉ} →
    htpy-section-systemᵉ Hᵉ gᵉ g'ᵉ → htpy-section-systemᵉ (inv-htpyᵉ Hᵉ) g'ᵉ gᵉ
  inv-htpy-section-systemᵉ Kᵉ =
    inv-htpy-section-system'ᵉ reflᵉ reflᵉ Kᵉ
```

---ᵉ

```agda
  constant-fibered-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} (Aᵉ : systemᵉ l2ᵉ Tᵉ) {Sᵉ : UUᵉ l3ᵉ}
    (Bᵉ : systemᵉ l4ᵉ Sᵉ) → fibered-systemᵉ l4ᵉ (λ Xᵉ → Sᵉ) Aᵉ
  fibered-system.elementᵉ (constant-fibered-systemᵉ Aᵉ Bᵉ) Yᵉ xᵉ = system.elementᵉ Bᵉ Yᵉ
  fibered-system.sliceᵉ (constant-fibered-systemᵉ Aᵉ Bᵉ) {Xᵉ} Yᵉ =
    constant-fibered-systemᵉ
      ( system.sliceᵉ Aᵉ Xᵉ)
      ( system.sliceᵉ Bᵉ Yᵉ)

  hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} {Sᵉ : UUᵉ l2ᵉ} (fᵉ : Tᵉ → Sᵉ)
    (Aᵉ : systemᵉ l3ᵉ Tᵉ) (Bᵉ : systemᵉ l4ᵉ Sᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-systemᵉ fᵉ Aᵉ Bᵉ = section-systemᵉ (constant-fibered-systemᵉ Aᵉ Bᵉ) fᵉ

  htpy-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} {Sᵉ : UUᵉ l2ᵉ} {fᵉ : Tᵉ → Sᵉ}
    {Aᵉ : systemᵉ l3ᵉ Tᵉ} {Bᵉ : systemᵉ l4ᵉ Sᵉ} (gᵉ hᵉ : hom-systemᵉ fᵉ Aᵉ Bᵉ) →
    UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-hom-systemᵉ gᵉ hᵉ = htpy-section-systemᵉ {!!ᵉ} {!!ᵉ} {!!ᵉ}

  id-hom-systemᵉ :
    {l1ᵉ l2ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} (Aᵉ : systemᵉ l2ᵉ Tᵉ) → hom-systemᵉ idᵉ Aᵉ Aᵉ
  section-system.elementᵉ (id-hom-systemᵉ Aᵉ) {Xᵉ} = idᵉ
  section-system.sliceᵉ (id-hom-systemᵉ Aᵉ) Xᵉ = id-hom-systemᵉ (system.sliceᵉ Aᵉ Xᵉ)

  comp-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} {Sᵉ : UUᵉ l2ᵉ} {Rᵉ : UUᵉ l3ᵉ} {gᵉ : Sᵉ → Rᵉ}
    {fᵉ : Tᵉ → Sᵉ} {Aᵉ : systemᵉ l4ᵉ Tᵉ} {Bᵉ : systemᵉ l5ᵉ Sᵉ} {Cᵉ : systemᵉ l6ᵉ Rᵉ}
    (βᵉ : hom-systemᵉ gᵉ Bᵉ Cᵉ) (αᵉ : hom-systemᵉ fᵉ Aᵉ Bᵉ) → hom-systemᵉ (gᵉ ∘ᵉ fᵉ) Aᵉ Cᵉ
  section-system.elementᵉ (comp-hom-systemᵉ {fᵉ = fᵉ} βᵉ αᵉ) {Xᵉ} =
    section-system.elementᵉ βᵉ {fᵉ Xᵉ} ∘ᵉ section-system.elementᵉ αᵉ {Xᵉ}
  section-system.sliceᵉ (comp-hom-systemᵉ {fᵉ = fᵉ} βᵉ αᵉ) Xᵉ =
    comp-hom-systemᵉ (section-system.sliceᵉ βᵉ (fᵉ Xᵉ)) (section-system.sliceᵉ αᵉ Xᵉ)

  record weakeningᵉ
    {l1ᵉ l2ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} (Aᵉ : systemᵉ l2ᵉ Tᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ : (Xᵉ : Tᵉ) → hom-systemᵉ idᵉ Aᵉ (system.sliceᵉ Aᵉ Xᵉ)
      sliceᵉ : (Xᵉ : Tᵉ) → weakeningᵉ (system.sliceᵉ Aᵉ Xᵉ)

  record preserves-weakeningᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} {Sᵉ : UUᵉ l2ᵉ} {fᵉ : Tᵉ → Sᵉ}
    {Aᵉ : systemᵉ l3ᵉ Tᵉ} {Bᵉ : systemᵉ l4ᵉ Sᵉ} (WAᵉ : weakeningᵉ Aᵉ) (WBᵉ : weakeningᵉ Bᵉ)
    (hᵉ : hom-systemᵉ fᵉ Aᵉ Bᵉ) : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ :
        (Xᵉ : Tᵉ) →
        htpy-hom-systemᵉ
          ( comp-hom-systemᵉ
            ( section-system.sliceᵉ hᵉ Xᵉ)
            ( weakening.elementᵉ WAᵉ Xᵉ))
          ( comp-hom-systemᵉ
            ( weakening.elementᵉ WBᵉ (fᵉ Xᵉ))
            ( hᵉ))
      sliceᵉ :
        (Xᵉ : Tᵉ) →
        preserves-weakeningᵉ
          ( weakening.sliceᵉ WAᵉ Xᵉ)
          ( weakening.sliceᵉ WBᵉ (fᵉ Xᵉ))
          ( section-system.sliceᵉ hᵉ Xᵉ)

  record substitutionᵉ
    {l1ᵉ l2ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} (Aᵉ : systemᵉ l2ᵉ Tᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ :
        {Xᵉ : Tᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
        hom-systemᵉ idᵉ (system.sliceᵉ Aᵉ Xᵉ) Aᵉ
      sliceᵉ :
        (Xᵉ : Tᵉ) → substitutionᵉ (system.sliceᵉ Aᵉ Xᵉ)

  record preserves-substitutionᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Sᵉ : UUᵉ l2ᵉ} {fᵉ : Tᵉ → Sᵉ} {Aᵉ : systemᵉ l3ᵉ Tᵉ}
    {Bᵉ : systemᵉ l4ᵉ Sᵉ} (SAᵉ : substitutionᵉ Aᵉ) (SBᵉ : substitutionᵉ Bᵉ)
    (hᵉ : hom-systemᵉ fᵉ Aᵉ Bᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ :
        {Xᵉ : Tᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
        htpy-hom-systemᵉ
          ( comp-hom-systemᵉ
            ( hᵉ)
            ( substitution.elementᵉ SAᵉ xᵉ))
          ( comp-hom-systemᵉ
            ( substitution.elementᵉ SBᵉ
              ( section-system.elementᵉ hᵉ xᵉ))
            ( section-system.sliceᵉ hᵉ Xᵉ))
      sliceᵉ :
        (Xᵉ : Tᵉ) →
        preserves-substitutionᵉ
          ( substitution.sliceᵉ SAᵉ Xᵉ)
          ( substitution.sliceᵉ SBᵉ (fᵉ Xᵉ))
          ( section-system.sliceᵉ hᵉ Xᵉ)

  record generic-elementᵉ
    {l1ᵉ l2ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} (Aᵉ : systemᵉ l2ᵉ Tᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ : (Xᵉ : Tᵉ) → system.elementᵉ (system.sliceᵉ Aᵉ Xᵉ) Xᵉ
      sliceᵉ : (Xᵉ : Tᵉ) → generic-elementᵉ (system.sliceᵉ Aᵉ Xᵉ)

  record preserves-generic-elementᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Sᵉ : UUᵉ l2ᵉ} {fᵉ : Tᵉ → Sᵉ}
    {Aᵉ : systemᵉ l3ᵉ Tᵉ} {Bᵉ : systemᵉ l4ᵉ Sᵉ}
    (δAᵉ : generic-elementᵉ Aᵉ) (δBᵉ : generic-elementᵉ Bᵉ)
    (hᵉ : hom-systemᵉ fᵉ Aᵉ Bᵉ) : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ :
        (Xᵉ : Tᵉ) →
        Idᵉ
          ( section-system.elementᵉ
            ( section-system.sliceᵉ hᵉ Xᵉ)
            ( generic-element.elementᵉ δAᵉ Xᵉ))
          ( generic-element.elementᵉ δBᵉ (fᵉ Xᵉ))
      sliceᵉ :
        (Xᵉ : Tᵉ) →
        preserves-generic-elementᵉ
          ( generic-element.sliceᵉ δAᵉ Xᵉ)
          ( generic-element.sliceᵉ δBᵉ (fᵉ Xᵉ))
          ( section-system.sliceᵉ hᵉ Xᵉ)

  module _
    {l1ᵉ l2ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ}
    where

    record weakening-preserves-weakeningᵉ
      {Aᵉ : systemᵉ l2ᵉ Tᵉ} (Wᵉ : weakeningᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
      where
      coinductiveᵉ
      field
        elementᵉ :
          (Xᵉ : Tᵉ) →
          preserves-weakeningᵉ
            ( Wᵉ)
            ( weakening.sliceᵉ Wᵉ Xᵉ)
            ( weakening.elementᵉ Wᵉ Xᵉ)
        sliceᵉ :
          (Xᵉ : Tᵉ) → weakening-preserves-weakeningᵉ (weakening.sliceᵉ Wᵉ Xᵉ)

    record substitution-preserves-substitutionᵉ
      {Aᵉ : systemᵉ l2ᵉ Tᵉ} (Sᵉ : substitutionᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
      where
      coinductiveᵉ
      field
        elementᵉ :
          {Xᵉ : Tᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
          preserves-substitutionᵉ
            ( substitution.sliceᵉ Sᵉ Xᵉ)
            ( Sᵉ)
            ( substitution.elementᵉ Sᵉ xᵉ)
        sliceᵉ :
          (Xᵉ : Tᵉ) →
          substitution-preserves-substitutionᵉ (substitution.sliceᵉ Sᵉ Xᵉ)

    record weakening-preserves-substitutionᵉ
      {Aᵉ : systemᵉ l2ᵉ Tᵉ} (Wᵉ : weakeningᵉ Aᵉ) (Sᵉ : substitutionᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
      where
      coinductiveᵉ
      field
        elementᵉ :
          (Xᵉ : Tᵉ) →
          preserves-substitutionᵉ
            ( Sᵉ)
            ( substitution.sliceᵉ Sᵉ Xᵉ)
            ( weakening.elementᵉ Wᵉ Xᵉ)
        sliceᵉ :
          (Xᵉ : Tᵉ) →
          weakening-preserves-substitutionᵉ
            ( weakening.sliceᵉ Wᵉ Xᵉ)
            ( substitution.sliceᵉ Sᵉ Xᵉ)

    record substitution-preserves-weakeningᵉ
      {Aᵉ : systemᵉ l2ᵉ Tᵉ} (Wᵉ : weakeningᵉ Aᵉ) (Sᵉ : substitutionᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
      where
      coinductiveᵉ
      field
        elementᵉ :
          {Xᵉ : Tᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
          preserves-weakeningᵉ
            ( weakening.sliceᵉ Wᵉ Xᵉ)
            ( Wᵉ)
            ( substitution.elementᵉ Sᵉ xᵉ)
        sliceᵉ :
          (Xᵉ : Tᵉ) →
          substitution-preserves-weakeningᵉ
            ( weakening.sliceᵉ Wᵉ Xᵉ)
            ( substitution.sliceᵉ Sᵉ Xᵉ)

    record weakening-preserves-generic-elementᵉ
      {Aᵉ : systemᵉ l2ᵉ Tᵉ} (Wᵉ : weakeningᵉ Aᵉ) (δᵉ : generic-elementᵉ Aᵉ) :
      UUᵉ (l1ᵉ ⊔ l2ᵉ)
      where
      coinductiveᵉ
      field
        elementᵉ :
          (Xᵉ : Tᵉ) →
          preserves-generic-elementᵉ
            ( δᵉ)
            ( generic-element.sliceᵉ δᵉ Xᵉ)
            ( weakening.elementᵉ Wᵉ Xᵉ)
        sliceᵉ :
          (Xᵉ : Tᵉ) →
          weakening-preserves-generic-elementᵉ
            ( weakening.sliceᵉ Wᵉ Xᵉ)
            ( generic-element.sliceᵉ δᵉ Xᵉ)

    record substitution-preserves-generic-elementᵉ
      {Aᵉ : systemᵉ l2ᵉ Tᵉ} (Sᵉ : substitutionᵉ Aᵉ) (δᵉ : generic-elementᵉ Aᵉ) :
      UUᵉ (l1ᵉ ⊔ l2ᵉ)
      where
      coinductiveᵉ
      field
        elementᵉ :
          {Xᵉ : Tᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
          preserves-generic-elementᵉ
            ( generic-element.sliceᵉ δᵉ Xᵉ)
            ( δᵉ)
            ( substitution.elementᵉ Sᵉ xᵉ)
        sliceᵉ :
          (Xᵉ : Tᵉ) →
          substitution-preserves-generic-elementᵉ
            ( substitution.sliceᵉ Sᵉ Xᵉ)
            ( generic-element.sliceᵉ δᵉ Xᵉ)

    record substitution-cancels-weakeningᵉ
      {Aᵉ : systemᵉ l2ᵉ Tᵉ} (Wᵉ : weakeningᵉ Aᵉ) (Sᵉ : substitutionᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
      where
      coinductiveᵉ
      field
        elementᵉ :
          {Xᵉ : Tᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
          htpy-hom-systemᵉ
            ( comp-hom-systemᵉ
              ( substitution.elementᵉ Sᵉ xᵉ)
              ( weakening.elementᵉ Wᵉ Xᵉ))
            ( id-hom-systemᵉ Aᵉ)
        sliceᵉ :
          (Xᵉ : Tᵉ) →
          substitution-cancels-weakeningᵉ
            ( weakening.sliceᵉ Wᵉ Xᵉ)
            ( substitution.sliceᵉ Sᵉ Xᵉ)

    record generic-element-is-identityᵉ
      {Aᵉ : systemᵉ l2ᵉ Tᵉ} (Sᵉ : substitutionᵉ Aᵉ) (δᵉ : generic-elementᵉ Aᵉ) :
      UUᵉ (l1ᵉ ⊔ l2ᵉ)
      where
      coinductiveᵉ
      field
        elementᵉ :
          {Xᵉ : Tᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
          Idᵉ ( section-system.elementᵉ
                ( substitution.elementᵉ Sᵉ xᵉ)
                ( generic-element.elementᵉ δᵉ Xᵉ))
              ( xᵉ)
        sliceᵉ :
          (Xᵉ : Tᵉ) →
          generic-element-is-identityᵉ
            ( substitution.sliceᵉ Sᵉ Xᵉ)
            ( generic-element.sliceᵉ δᵉ Xᵉ)

    record substitution-by-generic-elementᵉ
      {Aᵉ : systemᵉ l2ᵉ Tᵉ} (Wᵉ : weakeningᵉ Aᵉ) (Sᵉ : substitutionᵉ Aᵉ)
      (δᵉ : generic-elementᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
      where
      coinductiveᵉ
      field
        elementᵉ :
          (Xᵉ : Tᵉ) →
          htpy-hom-systemᵉ
            ( comp-hom-systemᵉ
              ( substitution.elementᵉ
                ( substitution.sliceᵉ Sᵉ Xᵉ)
                ( generic-element.elementᵉ δᵉ Xᵉ))
              ( weakening.elementᵉ (weakening.sliceᵉ Wᵉ Xᵉ) Xᵉ))
            ( id-hom-systemᵉ (system.sliceᵉ Aᵉ Xᵉ))
        sliceᵉ :
          (Xᵉ : Tᵉ) →
          substitution-by-generic-elementᵉ
            ( weakening.sliceᵉ Wᵉ Xᵉ)
            ( substitution.sliceᵉ Sᵉ Xᵉ)
            ( generic-element.sliceᵉ δᵉ Xᵉ)

  record type-theoryᵉ
    (l1ᵉ l2ᵉ : Level) : UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
    where
    field
      typᵉ : UUᵉ l1ᵉ
      sysᵉ : systemᵉ l2ᵉ typᵉ
      Wᵉ : weakeningᵉ sysᵉ
      Sᵉ : substitutionᵉ sysᵉ
      δᵉ : generic-elementᵉ sysᵉ
      WWᵉ : weakening-preserves-weakeningᵉ Wᵉ
      SSᵉ : substitution-preserves-substitutionᵉ Sᵉ
      WSᵉ : weakening-preserves-substitutionᵉ Wᵉ Sᵉ
      SWᵉ : substitution-preserves-weakeningᵉ Wᵉ Sᵉ
      Wδᵉ : weakening-preserves-generic-elementᵉ Wᵉ δᵉ
      Sδᵉ : substitution-preserves-generic-elementᵉ Sᵉ δᵉ
      S!Wᵉ : substitution-cancels-weakeningᵉ Wᵉ Sᵉ
      δidᵉ : generic-element-is-identityᵉ Sᵉ δᵉ
      Sδ!ᵉ : substitution-by-generic-elementᵉ Wᵉ Sᵉ δᵉ

  slice-type-theoryᵉ :
    {l1ᵉ l2ᵉ : Level} (Tᵉ : type-theoryᵉ l1ᵉ l2ᵉ)
    (Xᵉ : type-theory.typᵉ Tᵉ) →
    type-theoryᵉ l1ᵉ l2ᵉ
  type-theory.typᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    type-theory.typᵉ Tᵉ
  type-theory.sysᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    system.sliceᵉ (type-theory.sysᵉ Tᵉ) Xᵉ
  type-theory.Wᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    weakening.sliceᵉ (type-theory.Wᵉ Tᵉ) Xᵉ
  type-theory.Sᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    substitution.sliceᵉ (type-theory.Sᵉ Tᵉ) Xᵉ
  type-theory.δᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    generic-element.sliceᵉ (type-theory.δᵉ Tᵉ) Xᵉ
  type-theory.WWᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    weakening-preserves-weakening.sliceᵉ (type-theory.WWᵉ Tᵉ) Xᵉ
  type-theory.SSᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    substitution-preserves-substitution.sliceᵉ (type-theory.SSᵉ Tᵉ) Xᵉ
  type-theory.WSᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    weakening-preserves-substitution.sliceᵉ (type-theory.WSᵉ Tᵉ) Xᵉ
  type-theory.SWᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    substitution-preserves-weakening.sliceᵉ (type-theory.SWᵉ Tᵉ) Xᵉ
  type-theory.Wδᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    weakening-preserves-generic-element.sliceᵉ (type-theory.Wδᵉ Tᵉ) Xᵉ
  type-theory.Sδᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    substitution-preserves-generic-element.sliceᵉ (type-theory.Sδᵉ Tᵉ) Xᵉ
  type-theory.S!Wᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    substitution-cancels-weakening.sliceᵉ (type-theory.S!Wᵉ Tᵉ) Xᵉ
  type-theory.δidᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    generic-element-is-identity.sliceᵉ (type-theory.δidᵉ Tᵉ) Xᵉ
  type-theory.Sδ!ᵉ (slice-type-theoryᵉ Tᵉ Xᵉ) =
    substitution-by-generic-element.sliceᵉ (type-theory.Sδ!ᵉ Tᵉ) Xᵉ

module dependent-simpleᵉ
  where

  open import type-theories.dependent-type-theoriesᵉ
  open import type-theories.fibered-dependent-type-theoriesᵉ

  systemᵉ :
    {l1ᵉ l2ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} → simple.systemᵉ l2ᵉ Tᵉ → dependent.systemᵉ l1ᵉ l2ᵉ
  dependent.system.typeᵉ (systemᵉ {Tᵉ = Tᵉ} Aᵉ) = Tᵉ
  dependent.system.elementᵉ (systemᵉ Aᵉ) Xᵉ =
    simple.system.elementᵉ Aᵉ Xᵉ
  dependent.system.sliceᵉ (systemᵉ Aᵉ) Xᵉ =
    systemᵉ (simple.system.sliceᵉ Aᵉ Xᵉ)

  fibered-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : simple.systemᵉ l2ᵉ Tᵉ} {Sᵉ : Tᵉ → UUᵉ l3ᵉ} →
    simple.fibered-systemᵉ l4ᵉ Sᵉ Aᵉ →
    dependent.fibered-systemᵉ l3ᵉ l4ᵉ (systemᵉ Aᵉ)
  dependent.fibered-system.typeᵉ (fibered-systemᵉ {Sᵉ = Sᵉ} Bᵉ) = Sᵉ
  dependent.fibered-system.elementᵉ (fibered-systemᵉ Bᵉ) Yᵉ =
    simple.fibered-system.elementᵉ Bᵉ Yᵉ
  dependent.fibered-system.sliceᵉ (fibered-systemᵉ Bᵉ) Yᵉ =
    fibered-systemᵉ (simple.fibered-system.sliceᵉ Bᵉ Yᵉ)

  section-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : simple.systemᵉ l2ᵉ Tᵉ} {Sᵉ : Tᵉ → UUᵉ l3ᵉ}
    {Bᵉ : simple.fibered-systemᵉ l4ᵉ Sᵉ Aᵉ} {fᵉ : (Xᵉ : Tᵉ) → Sᵉ Xᵉ} →
    simple.section-systemᵉ Bᵉ fᵉ → dependent.section-systemᵉ (fibered-systemᵉ Bᵉ)
  dependent.section-system.typeᵉ (section-systemᵉ {Bᵉ = Bᵉ} {fᵉ} gᵉ) Xᵉ = fᵉ Xᵉ
  dependent.section-system.elementᵉ (section-systemᵉ {Bᵉ = Bᵉ} {fᵉ} gᵉ) xᵉ =
    simple.section-system.elementᵉ gᵉ xᵉ
  dependent.section-system.sliceᵉ (section-systemᵉ {Bᵉ = Bᵉ} {fᵉ} gᵉ) Xᵉ =
    section-systemᵉ (simple.section-system.sliceᵉ gᵉ Xᵉ)

  Eq-fibered-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : simple.systemᵉ l2ᵉ Tᵉ} {Sᵉ : Tᵉ → UUᵉ l3ᵉ}
    {Bᵉ B'ᵉ : simple.fibered-systemᵉ l4ᵉ Sᵉ Aᵉ} (αᵉ : Idᵉ Bᵉ B'ᵉ)
    {fᵉ f'ᵉ : (Xᵉ : Tᵉ) → Sᵉ Xᵉ}
    (gᵉ : simple.section-systemᵉ Bᵉ fᵉ) (g'ᵉ : simple.section-systemᵉ B'ᵉ f'ᵉ) →
    fibered.hom-fibered-systemᵉ
      ( dependent.id-hom-systemᵉ (systemᵉ Aᵉ))
      ( fibered-systemᵉ (simple.Eq-fibered-system'ᵉ αᵉ gᵉ g'ᵉ))
      ( dependent.Eq-fibered-system'ᵉ
        ( apᵉ fibered-systemᵉ αᵉ)
        ( section-systemᵉ gᵉ)
        ( section-systemᵉ g'ᵉ))
  fibered.section-fibered-system.typeᵉ (Eq-fibered-system'ᵉ reflᵉ fᵉ gᵉ) Yᵉ = Yᵉ
  fibered.section-fibered-system.elementᵉ (Eq-fibered-system'ᵉ reflᵉ fᵉ gᵉ) yᵉ = yᵉ
  fibered.section-fibered-system.sliceᵉ (Eq-fibered-system'ᵉ reflᵉ fᵉ gᵉ) Yᵉ =
    {!Eq-fibered-system'ᵉ ?ᵉ ?ᵉ ?ᵉ !ᵉ}

  htpy-section-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : simple.systemᵉ l2ᵉ Tᵉ} {Sᵉ : Tᵉ → UUᵉ l3ᵉ}
    {Bᵉ B'ᵉ : simple.fibered-systemᵉ l4ᵉ Sᵉ Aᵉ} (αᵉ : Idᵉ Bᵉ B'ᵉ) {fᵉ f'ᵉ : (Xᵉ : Tᵉ) → Sᵉ Xᵉ}
    {Hᵉ : fᵉ ~ᵉ f'ᵉ} {gᵉ : simple.section-systemᵉ Bᵉ fᵉ}
    {g'ᵉ : simple.section-systemᵉ B'ᵉ f'ᵉ} → simple.htpy-section-system'ᵉ αᵉ Hᵉ gᵉ g'ᵉ →
    dependent.htpy-section-system'ᵉ
      ( apᵉ fibered-systemᵉ αᵉ)
      ( section-systemᵉ gᵉ)
      ( section-systemᵉ g'ᵉ)
  dependent.section-system.typeᵉ (htpy-section-system'ᵉ reflᵉ {Hᵉ = Hᵉ} Kᵉ) = Hᵉ
  dependent.section-system.elementᵉ (htpy-section-system'ᵉ reflᵉ {Hᵉ = Hᵉ} Kᵉ) =
    simple.section-system.elementᵉ Kᵉ
  dependent.section-system.sliceᵉ (htpy-section-system'ᵉ reflᵉ {Hᵉ = Hᵉ} Kᵉ) Xᵉ =
    {!htpy-section-system'ᵉ ?ᵉ ?ᵉ !ᵉ}

  htpy-section-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : simple.systemᵉ l2ᵉ Tᵉ} {Sᵉ : Tᵉ → UUᵉ l3ᵉ}
    {Bᵉ : simple.fibered-systemᵉ l4ᵉ Sᵉ Aᵉ} {fᵉ f'ᵉ : (Xᵉ : Tᵉ) → Sᵉ Xᵉ} {Hᵉ : fᵉ ~ᵉ f'ᵉ}
    {gᵉ : simple.section-systemᵉ Bᵉ fᵉ} {g'ᵉ : simple.section-systemᵉ Bᵉ f'ᵉ} →
    simple.htpy-section-systemᵉ Hᵉ gᵉ g'ᵉ →
    dependent.htpy-section-systemᵉ (section-systemᵉ gᵉ) (section-systemᵉ g'ᵉ)
  dependent.section-system.typeᵉ (htpy-section-systemᵉ {Hᵉ = Hᵉ} Kᵉ) = Hᵉ
  dependent.section-system.elementᵉ (htpy-section-systemᵉ {Hᵉ = Hᵉ} Kᵉ) =
    simple.section-system.elementᵉ Kᵉ
  dependent.section-system.sliceᵉ (htpy-section-systemᵉ {Hᵉ = Hᵉ} Kᵉ) Xᵉ =
    {!htpy-section-systemᵉ ?ᵉ !ᵉ}

  hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} {Sᵉ : UUᵉ l3ᵉ} {fᵉ : Tᵉ → Sᵉ}
    {Aᵉ : simple.systemᵉ l2ᵉ Tᵉ} {Bᵉ : simple.systemᵉ l4ᵉ Sᵉ} →
    simple.hom-systemᵉ fᵉ Aᵉ Bᵉ →
    dependent.hom-systemᵉ (systemᵉ Aᵉ) (systemᵉ Bᵉ)
  dependent.section-system.typeᵉ (hom-systemᵉ {fᵉ = fᵉ} hᵉ) = fᵉ
  dependent.section-system.elementᵉ (hom-systemᵉ hᵉ) =
    simple.section-system.elementᵉ hᵉ
  dependent.section-system.sliceᵉ (hom-systemᵉ hᵉ) Xᵉ =
    hom-systemᵉ (simple.section-system.sliceᵉ hᵉ Xᵉ)

  comp-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Sᵉ : UUᵉ l2ᵉ} {Rᵉ : UUᵉ l3ᵉ}
    {gᵉ : Sᵉ → Rᵉ} {fᵉ : Tᵉ → Sᵉ} {Aᵉ : simple.systemᵉ l4ᵉ Tᵉ} {Bᵉ : simple.systemᵉ l5ᵉ Sᵉ}
    {Cᵉ : simple.systemᵉ l6ᵉ Rᵉ} (kᵉ : simple.hom-systemᵉ gᵉ Bᵉ Cᵉ)
    (hᵉ : simple.hom-systemᵉ fᵉ Aᵉ Bᵉ) →
    dependent.htpy-hom-systemᵉ
      ( hom-systemᵉ
        ( simple.comp-hom-systemᵉ kᵉ hᵉ))
      ( dependent.comp-hom-systemᵉ
        ( hom-systemᵉ kᵉ)
        ( hom-systemᵉ hᵉ))
  dependent.section-system.typeᵉ (comp-hom-systemᵉ kᵉ hᵉ) Xᵉ = reflᵉ
  dependent.section-system.elementᵉ (comp-hom-systemᵉ kᵉ hᵉ) xᵉ = reflᵉ
  dependent.section-system.sliceᵉ (comp-hom-systemᵉ {fᵉ = fᵉ} kᵉ hᵉ) Xᵉ =
    comp-hom-systemᵉ
      ( simple.section-system.sliceᵉ kᵉ (fᵉ Xᵉ))
      ( simple.section-system.sliceᵉ hᵉ Xᵉ)

  htpy-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Sᵉ : UUᵉ l2ᵉ} {fᵉ : Tᵉ → Sᵉ}
    {Aᵉ : simple.systemᵉ l3ᵉ Tᵉ} {Bᵉ : simple.systemᵉ l4ᵉ Sᵉ}
    {gᵉ hᵉ : simple.hom-systemᵉ fᵉ Aᵉ Bᵉ} →
    simple.htpy-hom-systemᵉ gᵉ hᵉ →
    dependent.htpy-hom-systemᵉ (hom-systemᵉ gᵉ) (hom-systemᵉ hᵉ)
  dependent.section-system.typeᵉ (htpy-hom-systemᵉ Hᵉ) = refl-htpyᵉ
  dependent.section-system.elementᵉ (htpy-hom-systemᵉ {fᵉ = fᵉ} Hᵉ) {Xᵉ} xᵉ =
    simple.section-system.elementᵉ {fᵉ = {!!ᵉ}} Hᵉ xᵉ
    --simple.section-system.elementᵉ Hᵉ {Xᵉ} xᵉ
  dependent.section-system.sliceᵉ (htpy-hom-systemᵉ Hᵉ) Xᵉ =
    {!!ᵉ} --htpy-hom-systemᵉ (simple.section-system.sliceᵉ Hᵉ Xᵉ)

  weakeningᵉ :
    {l1ᵉ l2ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : simple.systemᵉ l2ᵉ Tᵉ} →
    simple.weakeningᵉ Aᵉ → dependent.weakeningᵉ (systemᵉ Aᵉ)
  dependent.weakening.typeᵉ (weakeningᵉ Wᵉ) Xᵉ =
    hom-systemᵉ (simple.weakening.elementᵉ Wᵉ Xᵉ)
  dependent.weakening.sliceᵉ (weakeningᵉ Wᵉ) Xᵉ =
    weakeningᵉ (simple.weakening.sliceᵉ Wᵉ Xᵉ)

  preserves-weakeningᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Tᵉ : UUᵉ l1ᵉ} {Sᵉ : UUᵉ l2ᵉ} {fᵉ : Tᵉ → Sᵉ}
    {Aᵉ : simple.systemᵉ l3ᵉ Tᵉ} {Bᵉ : simple.systemᵉ l4ᵉ Sᵉ}
    {WAᵉ : simple.weakeningᵉ Aᵉ} {WBᵉ : simple.weakeningᵉ Bᵉ}
    {gᵉ : simple.hom-systemᵉ fᵉ Aᵉ Bᵉ} →
    simple.preserves-weakeningᵉ WAᵉ WBᵉ gᵉ →
    dependent.preserves-weakeningᵉ
      ( weakeningᵉ WAᵉ)
      ( weakeningᵉ WBᵉ)
      ( hom-systemᵉ gᵉ)
  dependent.preserves-weakening.typeᵉ
    ( preserves-weakeningᵉ {fᵉ = fᵉ} {WAᵉ = WAᵉ} {WBᵉ} {gᵉ = gᵉ} Wgᵉ) Xᵉ =
    dependent.concat-htpy-hom-systemᵉ
      ( dependent.inv-htpy-hom-systemᵉ
        ( comp-hom-systemᵉ
          ( simple.section-system.sliceᵉ gᵉ Xᵉ)
          ( simple.weakening.elementᵉ WAᵉ Xᵉ)))
      ( dependent.concat-htpy-hom-systemᵉ
        ( htpy-hom-systemᵉ (simple.preserves-weakening.elementᵉ Wgᵉ Xᵉ))
        ( comp-hom-systemᵉ
          ( simple.weakening.elementᵉ WBᵉ (fᵉ Xᵉ))
          ( gᵉ)))
  dependent.preserves-weakening.sliceᵉ (preserves-weakeningᵉ Wgᵉ) Xᵉ =
    preserves-weakeningᵉ (simple.preserves-weakening.sliceᵉ Wgᵉ Xᵉ)

  substitutionᵉ :
    {l1ᵉ l2ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : simple.systemᵉ l2ᵉ Tᵉ} →
    simple.substitutionᵉ Aᵉ →
    dependent.substitutionᵉ (systemᵉ Aᵉ)
  dependent.substitution.typeᵉ
    ( substitutionᵉ Sᵉ) xᵉ =
    hom-systemᵉ (simple.substitution.elementᵉ Sᵉ xᵉ)
  dependent.substitution.sliceᵉ
    ( substitutionᵉ Sᵉ) Xᵉ =
    substitutionᵉ (simple.substitution.sliceᵉ Sᵉ Xᵉ)

  generic-elementᵉ :
    {l1ᵉ l2ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : simple.systemᵉ l2ᵉ Tᵉ} →
    (Wᵉ : simple.weakeningᵉ Aᵉ) → simple.generic-elementᵉ Aᵉ →
    dependent.generic-elementᵉ (weakeningᵉ Wᵉ)
  dependent.generic-element.typeᵉ
    ( generic-elementᵉ Wᵉ δᵉ) Xᵉ =
    simple.generic-element.elementᵉ δᵉ Xᵉ
  dependent.generic-element.sliceᵉ
    ( generic-elementᵉ Wᵉ δᵉ) Xᵉ =
    generic-elementᵉ
      ( simple.weakening.sliceᵉ Wᵉ Xᵉ)
      ( simple.generic-element.sliceᵉ δᵉ Xᵉ)

  weakening-preserves-weakeningᵉ :
    {l1ᵉ l2ᵉ : Level} {Tᵉ : UUᵉ l1ᵉ} {Aᵉ : simple.systemᵉ l2ᵉ Tᵉ}
    {Wᵉ : simple.weakeningᵉ Aᵉ} →
    simple.weakening-preserves-weakeningᵉ Wᵉ →
    dependent.weakening-preserves-weakeningᵉ (weakeningᵉ Wᵉ)
  dependent.weakening-preserves-weakening.typeᵉ
    ( weakening-preserves-weakeningᵉ WWᵉ) Xᵉ =
    preserves-weakeningᵉ (simple.weakening-preserves-weakening.elementᵉ WWᵉ Xᵉ)
  dependent.weakening-preserves-weakening.sliceᵉ
    ( weakening-preserves-weakeningᵉ WWᵉ) Xᵉ =
    weakening-preserves-weakeningᵉ
      ( simple.weakening-preserves-weakening.sliceᵉ WWᵉ Xᵉ)
```