# The Regensburg extension of the fundamental theorem of identity types

```agda
module
  foundation.regensburg-extension-fundamental-theorem-of-identity-typesᵉ
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.connected-mapsᵉ
open import foundation.connected-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fiber-inclusionsᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.functoriality-truncationᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.separated-typesᵉ
open import foundation.subuniversesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.truncated-mapsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **Regensburgᵉ extension**ᵉ ofᵉ theᵉ
[fundamentalᵉ theoremᵉ ofᵉ identityᵉ types](foundation.fundamental-theorem-of-identity-types.mdᵉ)
assertsᵉ thatᵉ forᵉ anyᵉ [subuniverse](foundation.subuniverses.mdᵉ) `P`,ᵉ andᵉ anyᵉ
[pointed](structured-types.pointed-types.mdᵉ)
[connectedᵉ type](foundation.connected-types.mdᵉ) `A`ᵉ equippedᵉ with aᵉ typeᵉ familyᵉ
`B`ᵉ overᵉ `A`,ᵉ theᵉ followingᵉ areᵉ
[logicallyᵉ equivalent](foundation.logical-equivalences.mdᵉ):

1.ᵉ Everyᵉ familyᵉ ofᵉ mapsᵉ `fᵉ : (xᵉ : Aᵉ) → (*ᵉ ＝ᵉ xᵉ) → Bᵉ x`ᵉ isᵉ aᵉ familyᵉ ofᵉ `P`-maps,ᵉ
   i.e.,ᵉ aᵉ familyᵉ ofᵉ mapsᵉ with [fibers](foundation-core.fibers-of-maps.mdᵉ) in
   `P`.ᵉ
2.ᵉ Theᵉ [totalᵉ space](foundation.dependent-pair-types.mdᵉ) `Σᵉ Aᵉ B`ᵉ isᵉ
   [`P`-separated](foundation.separated-types.md),ᵉ i.e.,ᵉ itsᵉ
   [identityᵉ types](foundation-core.identity-types.mdᵉ) areᵉ in `P`.ᵉ

Inᵉ otherᵉ words,ᵉ theᵉ extendedᵉ fundamentalᵉ theoremᵉ ofᵉ
[identityᵉ types](foundation-core.identity-types.mdᵉ) assertsᵉ thatᵉ forᵉ anyᵉ
[higherᵉ group](higher-group-theory.higher-groups.mdᵉ) `BG`ᵉ equippedᵉ with aᵉ
[higherᵉ groupᵉ action](higher-group-theory.higher-group-actions.mdᵉ) `X`,ᵉ everyᵉ
[homomorphismᵉ ofᵉ higherᵉ groupᵉ actions](higher-group-theory.homomorphisms-higher-group-actions.mdᵉ)
`fᵉ : (uᵉ : BGᵉ) → (*ᵉ ＝ᵉ uᵉ) → Xᵉ u`ᵉ consistsᵉ ofᵉ aᵉ familyᵉ ofᵉ `P`ᵉ mapsᵉ ifᵉ andᵉ onlyᵉ ifᵉ
theᵉ typeᵉ ofᵉ [orbits](higher-group-theory.orbits-higher-group-actions.mdᵉ) ofᵉ `X`ᵉ
isᵉ `P`-separated.ᵉ

**Proof:**ᵉ Supposeᵉ thatᵉ everyᵉ familyᵉ ofᵉ mapsᵉ `fᵉ : (xᵉ : Aᵉ) → (*ᵉ ＝ᵉ xᵉ) → Bᵉ x`ᵉ isᵉ aᵉ
familyᵉ ofᵉ `P`-maps.ᵉ Theᵉ [fiber](foundation-core.fibers-of-maps.mdᵉ) ofᵉ suchᵉ
`fᵉ xᵉ : (*ᵉ ＝ᵉ xᵉ) → Bᵉ x`ᵉ atᵉ `y`ᵉ isᵉ [equivalent](foundation-core.equivalences.mdᵉ)
to theᵉ typeᵉ `(*ᵉ ,ᵉ fᵉ *ᵉ reflᵉ) ＝ᵉ (xᵉ ,ᵉ y)`.ᵉ Ourᵉ assumptionᵉ isᵉ thereforeᵉ equivalentᵉ
to theᵉ assumptionᵉ thatᵉ theᵉ typeᵉ `(*ᵉ ,ᵉ fᵉ *ᵉ reflᵉ) ＝ᵉ (xᵉ ,ᵉ y)`ᵉ isᵉ in `P`ᵉ forᵉ everyᵉ
`f`,ᵉ `x`,ᵉ andᵉ `y`.ᵉ Byᵉ theᵉ
[universalᵉ propertyᵉ ofᵉ identityᵉ types](foundation.universal-property-identity-types.md),ᵉ
thisᵉ conditionᵉ isᵉ equivalentᵉ to theᵉ conditionᵉ thatᵉ `(*ᵉ ,ᵉ y'ᵉ) ＝ᵉ (xᵉ ,ᵉ y)`ᵉ isᵉ in
`P`ᵉ forᵉ everyᵉ `y'`,ᵉ `x`,ᵉ andᵉ `y`.ᵉ Finally,ᵉ sinceᵉ `A`ᵉ isᵉ assumedᵉ to beᵉ connected,ᵉ
thisᵉ conditionᵉ isᵉ equivalentᵉ to theᵉ conditionᵉ thatᵉ `Σᵉ Aᵉ B`ᵉ isᵉ `P`-separated.ᵉ

Thisᵉ theoremᵉ wasᵉ statedᵉ andᵉ provenᵉ forᵉ theᵉ firstᵉ timeᵉ duringᵉ theᵉ
[Interactionsᵉ ofᵉ Proofᵉ Assistantsᵉ andᵉ Mathematics](https://itp-school-2023.github.ioᵉ)
summerᵉ schoolᵉ in Regensburg,ᵉ 2023,ᵉ asᵉ partᵉ ofᵉ Egbertᵉ Rijke'sᵉ tutorialᵉ onᵉ
formalizationᵉ in agda-unimath.ᵉ

## Theorem

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ (l1ᵉ ⊔ l2ᵉ) l3ᵉ)
  {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  abstract
    forward-implication-extended-fundamental-theorem-idᵉ :
      is-0-connectedᵉ Aᵉ →
      ((fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ) (xᵉ : Aᵉ) → is-in-subuniverse-mapᵉ Pᵉ (fᵉ xᵉ)) →
      is-separatedᵉ Pᵉ (Σᵉ Aᵉ Bᵉ)
    forward-implication-extended-fundamental-theorem-idᵉ Hᵉ Kᵉ (xᵉ ,ᵉ yᵉ) (x'ᵉ ,ᵉ y'ᵉ) =
      apply-universal-property-trunc-Propᵉ
        ( mere-eq-is-0-connectedᵉ Hᵉ aᵉ xᵉ)
        ( Pᵉ _)
        ( λ where
          reflᵉ →
            is-in-subuniverse-equivᵉ Pᵉ
              ( compute-fiber-map-out-of-identity-typeᵉ
                ( ind-Idᵉ aᵉ (λ uᵉ vᵉ → Bᵉ uᵉ) yᵉ)
                ( x'ᵉ)
                ( y'ᵉ))
              ( Kᵉ (ind-Idᵉ aᵉ (λ uᵉ vᵉ → Bᵉ uᵉ) yᵉ) x'ᵉ y'ᵉ))

  abstract
    backward-implication-extended-fundamental-theorem-idᵉ :
      is-separatedᵉ Pᵉ (Σᵉ Aᵉ Bᵉ) →
      (fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ) (xᵉ : Aᵉ) → is-in-subuniverse-mapᵉ Pᵉ (fᵉ xᵉ)
    backward-implication-extended-fundamental-theorem-idᵉ Kᵉ fᵉ xᵉ yᵉ =
      is-in-subuniverse-equiv'ᵉ Pᵉ
        ( compute-fiber-map-out-of-identity-typeᵉ fᵉ xᵉ yᵉ)
        ( Kᵉ (aᵉ ,ᵉ fᵉ aᵉ reflᵉ) (xᵉ ,ᵉ yᵉ))

  abstract
    extended-fundamental-theorem-idᵉ :
      is-0-connectedᵉ Aᵉ →
      ((fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ) (xᵉ : Aᵉ) → is-in-subuniverse-mapᵉ Pᵉ (fᵉ xᵉ)) ↔ᵉ
      is-separatedᵉ Pᵉ (Σᵉ Aᵉ Bᵉ)
    pr1ᵉ (extended-fundamental-theorem-idᵉ Hᵉ) =
      forward-implication-extended-fundamental-theorem-idᵉ Hᵉ
    pr2ᵉ (extended-fundamental-theorem-idᵉ Hᵉ) =
      backward-implication-extended-fundamental-theorem-idᵉ
```

## Corollaries

### Characterizing families of surjective maps out of identity types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  forward-implication-extended-fundamental-theorem-id-surjectiveᵉ :
    is-0-connectedᵉ Aᵉ →
    ( (fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ) → (xᵉ : Aᵉ) → is-surjectiveᵉ (fᵉ xᵉ)) →
    is-inhabitedᵉ (Bᵉ aᵉ) → is-0-connectedᵉ (Σᵉ Aᵉ Bᵉ)
  forward-implication-extended-fundamental-theorem-id-surjectiveᵉ Hᵉ Kᵉ Lᵉ =
    is-0-connected-mere-eq-is-inhabitedᵉ
      ( map-trunc-Propᵉ (fiber-inclusionᵉ Bᵉ aᵉ) Lᵉ)
      ( forward-implication-extended-fundamental-theorem-idᵉ
        ( is-inhabited-Propᵉ)
        ( aᵉ)
        ( Hᵉ)
        ( Kᵉ))

  backward-implication-extended-fundamental-theorem-id-surjectiveᵉ :
    is-0-connectedᵉ (Σᵉ Aᵉ Bᵉ) →
    (fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ) (xᵉ : Aᵉ) → is-surjectiveᵉ (fᵉ xᵉ)
  backward-implication-extended-fundamental-theorem-id-surjectiveᵉ Lᵉ =
    backward-implication-extended-fundamental-theorem-idᵉ
      ( is-inhabited-Propᵉ)
      ( aᵉ)
      ( mere-eq-is-0-connectedᵉ Lᵉ)

  extended-fundamental-theorem-id-surjectiveᵉ :
    is-0-connectedᵉ Aᵉ → is-inhabitedᵉ (Bᵉ aᵉ) →
    ( (fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ) → (xᵉ : Aᵉ) → is-surjectiveᵉ (fᵉ xᵉ)) ↔ᵉ
    is-0-connectedᵉ (Σᵉ Aᵉ Bᵉ)
  pr1ᵉ (extended-fundamental-theorem-id-surjectiveᵉ Hᵉ Kᵉ) Lᵉ =
    forward-implication-extended-fundamental-theorem-id-surjectiveᵉ Hᵉ Lᵉ Kᵉ
  pr2ᵉ ( extended-fundamental-theorem-id-surjectiveᵉ Hᵉ Kᵉ) =
    backward-implication-extended-fundamental-theorem-id-surjectiveᵉ
```

### Characterizing families of connected maps out of identity types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ)
  {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Hᵉ : is-0-connectedᵉ Aᵉ)
  where

  forward-implication-extended-fundamental-theorem-id-connectedᵉ :
    ( (fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ) → (xᵉ : Aᵉ) → is-connected-mapᵉ kᵉ (fᵉ xᵉ)) →
    is-inhabitedᵉ (Bᵉ aᵉ) → is-connectedᵉ (succ-𝕋ᵉ kᵉ) (Σᵉ Aᵉ Bᵉ)
  forward-implication-extended-fundamental-theorem-id-connectedᵉ Kᵉ Lᵉ =
    is-connected-succ-is-connected-eqᵉ
      ( map-trunc-Propᵉ (fiber-inclusionᵉ Bᵉ aᵉ) Lᵉ)
      ( forward-implication-extended-fundamental-theorem-idᵉ
        ( is-connected-Propᵉ kᵉ)
        ( aᵉ)
        ( Hᵉ)
        ( Kᵉ))

  backward-implication-extended-fundamental-theorem-id-connectedᵉ :
    is-connectedᵉ (succ-𝕋ᵉ kᵉ) (Σᵉ Aᵉ Bᵉ) →
    (fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ) (xᵉ : Aᵉ) → is-connected-mapᵉ kᵉ (fᵉ xᵉ)
  backward-implication-extended-fundamental-theorem-id-connectedᵉ Kᵉ =
    backward-implication-extended-fundamental-theorem-idᵉ
      ( is-connected-Propᵉ kᵉ)
      ( aᵉ)
      ( λ xᵉ yᵉ → is-connected-eq-is-connectedᵉ Kᵉ)

  extended-fundamental-theorem-id-connectedᵉ :
    is-0-connectedᵉ Aᵉ → is-inhabitedᵉ (Bᵉ aᵉ) →
    ((fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ) (xᵉ : Aᵉ) → is-connected-mapᵉ kᵉ (fᵉ xᵉ)) ↔ᵉ
    is-connectedᵉ (succ-𝕋ᵉ kᵉ) (Σᵉ Aᵉ Bᵉ)
  pr1ᵉ (extended-fundamental-theorem-id-connectedᵉ Hᵉ Kᵉ) Lᵉ =
    forward-implication-extended-fundamental-theorem-id-connectedᵉ Lᵉ Kᵉ
  pr2ᵉ (extended-fundamental-theorem-id-connectedᵉ Hᵉ Kᵉ) =
    backward-implication-extended-fundamental-theorem-id-connectedᵉ
```

### Characterizing families of truncated maps out of identity types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  forward-implication-extended-fundamental-theorem-id-truncatedᵉ :
    is-0-connectedᵉ Aᵉ →
    ((fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ) → (xᵉ : Aᵉ) → is-trunc-mapᵉ kᵉ (fᵉ xᵉ)) →
    is-truncᵉ (succ-𝕋ᵉ kᵉ) (Σᵉ Aᵉ Bᵉ)
  forward-implication-extended-fundamental-theorem-id-truncatedᵉ =
    forward-implication-extended-fundamental-theorem-idᵉ
      ( is-trunc-Propᵉ kᵉ)
      ( aᵉ)

  backward-implication-extended-fundamental-theorem-id-truncatedᵉ :
    is-truncᵉ (succ-𝕋ᵉ kᵉ) (Σᵉ Aᵉ Bᵉ) →
    (fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ) (xᵉ : Aᵉ) → is-trunc-mapᵉ kᵉ (fᵉ xᵉ)
  backward-implication-extended-fundamental-theorem-id-truncatedᵉ =
    backward-implication-extended-fundamental-theorem-idᵉ
      ( is-trunc-Propᵉ kᵉ)
      ( aᵉ)

  extended-fundamental-theorem-id-truncatedᵉ :
    is-0-connectedᵉ Aᵉ →
    ((fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ) (xᵉ : Aᵉ) → is-trunc-mapᵉ kᵉ (fᵉ xᵉ)) ↔ᵉ
    is-truncᵉ (succ-𝕋ᵉ kᵉ) (Σᵉ Aᵉ Bᵉ)
  pr1ᵉ (extended-fundamental-theorem-id-truncatedᵉ Hᵉ) =
    forward-implication-extended-fundamental-theorem-id-truncatedᵉ Hᵉ
  pr2ᵉ (extended-fundamental-theorem-id-truncatedᵉ Hᵉ) =
    backward-implication-extended-fundamental-theorem-id-truncatedᵉ
```

## See also

Theᵉ Regensburgᵉ extensionᵉ ofᵉ theᵉ fundamentalᵉ theoremᵉ isᵉ usedᵉ in theᵉ followingᵉ
filesᵉ:

-ᵉ Inᵉ
  [`higher-group-theory.free-higher-group-actions.md`](higher-group-theory.free-higher-group-actions.mdᵉ)
  itᵉ isᵉ usedᵉ to showᵉ thatᵉ aᵉ higherᵉ groupᵉ actionᵉ isᵉ freeᵉ ifᵉ andᵉ onlyᵉ itsᵉ totalᵉ
  spaceᵉ isᵉ aᵉ set.ᵉ
-ᵉ Inᵉ
  [`higher-group-theory.transitive-higher-group-actions.md`](higher-group-theory.transitive-higher-group-actions.mdᵉ)
  itᵉ isᵉ usedᵉ to showᵉ thatᵉ aᵉ higherᵉ groupᵉ actionᵉ isᵉ transitiveᵉ ifᵉ andᵉ onlyᵉ ifᵉ itsᵉ
  totalᵉ spaceᵉ isᵉ connected.ᵉ

## References

Twoᵉ specialᵉ casesᵉ ofᵉ theᵉ extendedᵉ fundamentalᵉ theoremᵉ ofᵉ identityᵉ typesᵉ areᵉ
statedᵉ in {{#citeᵉ Rij22ᵉ}}: Theᵉ caseᵉ where `P`ᵉ isᵉ theᵉ subuniverseᵉ ofᵉ
`k`-truncatedᵉ typesᵉ isᵉ statedᵉ asᵉ Theoremᵉ 19.6.2;ᵉ andᵉ theᵉ caseᵉ where `P`ᵉ isᵉ theᵉ
subuniverseᵉ ofᵉ inhabitedᵉ typesᵉ isᵉ statedᵉ asᵉ Exerciseᵉ 19.14.ᵉ

{{#bibliographyᵉ}}