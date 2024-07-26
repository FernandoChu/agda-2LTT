# Normal submonoids

```agda
module group-theory.normal-submonoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.congruence-relations-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.saturated-congruence-relations-monoidsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.submonoidsᵉ
open import group-theory.subsets-monoidsᵉ
```

</details>

## Idea

Aᵉ **normalᵉ submonoid**ᵉ `N`ᵉ ofᵉ `M`ᵉ isᵉ aᵉ monoidᵉ forᵉ whichᵉ thereᵉ existsᵉ aᵉ
congruenceᵉ relationᵉ `~`ᵉ onᵉ `M`ᵉ suchᵉ thatᵉ theᵉ elementsᵉ ofᵉ `N`ᵉ areᵉ preciselyᵉ theᵉ
elementsᵉ `xᵉ ~ᵉ 1`.ᵉ Suchᵉ aᵉ congruenceᵉ relationᵉ isᵉ rarelyᵉ unique.ᵉ However,ᵉ oneᵉ canᵉ
showᵉ thatᵉ theᵉ normalᵉ submonoidsᵉ formᵉ aᵉ retractᵉ ofᵉ theᵉ typeᵉ ofᵉ congruenceᵉ
relationsᵉ onᵉ `M`,ᵉ andᵉ thatᵉ theᵉ normalᵉ submonoidsᵉ correspondᵉ uniquelyᵉ to
_saturatedᵉ_ congruenceᵉ relations.ᵉ

Aᵉ submonoidᵉ `N`ᵉ ofᵉ `M`ᵉ isᵉ normalᵉ ifᵉ andᵉ onlyᵉ ifᵉ forᵉ allᵉ `xᵉ yᵉ : M`ᵉ andᵉ `uᵉ : N`ᵉ weᵉ
haveᵉ

```text
  xuyᵉ ∈ᵉ Nᵉ ⇔ᵉ xyᵉ ∈ᵉ N.ᵉ
```

## Definitions

### Normal submonoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Submonoidᵉ l2ᵉ Mᵉ)
  where

  is-normal-prop-Submonoidᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-normal-prop-Submonoidᵉ =
    Π-Propᵉ
      ( type-Monoidᵉ Mᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Monoidᵉ Mᵉ)
          ( λ yᵉ →
            Π-Propᵉ
              ( type-Monoidᵉ Mᵉ)
              ( λ uᵉ →
                function-Propᵉ
                  ( is-in-Submonoidᵉ Mᵉ Nᵉ uᵉ)
                  ( iff-Propᵉ
                    ( subset-Submonoidᵉ Mᵉ Nᵉ (mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ xᵉ uᵉ) yᵉ))
                    ( subset-Submonoidᵉ Mᵉ Nᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ))))))

  is-normal-Submonoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-normal-Submonoidᵉ = type-Propᵉ is-normal-prop-Submonoidᵉ

  is-prop-is-normal-Submonoidᵉ : is-propᵉ is-normal-Submonoidᵉ
  is-prop-is-normal-Submonoidᵉ = is-prop-type-Propᵉ is-normal-prop-Submonoidᵉ

Normal-Submonoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → Monoidᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Normal-Submonoidᵉ l2ᵉ Mᵉ = Σᵉ (Submonoidᵉ l2ᵉ Mᵉ) (is-normal-Submonoidᵉ Mᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Normal-Submonoidᵉ l2ᵉ Mᵉ)
  where

  submonoid-Normal-Submonoidᵉ : Submonoidᵉ l2ᵉ Mᵉ
  submonoid-Normal-Submonoidᵉ = pr1ᵉ Nᵉ

  is-normal-Normal-Submonoidᵉ : is-normal-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ
  is-normal-Normal-Submonoidᵉ = pr2ᵉ Nᵉ

  subset-Normal-Submonoidᵉ : subtypeᵉ l2ᵉ (type-Monoidᵉ Mᵉ)
  subset-Normal-Submonoidᵉ =
    subset-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  is-submonoid-Normal-Submonoidᵉ :
    is-submonoid-subset-Monoidᵉ Mᵉ subset-Normal-Submonoidᵉ
  is-submonoid-Normal-Submonoidᵉ =
    is-submonoid-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  is-in-Normal-Submonoidᵉ : type-Monoidᵉ Mᵉ → UUᵉ l2ᵉ
  is-in-Normal-Submonoidᵉ =
    is-in-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  is-prop-is-in-Normal-Submonoidᵉ :
    (xᵉ : type-Monoidᵉ Mᵉ) → is-propᵉ (is-in-Normal-Submonoidᵉ xᵉ)
  is-prop-is-in-Normal-Submonoidᵉ =
    is-prop-is-in-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  is-closed-under-eq-Normal-Submonoidᵉ :
    {xᵉ yᵉ : type-Monoidᵉ Mᵉ} → is-in-Normal-Submonoidᵉ xᵉ → (xᵉ ＝ᵉ yᵉ) →
    is-in-Normal-Submonoidᵉ yᵉ
  is-closed-under-eq-Normal-Submonoidᵉ =
    is-closed-under-eq-subtypeᵉ subset-Normal-Submonoidᵉ

  is-closed-under-eq-Normal-Submonoid'ᵉ :
    {xᵉ yᵉ : type-Monoidᵉ Mᵉ} → is-in-Normal-Submonoidᵉ yᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-Normal-Submonoidᵉ xᵉ
  is-closed-under-eq-Normal-Submonoid'ᵉ =
    is-closed-under-eq-subtype'ᵉ subset-Normal-Submonoidᵉ

  type-Normal-Submonoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Normal-Submonoidᵉ = type-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  is-set-type-Normal-Submonoidᵉ : is-setᵉ type-Normal-Submonoidᵉ
  is-set-type-Normal-Submonoidᵉ =
    is-set-type-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  set-Normal-Submonoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Normal-Submonoidᵉ = set-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  inclusion-Normal-Submonoidᵉ : type-Normal-Submonoidᵉ → type-Monoidᵉ Mᵉ
  inclusion-Normal-Submonoidᵉ = inclusion-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  ap-inclusion-Normal-Submonoidᵉ :
    (xᵉ yᵉ : type-Normal-Submonoidᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-Normal-Submonoidᵉ xᵉ ＝ᵉ inclusion-Normal-Submonoidᵉ yᵉ
  ap-inclusion-Normal-Submonoidᵉ =
    ap-inclusion-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  is-in-submonoid-inclusion-Normal-Submonoidᵉ :
    (xᵉ : type-Normal-Submonoidᵉ) →
    is-in-Normal-Submonoidᵉ (inclusion-Normal-Submonoidᵉ xᵉ)
  is-in-submonoid-inclusion-Normal-Submonoidᵉ =
    is-in-submonoid-inclusion-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  contains-unit-Normal-Submonoidᵉ : is-in-Normal-Submonoidᵉ (unit-Monoidᵉ Mᵉ)
  contains-unit-Normal-Submonoidᵉ =
    contains-unit-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  unit-Normal-Submonoidᵉ : type-Normal-Submonoidᵉ
  unit-Normal-Submonoidᵉ = unit-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  is-closed-under-multiplication-Normal-Submonoidᵉ :
    {xᵉ yᵉ : type-Monoidᵉ Mᵉ} →
    is-in-Normal-Submonoidᵉ xᵉ → is-in-Normal-Submonoidᵉ yᵉ →
    is-in-Normal-Submonoidᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ)
  is-closed-under-multiplication-Normal-Submonoidᵉ =
    is-closed-under-multiplication-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  mul-Normal-Submonoidᵉ : (xᵉ yᵉ : type-Normal-Submonoidᵉ) → type-Normal-Submonoidᵉ
  mul-Normal-Submonoidᵉ = mul-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  associative-mul-Normal-Submonoidᵉ :
    (xᵉ yᵉ zᵉ : type-Normal-Submonoidᵉ) →
    (mul-Normal-Submonoidᵉ (mul-Normal-Submonoidᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    (mul-Normal-Submonoidᵉ xᵉ (mul-Normal-Submonoidᵉ yᵉ zᵉ))
  associative-mul-Normal-Submonoidᵉ =
    associative-mul-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  semigroup-Normal-Submonoidᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-Normal-Submonoidᵉ =
    semigroup-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  left-unit-law-mul-Normal-Submonoidᵉ :
    (xᵉ : type-Normal-Submonoidᵉ) →
    mul-Normal-Submonoidᵉ unit-Normal-Submonoidᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Normal-Submonoidᵉ =
    left-unit-law-mul-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  right-unit-law-mul-Normal-Submonoidᵉ :
    (xᵉ : type-Normal-Submonoidᵉ) →
    mul-Normal-Submonoidᵉ xᵉ unit-Normal-Submonoidᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Normal-Submonoidᵉ =
    right-unit-law-mul-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ

  monoid-Normal-Submonoidᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  monoid-Normal-Submonoidᵉ = monoid-Submonoidᵉ Mᵉ submonoid-Normal-Submonoidᵉ
```

## Properties

### Extensionality of the type of all normal submonoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Normal-Submonoidᵉ l2ᵉ Mᵉ)
  where

  has-same-elements-Normal-Submonoidᵉ :
    {l3ᵉ : Level} → Normal-Submonoidᵉ l3ᵉ Mᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-Normal-Submonoidᵉ Kᵉ =
    has-same-elements-Submonoidᵉ Mᵉ
      ( submonoid-Normal-Submonoidᵉ Mᵉ Nᵉ)
      ( submonoid-Normal-Submonoidᵉ Mᵉ Kᵉ)

  extensionality-Normal-Submonoidᵉ :
    (Kᵉ : Normal-Submonoidᵉ l2ᵉ Mᵉ) →
    (Nᵉ ＝ᵉ Kᵉ) ≃ᵉ has-same-elements-Normal-Submonoidᵉ Kᵉ
  extensionality-Normal-Submonoidᵉ =
    extensionality-type-subtypeᵉ
      ( is-normal-prop-Submonoidᵉ Mᵉ)
      ( is-normal-Normal-Submonoidᵉ Mᵉ Nᵉ)
      ( λ xᵉ → (idᵉ ,ᵉ idᵉ))
      ( extensionality-Submonoidᵉ Mᵉ (submonoid-Normal-Submonoidᵉ Mᵉ Nᵉ))

  eq-has-same-elements-Normal-Submonoidᵉ :
    (Kᵉ : Normal-Submonoidᵉ l2ᵉ Mᵉ) →
    has-same-elements-Normal-Submonoidᵉ Kᵉ → Nᵉ ＝ᵉ Kᵉ
  eq-has-same-elements-Normal-Submonoidᵉ Kᵉ =
    map-inv-equivᵉ (extensionality-Normal-Submonoidᵉ Kᵉ)
```

### The congruence relation of a normal submonoid

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Normal-Submonoidᵉ l2ᵉ Mᵉ)
  where

  rel-congruence-Normal-Submonoidᵉ : Relation-Propᵉ (l1ᵉ ⊔ l2ᵉ) (type-Monoidᵉ Mᵉ)
  rel-congruence-Normal-Submonoidᵉ xᵉ yᵉ =
    Π-Propᵉ
      ( type-Monoidᵉ Mᵉ)
      ( λ uᵉ →
        Π-Propᵉ
          ( type-Monoidᵉ Mᵉ)
          ( λ vᵉ →
            iff-Propᵉ
              ( subset-Normal-Submonoidᵉ Mᵉ Nᵉ
                ( mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ xᵉ) vᵉ))
              ( subset-Normal-Submonoidᵉ Mᵉ Nᵉ
                ( mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ yᵉ) vᵉ))))

  sim-congruence-Normal-Submonoidᵉ : (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  sim-congruence-Normal-Submonoidᵉ xᵉ yᵉ =
    type-Propᵉ (rel-congruence-Normal-Submonoidᵉ xᵉ yᵉ)

  refl-congruence-Normal-Submonoidᵉ :
    is-reflexiveᵉ sim-congruence-Normal-Submonoidᵉ
  pr1ᵉ (refl-congruence-Normal-Submonoidᵉ _ uᵉ vᵉ) = idᵉ
  pr2ᵉ (refl-congruence-Normal-Submonoidᵉ _ uᵉ vᵉ) = idᵉ

  symmetric-congruence-Normal-Submonoidᵉ :
    is-symmetricᵉ sim-congruence-Normal-Submonoidᵉ
  pr1ᵉ (symmetric-congruence-Normal-Submonoidᵉ _ _ Hᵉ uᵉ vᵉ) = pr2ᵉ (Hᵉ uᵉ vᵉ)
  pr2ᵉ (symmetric-congruence-Normal-Submonoidᵉ _ _ Hᵉ uᵉ vᵉ) = pr1ᵉ (Hᵉ uᵉ vᵉ)

  transitive-congruence-Normal-Submonoidᵉ :
    is-transitiveᵉ sim-congruence-Normal-Submonoidᵉ
  transitive-congruence-Normal-Submonoidᵉ _ _ _ Hᵉ Kᵉ uᵉ vᵉ = (Hᵉ uᵉ vᵉ) ∘iffᵉ (Kᵉ uᵉ vᵉ)

  equivalence-relation-congruence-Normal-Submonoidᵉ :
    equivalence-relationᵉ (l1ᵉ ⊔ l2ᵉ) (type-Monoidᵉ Mᵉ)
  pr1ᵉ equivalence-relation-congruence-Normal-Submonoidᵉ =
    rel-congruence-Normal-Submonoidᵉ
  pr1ᵉ (pr2ᵉ equivalence-relation-congruence-Normal-Submonoidᵉ) =
    refl-congruence-Normal-Submonoidᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-congruence-Normal-Submonoidᵉ)) =
    symmetric-congruence-Normal-Submonoidᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-congruence-Normal-Submonoidᵉ)) =
    transitive-congruence-Normal-Submonoidᵉ

  is-congruence-congruence-Normal-Submonoidᵉ :
    is-congruence-Monoidᵉ Mᵉ equivalence-relation-congruence-Normal-Submonoidᵉ
  pr1ᵉ (is-congruence-congruence-Normal-Submonoidᵉ {xᵉ} {x'ᵉ} {yᵉ} {y'ᵉ} Hᵉ Kᵉ uᵉ vᵉ) Lᵉ =
    is-closed-under-eq-Normal-Submonoidᵉ Mᵉ Nᵉ
      ( forward-implicationᵉ
        ( Hᵉ uᵉ (mul-Monoidᵉ Mᵉ y'ᵉ vᵉ))
        ( is-closed-under-eq-Normal-Submonoidᵉ Mᵉ Nᵉ
          ( forward-implicationᵉ
            ( Kᵉ (mul-Monoidᵉ Mᵉ uᵉ xᵉ) vᵉ)
            ( is-closed-under-eq-Normal-Submonoidᵉ Mᵉ Nᵉ Lᵉ
              ( apᵉ (mul-Monoid'ᵉ Mᵉ vᵉ) (invᵉ (associative-mul-Monoidᵉ Mᵉ uᵉ xᵉ yᵉ)))))
          ( associative-mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ xᵉ) y'ᵉ vᵉ)))
      ( ( invᵉ (associative-mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ x'ᵉ) y'ᵉ vᵉ)) ∙ᵉ
        ( apᵉ (mul-Monoid'ᵉ Mᵉ vᵉ) (associative-mul-Monoidᵉ Mᵉ uᵉ x'ᵉ y'ᵉ)))
  pr2ᵉ (is-congruence-congruence-Normal-Submonoidᵉ {xᵉ} {x'ᵉ} {yᵉ} {y'ᵉ} Hᵉ Kᵉ uᵉ vᵉ) Lᵉ =
    is-closed-under-eq-Normal-Submonoidᵉ Mᵉ Nᵉ
      ( backward-implicationᵉ
        ( Hᵉ uᵉ (mul-Monoidᵉ Mᵉ yᵉ vᵉ))
        ( is-closed-under-eq-Normal-Submonoidᵉ Mᵉ Nᵉ
          ( backward-implicationᵉ
            ( Kᵉ (mul-Monoidᵉ Mᵉ uᵉ x'ᵉ) vᵉ)
            ( is-closed-under-eq-Normal-Submonoidᵉ Mᵉ Nᵉ Lᵉ
              ( apᵉ (mul-Monoid'ᵉ Mᵉ vᵉ) (invᵉ (associative-mul-Monoidᵉ Mᵉ uᵉ x'ᵉ y'ᵉ)))))
          ( associative-mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ x'ᵉ) yᵉ vᵉ)))
      ( ( invᵉ (associative-mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ xᵉ) yᵉ vᵉ)) ∙ᵉ
        ( apᵉ (mul-Monoid'ᵉ Mᵉ vᵉ) (associative-mul-Monoidᵉ Mᵉ uᵉ xᵉ yᵉ)))

  congruence-Normal-Submonoidᵉ : congruence-Monoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ
  pr1ᵉ congruence-Normal-Submonoidᵉ =
    equivalence-relation-congruence-Normal-Submonoidᵉ
  pr2ᵉ congruence-Normal-Submonoidᵉ = is-congruence-congruence-Normal-Submonoidᵉ
```

### The normal submonoid obtained from a congruence relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ : congruence-Monoidᵉ l2ᵉ Mᵉ)
  where

  subset-normal-submonoid-congruence-Monoidᵉ :
    subtypeᵉ l2ᵉ (type-Monoidᵉ Mᵉ)
  subset-normal-submonoid-congruence-Monoidᵉ xᵉ =
    prop-congruence-Monoidᵉ Mᵉ Rᵉ xᵉ (unit-Monoidᵉ Mᵉ)

  is-in-normal-submonoid-congruence-Monoidᵉ : type-Monoidᵉ Mᵉ → UUᵉ l2ᵉ
  is-in-normal-submonoid-congruence-Monoidᵉ =
    is-in-subtypeᵉ subset-normal-submonoid-congruence-Monoidᵉ

  contains-unit-normal-submonoid-congruence-Monoidᵉ :
    is-in-normal-submonoid-congruence-Monoidᵉ (unit-Monoidᵉ Mᵉ)
  contains-unit-normal-submonoid-congruence-Monoidᵉ =
    refl-congruence-Monoidᵉ Mᵉ Rᵉ (unit-Monoidᵉ Mᵉ)

  is-closed-under-multiplication-normal-submonoid-congruence-Monoidᵉ :
    is-closed-under-multiplication-subset-Monoidᵉ Mᵉ
      subset-normal-submonoid-congruence-Monoidᵉ
  is-closed-under-multiplication-normal-submonoid-congruence-Monoidᵉ xᵉ yᵉ Hᵉ Kᵉ =
    concatenate-sim-eq-congruence-Monoidᵉ Mᵉ Rᵉ
      ( mul-congruence-Monoidᵉ Mᵉ Rᵉ Hᵉ Kᵉ)
      ( left-unit-law-mul-Monoidᵉ Mᵉ (unit-Monoidᵉ Mᵉ))

  submonoid-congruence-Monoidᵉ : Submonoidᵉ l2ᵉ Mᵉ
  pr1ᵉ submonoid-congruence-Monoidᵉ = subset-normal-submonoid-congruence-Monoidᵉ
  pr1ᵉ (pr2ᵉ submonoid-congruence-Monoidᵉ) =
    contains-unit-normal-submonoid-congruence-Monoidᵉ
  pr2ᵉ (pr2ᵉ submonoid-congruence-Monoidᵉ) =
    is-closed-under-multiplication-normal-submonoid-congruence-Monoidᵉ

  is-normal-submonoid-congruence-Monoidᵉ :
    is-normal-Submonoidᵉ Mᵉ submonoid-congruence-Monoidᵉ
  pr1ᵉ (is-normal-submonoid-congruence-Monoidᵉ xᵉ yᵉ uᵉ Hᵉ) Kᵉ =
    transitive-congruence-Monoidᵉ Mᵉ Rᵉ
      ( mul-Monoidᵉ Mᵉ xᵉ yᵉ)
      ( mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ xᵉ uᵉ) yᵉ)
      ( unit-Monoidᵉ Mᵉ)
      ( Kᵉ)
      ( symmetric-congruence-Monoidᵉ Mᵉ Rᵉ
        ( mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ xᵉ uᵉ) yᵉ)
        ( mul-Monoidᵉ Mᵉ xᵉ yᵉ)
        ( mul-congruence-Monoidᵉ Mᵉ Rᵉ
          ( concatenate-sim-eq-congruence-Monoidᵉ Mᵉ Rᵉ
            ( mul-congruence-Monoidᵉ Mᵉ Rᵉ (refl-congruence-Monoidᵉ Mᵉ Rᵉ xᵉ) Hᵉ)
            ( right-unit-law-mul-Monoidᵉ Mᵉ xᵉ))
          ( refl-congruence-Monoidᵉ Mᵉ Rᵉ yᵉ)))
  pr2ᵉ (is-normal-submonoid-congruence-Monoidᵉ xᵉ yᵉ uᵉ Hᵉ) Kᵉ =
    transitive-congruence-Monoidᵉ Mᵉ Rᵉ
      ( mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ xᵉ uᵉ) yᵉ)
      ( mul-Monoidᵉ Mᵉ xᵉ yᵉ)
      ( unit-Monoidᵉ Mᵉ)
      ( Kᵉ)
      ( mul-congruence-Monoidᵉ Mᵉ Rᵉ
        ( concatenate-sim-eq-congruence-Monoidᵉ Mᵉ Rᵉ
          ( mul-congruence-Monoidᵉ Mᵉ Rᵉ (refl-congruence-Monoidᵉ Mᵉ Rᵉ xᵉ) Hᵉ)
          ( right-unit-law-mul-Monoidᵉ Mᵉ xᵉ))
        ( refl-congruence-Monoidᵉ Mᵉ Rᵉ yᵉ))

  normal-submonoid-congruence-Monoidᵉ : Normal-Submonoidᵉ l2ᵉ Mᵉ
  pr1ᵉ normal-submonoid-congruence-Monoidᵉ = submonoid-congruence-Monoidᵉ
  pr2ᵉ normal-submonoid-congruence-Monoidᵉ = is-normal-submonoid-congruence-Monoidᵉ
```

### The normal submonoid obtained from the congruence relation of a normal submonoid has the same elements as the original normal submonoid

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Normal-Submonoidᵉ l2ᵉ Mᵉ)
  where

  has-same-elements-normal-submonoid-congruence-Normal-Submonoidᵉ :
    has-same-elements-Normal-Submonoidᵉ Mᵉ
      ( normal-submonoid-congruence-Monoidᵉ Mᵉ
        ( congruence-Normal-Submonoidᵉ Mᵉ Nᵉ))
      ( Nᵉ)
  pr1ᵉ (has-same-elements-normal-submonoid-congruence-Normal-Submonoidᵉ xᵉ) Hᵉ =
    is-closed-under-eq-Normal-Submonoidᵉ Mᵉ Nᵉ
      ( backward-implicationᵉ
        ( Hᵉ (unit-Monoidᵉ Mᵉ) (unit-Monoidᵉ Mᵉ))
        ( is-closed-under-eq-Normal-Submonoid'ᵉ Mᵉ Nᵉ
          ( contains-unit-Normal-Submonoidᵉ Mᵉ Nᵉ)
          ( ( right-unit-law-mul-Monoidᵉ Mᵉ
              ( mul-Monoidᵉ Mᵉ (unit-Monoidᵉ Mᵉ) (unit-Monoidᵉ Mᵉ))) ∙ᵉ
            ( left-unit-law-mul-Monoidᵉ Mᵉ (unit-Monoidᵉ Mᵉ)))))
      ( right-unit-law-mul-Monoidᵉ Mᵉ _ ∙ᵉ left-unit-law-mul-Monoidᵉ Mᵉ _)
  pr1ᵉ
    ( pr2ᵉ
      ( has-same-elements-normal-submonoid-congruence-Normal-Submonoidᵉ xᵉ)
      ( Hᵉ)
      ( uᵉ)
      ( vᵉ))
    ( Kᵉ) =
    is-closed-under-eq-Normal-Submonoid'ᵉ Mᵉ Nᵉ
      ( forward-implicationᵉ (is-normal-Normal-Submonoidᵉ Mᵉ Nᵉ uᵉ vᵉ xᵉ Hᵉ) Kᵉ)
      ( apᵉ (mul-Monoid'ᵉ Mᵉ vᵉ) (right-unit-law-mul-Monoidᵉ Mᵉ uᵉ))
  pr2ᵉ
    ( pr2ᵉ
      ( has-same-elements-normal-submonoid-congruence-Normal-Submonoidᵉ xᵉ)
      ( Hᵉ)
      ( uᵉ)
      ( vᵉ))
    ( Kᵉ) =
    backward-implicationᵉ
      ( is-normal-Normal-Submonoidᵉ Mᵉ Nᵉ uᵉ vᵉ xᵉ Hᵉ)
      ( is-closed-under-eq-Normal-Submonoidᵉ Mᵉ Nᵉ Kᵉ
        ( apᵉ (mul-Monoid'ᵉ Mᵉ vᵉ) (right-unit-law-mul-Monoidᵉ Mᵉ uᵉ)))
```

### The congruence relation of a normal submonoid is saturated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Normal-Submonoidᵉ l2ᵉ Mᵉ)
  where

  is-saturated-congruence-Normal-Submonoidᵉ :
    is-saturated-congruence-Monoidᵉ Mᵉ (congruence-Normal-Submonoidᵉ Mᵉ Nᵉ)
  is-saturated-congruence-Normal-Submonoidᵉ xᵉ yᵉ Hᵉ uᵉ vᵉ =
    ( ( has-same-elements-normal-submonoid-congruence-Normal-Submonoidᵉ Mᵉ Nᵉ
        ( mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ yᵉ) vᵉ)) ∘iffᵉ
      ( Hᵉ uᵉ vᵉ)) ∘iffᵉ
    ( inv-iffᵉ
      ( has-same-elements-normal-submonoid-congruence-Normal-Submonoidᵉ Mᵉ Nᵉ
        ( mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ xᵉ) vᵉ)))

  saturated-congruence-Normal-Submonoidᵉ :
    saturated-congruence-Monoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ
  pr1ᵉ saturated-congruence-Normal-Submonoidᵉ = congruence-Normal-Submonoidᵉ Mᵉ Nᵉ
  pr2ᵉ saturated-congruence-Normal-Submonoidᵉ =
    is-saturated-congruence-Normal-Submonoidᵉ
```

### The congruence relation of the normal submonoid associated to a congruence relation relates the same elements as the original congruence relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ : saturated-congruence-Monoidᵉ l2ᵉ Mᵉ)
  where

  normal-submonoid-saturated-congruence-Monoidᵉ :
    Normal-Submonoidᵉ l2ᵉ Mᵉ
  normal-submonoid-saturated-congruence-Monoidᵉ =
    normal-submonoid-congruence-Monoidᵉ Mᵉ
      ( congruence-saturated-congruence-Monoidᵉ Mᵉ Rᵉ)

  relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoidᵉ :
    relate-same-elements-saturated-congruence-Monoidᵉ Mᵉ
      ( saturated-congruence-Normal-Submonoidᵉ Mᵉ
        ( normal-submonoid-saturated-congruence-Monoidᵉ))
      ( Rᵉ)
  pr1ᵉ
    ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoidᵉ
      xᵉ yᵉ)
    Hᵉ =
    is-saturated-saturated-congruence-Monoidᵉ Mᵉ Rᵉ xᵉ yᵉ Hᵉ
  pr1ᵉ
    ( pr2ᵉ
      ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoidᵉ
        xᵉ yᵉ)
      Hᵉ uᵉ vᵉ) Kᵉ =
    transitive-saturated-congruence-Monoidᵉ Mᵉ Rᵉ
      ( mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ yᵉ) vᵉ)
      ( mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ xᵉ) vᵉ)
      ( unit-Monoidᵉ Mᵉ)
      ( Kᵉ)
      ( mul-saturated-congruence-Monoidᵉ Mᵉ Rᵉ
        ( mul-saturated-congruence-Monoidᵉ Mᵉ Rᵉ
          ( refl-saturated-congruence-Monoidᵉ Mᵉ Rᵉ uᵉ)
          ( symmetric-saturated-congruence-Monoidᵉ Mᵉ Rᵉ xᵉ yᵉ Hᵉ))
        ( refl-saturated-congruence-Monoidᵉ Mᵉ Rᵉ vᵉ))
  pr2ᵉ
    ( pr2ᵉ
      ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoidᵉ
        xᵉ yᵉ)
      Hᵉ uᵉ vᵉ) Kᵉ =
    transitive-saturated-congruence-Monoidᵉ Mᵉ Rᵉ
      ( mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ xᵉ) vᵉ)
      ( mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ yᵉ) vᵉ)
      ( unit-Monoidᵉ Mᵉ)
      ( Kᵉ)
      ( mul-saturated-congruence-Monoidᵉ Mᵉ Rᵉ
        ( mul-saturated-congruence-Monoidᵉ Mᵉ Rᵉ
          ( refl-saturated-congruence-Monoidᵉ Mᵉ Rᵉ uᵉ)
          ( Hᵉ))
        ( refl-saturated-congruence-Monoidᵉ Mᵉ Rᵉ vᵉ))
```

### The type of normal submonoids of `M` is a retract of the type of congruence relations of `M`

```agda
is-section-congruence-Normal-Submonoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Normal-Submonoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ) →
  ( normal-submonoid-congruence-Monoidᵉ Mᵉ (congruence-Normal-Submonoidᵉ Mᵉ Nᵉ)) ＝ᵉ
  ( Nᵉ)
is-section-congruence-Normal-Submonoidᵉ l2ᵉ Mᵉ Nᵉ =
  eq-has-same-elements-Normal-Submonoidᵉ Mᵉ
    ( normal-submonoid-congruence-Monoidᵉ Mᵉ (congruence-Normal-Submonoidᵉ Mᵉ Nᵉ))
    ( Nᵉ)
    ( has-same-elements-normal-submonoid-congruence-Normal-Submonoidᵉ Mᵉ Nᵉ)

normal-submonoid-retract-of-congruence-Monoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Monoidᵉ l1ᵉ) →
  (Normal-Submonoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ) retract-ofᵉ (congruence-Monoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ)
pr1ᵉ (normal-submonoid-retract-of-congruence-Monoidᵉ l2ᵉ Mᵉ) =
  congruence-Normal-Submonoidᵉ Mᵉ
pr1ᵉ (pr2ᵉ (normal-submonoid-retract-of-congruence-Monoidᵉ l2ᵉ Mᵉ)) =
  normal-submonoid-congruence-Monoidᵉ Mᵉ
pr2ᵉ (pr2ᵉ (normal-submonoid-retract-of-congruence-Monoidᵉ l2ᵉ Mᵉ)) =
  is-section-congruence-Normal-Submonoidᵉ l2ᵉ Mᵉ
```

### The type of normal submonoids of `M` is equivalent to the type of saturated congruence relations on `M`

```agda
is-section-saturated-congruence-Normal-Submonoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Normal-Submonoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ) →
  ( normal-submonoid-saturated-congruence-Monoidᵉ Mᵉ
    ( saturated-congruence-Normal-Submonoidᵉ Mᵉ Nᵉ)) ＝ᵉ
  ( Nᵉ)
is-section-saturated-congruence-Normal-Submonoidᵉ l2ᵉ Mᵉ Nᵉ =
  eq-has-same-elements-Normal-Submonoidᵉ Mᵉ
    ( normal-submonoid-saturated-congruence-Monoidᵉ Mᵉ
      ( saturated-congruence-Normal-Submonoidᵉ Mᵉ Nᵉ))
    ( Nᵉ)
    ( has-same-elements-normal-submonoid-congruence-Normal-Submonoidᵉ Mᵉ Nᵉ)

is-retraction-saturated-congruence-Normal-Submonoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Monoidᵉ l1ᵉ)
  (Rᵉ : saturated-congruence-Monoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ) →
  ( saturated-congruence-Normal-Submonoidᵉ Mᵉ
    ( normal-submonoid-saturated-congruence-Monoidᵉ Mᵉ Rᵉ)) ＝ᵉ
  ( Rᵉ)
is-retraction-saturated-congruence-Normal-Submonoidᵉ l2ᵉ Mᵉ Rᵉ =
  eq-relate-same-elements-saturated-congruence-Monoidᵉ Mᵉ
    ( saturated-congruence-Normal-Submonoidᵉ Mᵉ
      ( normal-submonoid-saturated-congruence-Monoidᵉ Mᵉ Rᵉ))
    ( Rᵉ)
    ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoidᵉ
      ( Mᵉ)
      ( Rᵉ))

is-equiv-normal-submonoid-saturated-congruence-Monoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Monoidᵉ l1ᵉ) →
  is-equivᵉ (normal-submonoid-saturated-congruence-Monoidᵉ {l2ᵉ = l1ᵉ ⊔ l2ᵉ} Mᵉ)
is-equiv-normal-submonoid-saturated-congruence-Monoidᵉ l2ᵉ Mᵉ =
  is-equiv-is-invertibleᵉ
    ( saturated-congruence-Normal-Submonoidᵉ Mᵉ)
    ( is-section-saturated-congruence-Normal-Submonoidᵉ l2ᵉ Mᵉ)
    ( is-retraction-saturated-congruence-Normal-Submonoidᵉ l2ᵉ Mᵉ)

equiv-normal-submonoid-saturated-congruence-Monoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Monoidᵉ l1ᵉ) →
  saturated-congruence-Monoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ ≃ᵉ Normal-Submonoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ
pr1ᵉ (equiv-normal-submonoid-saturated-congruence-Monoidᵉ l2ᵉ Mᵉ) =
  normal-submonoid-saturated-congruence-Monoidᵉ Mᵉ
pr2ᵉ (equiv-normal-submonoid-saturated-congruence-Monoidᵉ l2ᵉ Mᵉ) =
  is-equiv-normal-submonoid-saturated-congruence-Monoidᵉ l2ᵉ Mᵉ
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ MP87ᵉ}}