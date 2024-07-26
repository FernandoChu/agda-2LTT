# Equivalences of cospans

```agda
module foundation.equivalences-cospansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cospansᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.morphisms-cospansᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Anᵉ {{#conceptᵉ "equivalenceᵉ ofᵉ cospans"ᵉ Agda=equiv-cospanᵉ}} fromᵉ
[cospans](foundation.cospans.mdᵉ) `(Xᵉ ,ᵉ fᵉ ,ᵉ g)`ᵉ to `(Yᵉ ,ᵉ hᵉ ,ᵉ k)`ᵉ betweenᵉ typesᵉ
`A`ᵉ andᵉ `B`ᵉ consistsᵉ ofᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ)
`eᵉ : Xᵉ ≃ᵉ Y`ᵉ suchᵉ thatᵉ theᵉ trianglesᵉ

```text
      eᵉ              eᵉ
  Xᵉ ---->ᵉ Yᵉ      Xᵉ ---->ᵉ Yᵉ
   \ᵉ     /ᵉ        \ᵉ     /ᵉ
  fᵉ \ᵉ   /ᵉ hᵉ      gᵉ \ᵉ   /ᵉ kᵉ
     ∨ᵉ ∨ᵉ            ∨ᵉ ∨ᵉ
      Aᵉ              Bᵉ
```

bothᵉ [commute](foundation.commuting-triangles-of-maps.md).ᵉ

## Definitions

### Equivalences of cospans

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  equiv-cospanᵉ : cospanᵉ l3ᵉ Aᵉ Bᵉ → cospanᵉ l4ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  equiv-cospanᵉ cᵉ dᵉ =
    Σᵉ ( codomain-cospanᵉ cᵉ ≃ᵉ codomain-cospanᵉ dᵉ)
      ( λ eᵉ → coherence-hom-cospanᵉ cᵉ dᵉ (map-equivᵉ eᵉ))
```

### The identity equivalence of cospans

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  id-equiv-cospanᵉ : (cᵉ : cospanᵉ l3ᵉ Aᵉ Bᵉ) → equiv-cospanᵉ cᵉ cᵉ
  pr1ᵉ (id-equiv-cospanᵉ cᵉ) = id-equivᵉ
  pr1ᵉ (pr2ᵉ (id-equiv-cospanᵉ cᵉ)) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (id-equiv-cospanᵉ cᵉ)) = refl-htpyᵉ
```

## Properties

### Characterizing equality of cospans

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  equiv-eq-cospanᵉ : (cᵉ dᵉ : cospanᵉ l3ᵉ Aᵉ Bᵉ) → cᵉ ＝ᵉ dᵉ → equiv-cospanᵉ cᵉ dᵉ
  equiv-eq-cospanᵉ cᵉ .cᵉ reflᵉ = id-equiv-cospanᵉ cᵉ

  is-torsorial-equiv-cospanᵉ :
    (cᵉ : cospanᵉ l3ᵉ Aᵉ Bᵉ) → is-torsorialᵉ (equiv-cospanᵉ cᵉ)
  is-torsorial-equiv-cospanᵉ cᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (pr1ᵉ cᵉ))
      ( codomain-cospanᵉ cᵉ ,ᵉ id-equivᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpy'ᵉ (left-map-cospanᵉ cᵉ))
        ( left-map-cospanᵉ cᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-htpy'ᵉ (right-map-cospanᵉ cᵉ)))

  is-equiv-equiv-eq-cospanᵉ :
    (cᵉ dᵉ : cospanᵉ l3ᵉ Aᵉ Bᵉ) → is-equivᵉ (equiv-eq-cospanᵉ cᵉ dᵉ)
  is-equiv-equiv-eq-cospanᵉ cᵉ =
    fundamental-theorem-idᵉ (is-torsorial-equiv-cospanᵉ cᵉ) (equiv-eq-cospanᵉ cᵉ)

  extensionality-cospanᵉ :
    (cᵉ dᵉ : cospanᵉ l3ᵉ Aᵉ Bᵉ) → (cᵉ ＝ᵉ dᵉ) ≃ᵉ (equiv-cospanᵉ cᵉ dᵉ)
  pr1ᵉ (extensionality-cospanᵉ cᵉ dᵉ) = equiv-eq-cospanᵉ cᵉ dᵉ
  pr2ᵉ (extensionality-cospanᵉ cᵉ dᵉ) = is-equiv-equiv-eq-cospanᵉ cᵉ dᵉ

  eq-equiv-cospanᵉ : (cᵉ dᵉ : cospanᵉ l3ᵉ Aᵉ Bᵉ) → equiv-cospanᵉ cᵉ dᵉ → cᵉ ＝ᵉ dᵉ
  eq-equiv-cospanᵉ cᵉ dᵉ = map-inv-equivᵉ (extensionality-cospanᵉ cᵉ dᵉ)
```