# Suspensions of pointed types

```agda
module synthetic-homotopy-theory.suspensions-of-pointed-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.loop-spacesᵉ
open import synthetic-homotopy-theory.suspension-structuresᵉ
open import synthetic-homotopy-theory.suspensions-of-typesᵉ
```

</details>

## Idea

Whenᵉ `X`ᵉ isᵉ aᵉ pointedᵉ type,ᵉ theᵉ suspensionᵉ ofᵉ `X`ᵉ hasᵉ niceᵉ propertiesᵉ

### The suspension of a pointed type

```agda
suspension-Pointed-Typeᵉ :
  {lᵉ : Level} → Pointed-Typeᵉ lᵉ → Pointed-Typeᵉ lᵉ
pr1ᵉ (suspension-Pointed-Typeᵉ Xᵉ) = suspensionᵉ (type-Pointed-Typeᵉ Xᵉ)
pr2ᵉ (suspension-Pointed-Typeᵉ Xᵉ) = north-suspensionᵉ
```

#### Suspension structure induced by a pointed type

```agda
constant-suspension-structure-Pointed-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : Pointed-Typeᵉ l2ᵉ) →
  suspension-structureᵉ Xᵉ (type-Pointed-Typeᵉ Yᵉ)
pr1ᵉ (constant-suspension-structure-Pointed-Typeᵉ Xᵉ Yᵉ) =
  point-Pointed-Typeᵉ Yᵉ
pr1ᵉ (pr2ᵉ (constant-suspension-structure-Pointed-Typeᵉ Xᵉ Yᵉ)) =
  point-Pointed-Typeᵉ Yᵉ
pr2ᵉ (pr2ᵉ (constant-suspension-structure-Pointed-Typeᵉ Xᵉ Yᵉ)) =
  constᵉ Xᵉ reflᵉ
```

#### Suspension structure induced by a map into a loop space

Theᵉ followingᵉ functionᵉ takesᵉ aᵉ mapᵉ `Xᵉ → Ωᵉ Y`ᵉ andᵉ returnsᵉ aᵉ suspensionᵉ structureᵉ
onᵉ `Y`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : Pointed-Typeᵉ l2ᵉ)
  where
  suspension-structure-map-into-Ωᵉ :
    (Xᵉ → type-Ωᵉ Yᵉ) → suspension-structureᵉ Xᵉ (type-Pointed-Typeᵉ Yᵉ)
  pr1ᵉ (suspension-structure-map-into-Ωᵉ fᵉ) = point-Pointed-Typeᵉ Yᵉ
  pr1ᵉ (pr2ᵉ (suspension-structure-map-into-Ωᵉ fᵉ)) = point-Pointed-Typeᵉ Yᵉ
  pr2ᵉ (pr2ᵉ (suspension-structure-map-into-Ωᵉ fᵉ)) = fᵉ
```