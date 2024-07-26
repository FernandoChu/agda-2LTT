# Planar binary trees

```agda
module trees.planar-binary-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleansᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.universe-levelsᵉ

open import trees.w-typesᵉ
```

</details>

## Idea

Aᵉ planarᵉ binaryᵉ treeᵉ isᵉ aᵉ binaryᵉ treeᵉ in whichᵉ theᵉ branchingsᵉ areᵉ labeledᵉ byᵉ theᵉ
booleans.ᵉ Theᵉ ideaᵉ isᵉ thatᵉ atᵉ anyᵉ branchingᵉ pointᵉ in aᵉ planarᵉ binaryᵉ tree,ᵉ weᵉ
knowᵉ whichᵉ branchᵉ goesᵉ to theᵉ leftᵉ andᵉ whichᵉ branchᵉ goesᵉ to theᵉ right.ᵉ

Planarᵉ binaryᵉ treesᵉ areᵉ commonlyᵉ calledᵉ binaryᵉ trees,ᵉ butᵉ in univalentᵉ
mathematicsᵉ itᵉ makesᵉ senseᵉ to recognizeᵉ thatᵉ theᵉ branchingᵉ pointsᵉ in aᵉ binaryᵉ
treeᵉ shouldᵉ notᵉ record whichᵉ branchᵉ goesᵉ leftᵉ andᵉ whichᵉ branchᵉ goesᵉ right.ᵉ

## Definitions

### The inductive definition of the type of planar binary trees

```agda
data Planar-Bin-Treeᵉ : UUᵉ lzero where
  root-PBTᵉ : Planar-Bin-Treeᵉ
  join-PBTᵉ : (xᵉ yᵉ : Planar-Bin-Treeᵉ) → Planar-Bin-Treeᵉ
```

### The definition of the type of planar binary trees as a W-type

```agda
PBT-𝕎ᵉ : UUᵉ lzero
PBT-𝕎ᵉ = 𝕎ᵉ boolᵉ Pᵉ
  where
  Pᵉ : boolᵉ → UUᵉ lzero
  Pᵉ trueᵉ = boolᵉ
  Pᵉ falseᵉ = emptyᵉ

root-PBT-𝕎ᵉ : PBT-𝕎ᵉ
root-PBT-𝕎ᵉ = constant-𝕎ᵉ falseᵉ idᵉ

join-PBT-𝕎ᵉ : (xᵉ yᵉ : PBT-𝕎ᵉ) → PBT-𝕎ᵉ
join-PBT-𝕎ᵉ xᵉ yᵉ = tree-𝕎ᵉ trueᵉ αᵉ
  where
  αᵉ : boolᵉ → PBT-𝕎ᵉ
  αᵉ trueᵉ = xᵉ
  αᵉ falseᵉ = yᵉ
```