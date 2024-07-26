# Full binary trees

```agda
module trees.full-binary-treesᵉ where
```

<details><sumary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.empty-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "fullᵉ binaryᵉ tree"ᵉ Agda=full-binary-treeᵉ WD="fullᵉ binaryᵉ tree"ᵉ WDID=Q29791667ᵉ}}
isᵉ aᵉ finiteᵉ [directedᵉ tree](trees.directed-trees.mdᵉ) in whichᵉ everyᵉ non-leafᵉ
nodeᵉ hasᵉ aᵉ specifiedᵉ leftᵉ branchᵉ andᵉ aᵉ specifiedᵉ rightᵉ branch.ᵉ Moreᵉ precisely,ᵉ aᵉ
fullᵉ binaryᵉ treeᵉ consistsᵉ ofᵉ aᵉ root,ᵉ aᵉ leftᵉ fullᵉ binaryᵉ subtreeᵉ andᵉ aᵉ rightᵉ fullᵉ
binaryᵉ subtree.ᵉ

## Definitions

### Full binary trees

```agda
data full-binary-treeᵉ : UUᵉ lzero where
  leaf-full-binary-treeᵉ : full-binary-treeᵉ
  join-full-binary-treeᵉ : (sᵉ tᵉ : full-binary-treeᵉ) → full-binary-treeᵉ
```