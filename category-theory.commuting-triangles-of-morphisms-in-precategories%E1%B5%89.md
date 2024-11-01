# Commuting triangles of morphisms in precategories

<pre class="Agda"><a id="62" class="Keyword">module</a> <a id="69" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html" class="Module">category-theory.commuting-triangles-of-morphisms-in-precategoriesᵉ</a> <a id="136" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html" class="Module">category-theory.commuting-triangles-of-morphisms-in-set-magmoidsᵉ</a>
<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="category-theory.precategories%25E1%25B5%2589.html" class="Module">category-theory.precategoriesᵉ</a>

<a id="314" class="Keyword">open</a> <a id="319" class="Keyword">import</a> <a id="326" href="foundation.identity-types%25E1%25B5%2589.html" class="Module">foundation.identity-typesᵉ</a>
<a id="353" class="Keyword">open</a> <a id="358" class="Keyword">import</a> <a id="365" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

A triangle of morphisms

```text
        top
     x ----> y
      \     /
  left \   / right
        ∨ ∨
         z
```

in a [precategory](category-theory.precategories.md) `C` is said to **commute**
if there is an [identification](foundation-core.identity-types.md) between:

```text
  left ＝ right ∘ top.
```

Such a identification is called the
{{#concept "coherence" Disambiguation="commuting triangle of morphisms in precategories" Agda=coherence-triangle-hom-Precategory}}
of the commuting triangle.

## Definitions

<pre class="Agda"><a id="coherence-triangle-hom-Precategoryᵉ"></a><a id="951" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#951" class="Function">coherence-triangle-hom-Precategoryᵉ</a> <a id="987" class="Symbol">:</a>
  <a id="991" class="Symbol">{</a><a id="992" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#992" class="Bound">l1ᵉ</a> <a id="996" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#996" class="Bound">l2ᵉ</a> <a id="1000" class="Symbol">:</a> <a id="1002" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1007" class="Symbol">}</a> <a id="1009" class="Symbol">(</a><a id="1010" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1010" class="Bound">Cᵉ</a> <a id="1013" class="Symbol">:</a> <a id="1015" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="1028" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#992" class="Bound">l1ᵉ</a> <a id="1032" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#996" class="Bound">l2ᵉ</a><a id="1035" class="Symbol">)</a>
  <a id="1039" class="Symbol">{</a><a id="1040" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1040" class="Bound">xᵉ</a> <a id="1043" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1043" class="Bound">yᵉ</a> <a id="1046" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1046" class="Bound">zᵉ</a> <a id="1049" class="Symbol">:</a> <a id="1051" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="1068" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1010" class="Bound">Cᵉ</a><a id="1070" class="Symbol">}</a>
  <a id="1074" class="Symbol">(</a><a id="1075" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1075" class="Bound">topᵉ</a> <a id="1080" class="Symbol">:</a> <a id="1082" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="1099" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1010" class="Bound">Cᵉ</a> <a id="1102" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1040" class="Bound">xᵉ</a> <a id="1105" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1043" class="Bound">yᵉ</a><a id="1107" class="Symbol">)</a>
  <a id="1111" class="Symbol">(</a><a id="1112" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1112" class="Bound">leftᵉ</a> <a id="1118" class="Symbol">:</a> <a id="1120" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="1137" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1010" class="Bound">Cᵉ</a> <a id="1140" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1040" class="Bound">xᵉ</a> <a id="1143" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1046" class="Bound">zᵉ</a><a id="1145" class="Symbol">)</a>
  <a id="1149" class="Symbol">(</a><a id="1150" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1150" class="Bound">rightᵉ</a> <a id="1157" class="Symbol">:</a> <a id="1159" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="1176" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1010" class="Bound">Cᵉ</a> <a id="1179" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1043" class="Bound">yᵉ</a> <a id="1182" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1046" class="Bound">zᵉ</a><a id="1184" class="Symbol">)</a> <a id="1186" class="Symbol">→</a>
  <a id="1190" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1194" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#996" class="Bound">l2ᵉ</a>
<a id="1198" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#951" class="Function">coherence-triangle-hom-Precategoryᵉ</a> <a id="1234" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1234" class="Bound">Cᵉ</a> <a id="1237" class="Symbol">=</a>
  <a id="1241" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#869" class="Function">coherence-triangle-hom-Set-Magmoidᵉ</a> <a id="1277" class="Symbol">(</a><a id="1278" href="category-theory.precategories%25E1%25B5%2589.html#8559" class="Function">set-magmoid-Precategoryᵉ</a> <a id="1303" href="category-theory.commuting-triangles-of-morphisms-in-precategories%25E1%25B5%2589.html#1234" class="Bound">Cᵉ</a><a id="1305" class="Symbol">)</a>
</pre>