# Coslice precategories

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="category-theory.coslice-precategories%25E1%25B5%2589.html" class="Module">category-theory.coslice-precategoriesᵉ</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="category-theory.functors-precategories%25E1%25B5%2589.html" class="Module">category-theory.functors-precategoriesᵉ</a>
<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="category-theory.opposite-precategories%25E1%25B5%2589.html" class="Module">category-theory.opposite-precategoriesᵉ</a>
<a id="240" class="Keyword">open</a> <a id="245" class="Keyword">import</a> <a id="252" href="category-theory.precategories%25E1%25B5%2589.html" class="Module">category-theory.precategoriesᵉ</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="category-theory.slice-precategories%25E1%25B5%2589.html" class="Module">category-theory.slice-precategoriesᵉ</a>

<a id="333" class="Keyword">open</a> <a id="338" class="Keyword">import</a> <a id="345" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

The {{#concept "coslice precategory" Agda=Coslice-Precategory}} of a
[precategory](category-theory.precategories.md) `C` under an object `X` of `C`
is the category of objects of `C` equipped with a morphism from `X`.

Equivalently, it is the opposite of the slice precategory of `Cᵒᵖ`.

## Definitions

<pre class="Agda"><a id="710" class="Keyword">module</a> <a id="717" href="category-theory.coslice-precategories%25E1%25B5%2589.html#717" class="Module">_</a>
  <a id="721" class="Symbol">{</a><a id="722" href="category-theory.coslice-precategories%25E1%25B5%2589.html#722" class="Bound">l1ᵉ</a> <a id="726" href="category-theory.coslice-precategories%25E1%25B5%2589.html#726" class="Bound">l2ᵉ</a> <a id="730" class="Symbol">:</a> <a id="732" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="737" class="Symbol">}</a> <a id="739" class="Symbol">(</a><a id="740" href="category-theory.coslice-precategories%25E1%25B5%2589.html#740" class="Bound">Cᵉ</a> <a id="743" class="Symbol">:</a> <a id="745" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="758" href="category-theory.coslice-precategories%25E1%25B5%2589.html#722" class="Bound">l1ᵉ</a> <a id="762" href="category-theory.coslice-precategories%25E1%25B5%2589.html#726" class="Bound">l2ᵉ</a><a id="765" class="Symbol">)</a> <a id="767" class="Symbol">(</a><a id="768" href="category-theory.coslice-precategories%25E1%25B5%2589.html#768" class="Bound">Xᵉ</a> <a id="771" class="Symbol">:</a> <a id="773" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="790" href="category-theory.coslice-precategories%25E1%25B5%2589.html#740" class="Bound">Cᵉ</a><a id="792" class="Symbol">)</a>
  <a id="796" class="Keyword">where</a>

  <a id="805" href="category-theory.coslice-precategories%25E1%25B5%2589.html#805" class="Function">Coslice-Precategoryᵉ</a> <a id="826" class="Symbol">:</a> <a id="828" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="841" class="Symbol">(</a><a id="842" href="category-theory.coslice-precategories%25E1%25B5%2589.html#722" class="Bound">l1ᵉ</a> <a id="846" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="848" href="category-theory.coslice-precategories%25E1%25B5%2589.html#726" class="Bound">l2ᵉ</a><a id="851" class="Symbol">)</a> <a id="853" href="category-theory.coslice-precategories%25E1%25B5%2589.html#726" class="Bound">l2ᵉ</a>
  <a id="859" href="category-theory.coslice-precategories%25E1%25B5%2589.html#805" class="Function">Coslice-Precategoryᵉ</a> <a id="880" class="Symbol">=</a>
    <a id="886" href="category-theory.opposite-precategories%25E1%25B5%2589.html#3357" class="Function">opposite-Precategoryᵉ</a> <a id="908" class="Symbol">(</a><a id="909" href="category-theory.slice-precategories%25E1%25B5%2589.html#6536" class="Function">Slice-Precategoryᵉ</a> <a id="928" class="Symbol">(</a><a id="929" href="category-theory.opposite-precategories%25E1%25B5%2589.html#3357" class="Function">opposite-Precategoryᵉ</a> <a id="951" href="category-theory.coslice-precategories%25E1%25B5%2589.html#740" class="Bound">Cᵉ</a><a id="953" class="Symbol">)</a> <a id="955" href="category-theory.coslice-precategories%25E1%25B5%2589.html#768" class="Bound">Xᵉ</a><a id="957" class="Symbol">)</a>
</pre>
## Properties

### The coslice precategory has a forgetful functor

<pre class="Agda"><a id="1040" class="Keyword">module</a> <a id="1047" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1047" class="Module">_</a>
  <a id="1051" class="Symbol">{</a><a id="1052" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1052" class="Bound">l1ᵉ</a> <a id="1056" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1056" class="Bound">l2ᵉ</a> <a id="1060" class="Symbol">:</a> <a id="1062" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1067" class="Symbol">}</a> <a id="1069" class="Symbol">(</a><a id="1070" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1070" class="Bound">Cᵉ</a> <a id="1073" class="Symbol">:</a> <a id="1075" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="1088" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1052" class="Bound">l1ᵉ</a> <a id="1092" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1056" class="Bound">l2ᵉ</a><a id="1095" class="Symbol">)</a> <a id="1097" class="Symbol">(</a><a id="1098" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1098" class="Bound">Xᵉ</a> <a id="1101" class="Symbol">:</a> <a id="1103" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="1120" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1070" class="Bound">Cᵉ</a><a id="1122" class="Symbol">)</a>
  <a id="1126" class="Keyword">where</a>

  <a id="1135" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1135" class="Function">forgetful-functor-Coslice-Precategoryᵉ</a> <a id="1174" class="Symbol">:</a>
    <a id="1180" href="category-theory.functors-precategories%25E1%25B5%2589.html#3980" class="Function">functor-Precategoryᵉ</a> <a id="1201" class="Symbol">(</a><a id="1202" href="category-theory.coslice-precategories%25E1%25B5%2589.html#805" class="Function">Coslice-Precategoryᵉ</a> <a id="1223" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1070" class="Bound">Cᵉ</a> <a id="1226" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1098" class="Bound">Xᵉ</a><a id="1228" class="Symbol">)</a> <a id="1230" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1070" class="Bound">Cᵉ</a>
  <a id="1235" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1135" class="Function">forgetful-functor-Coslice-Precategoryᵉ</a> <a id="1274" class="Symbol">=</a>
    <a id="1280" href="category-theory.functors-precategories%25E1%25B5%2589.html#15743" class="Function">opposite-functor-Precategoryᵉ</a>
      <a id="1316" class="Symbol">(</a> <a id="1318" href="category-theory.slice-precategories%25E1%25B5%2589.html#6536" class="Function">Slice-Precategoryᵉ</a> <a id="1337" class="Symbol">(</a><a id="1338" href="category-theory.opposite-precategories%25E1%25B5%2589.html#3357" class="Function">opposite-Precategoryᵉ</a> <a id="1360" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1070" class="Bound">Cᵉ</a><a id="1362" class="Symbol">)</a> <a id="1364" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1098" class="Bound">Xᵉ</a><a id="1366" class="Symbol">)</a>
      <a id="1374" class="Symbol">(</a> <a id="1376" href="category-theory.opposite-precategories%25E1%25B5%2589.html#3357" class="Function">opposite-Precategoryᵉ</a> <a id="1398" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1070" class="Bound">Cᵉ</a><a id="1400" class="Symbol">)</a>
      <a id="1408" class="Symbol">(</a> <a id="1410" href="category-theory.slice-precategories%25E1%25B5%2589.html#17565" class="Function">forgetful-functor-Slice-Precategoryᵉ</a> <a id="1447" class="Symbol">(</a><a id="1448" href="category-theory.opposite-precategories%25E1%25B5%2589.html#3357" class="Function">opposite-Precategoryᵉ</a> <a id="1470" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1070" class="Bound">Cᵉ</a><a id="1472" class="Symbol">)</a> <a id="1474" href="category-theory.coslice-precategories%25E1%25B5%2589.html#1098" class="Bound">Xᵉ</a><a id="1476" class="Symbol">)</a>
</pre>