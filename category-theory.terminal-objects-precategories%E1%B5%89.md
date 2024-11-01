# Terminal objects in a precategory

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html" class="Module">category-theory.terminal-objects-precategoriesᵉ</a> <a id="101" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="157" class="Keyword">open</a> <a id="162" class="Keyword">import</a> <a id="169" href="category-theory.precategories%25E1%25B5%2589.html" class="Module">category-theory.precategoriesᵉ</a>

<a id="201" class="Keyword">open</a> <a id="206" class="Keyword">import</a> <a id="213" href="foundation.contractible-types%25E1%25B5%2589.html" class="Module">foundation.contractible-typesᵉ</a>
<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="289" class="Keyword">open</a> <a id="294" class="Keyword">import</a> <a id="301" href="foundation.function-types%25E1%25B5%2589.html" class="Module">foundation.function-typesᵉ</a>
<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="foundation.identity-types%25E1%25B5%2589.html" class="Module">foundation.identity-typesᵉ</a>
<a id="367" class="Keyword">open</a> <a id="372" class="Keyword">import</a> <a id="379" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

The **terminal object** of a [precategory](category-theory.precategories.md), if
it exists, is an object with the universal property that there is a
[unique](foundation-core.contractible-types.md) morphism into it from any
object.

## Definition

### The universal property of a terminal object in a precategory

<pre class="Agda"><a id="is-terminal-obj-Precategoryᵉ"></a><a id="754" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#754" class="Function">is-terminal-obj-Precategoryᵉ</a> <a id="783" class="Symbol">:</a>
  <a id="787" class="Symbol">{</a><a id="788" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#788" class="Bound">l1ᵉ</a> <a id="792" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#792" class="Bound">l2ᵉ</a> <a id="796" class="Symbol">:</a> <a id="798" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="803" class="Symbol">}</a> <a id="805" class="Symbol">(</a><a id="806" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#806" class="Bound">Cᵉ</a> <a id="809" class="Symbol">:</a> <a id="811" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="824" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#788" class="Bound">l1ᵉ</a> <a id="828" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#792" class="Bound">l2ᵉ</a><a id="831" class="Symbol">)</a> <a id="833" class="Symbol">→</a> <a id="835" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="852" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#806" class="Bound">Cᵉ</a> <a id="855" class="Symbol">→</a> <a id="857" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="861" class="Symbol">(</a><a id="862" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#788" class="Bound">l1ᵉ</a> <a id="866" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="868" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#792" class="Bound">l2ᵉ</a><a id="871" class="Symbol">)</a>
<a id="873" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#754" class="Function">is-terminal-obj-Precategoryᵉ</a> <a id="902" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#902" class="Bound">Cᵉ</a> <a id="905" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#905" class="Bound">xᵉ</a> <a id="908" class="Symbol">=</a>
  <a id="912" class="Symbol">(</a><a id="913" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#913" class="Bound">yᵉ</a> <a id="916" class="Symbol">:</a> <a id="918" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="935" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#902" class="Bound">Cᵉ</a><a id="937" class="Symbol">)</a> <a id="939" class="Symbol">→</a> <a id="941" href="foundation-core.contractible-types%25E1%25B5%2589.html#908" class="Function">is-contrᵉ</a> <a id="951" class="Symbol">(</a><a id="952" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="969" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#902" class="Bound">Cᵉ</a> <a id="972" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#913" class="Bound">yᵉ</a> <a id="975" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#905" class="Bound">xᵉ</a><a id="977" class="Symbol">)</a>

<a id="980" class="Keyword">module</a> <a id="987" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#987" class="Module">_</a>
  <a id="991" class="Symbol">{</a><a id="992" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#992" class="Bound">l1ᵉ</a> <a id="996" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#996" class="Bound">l2ᵉ</a> <a id="1000" class="Symbol">:</a> <a id="1002" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1007" class="Symbol">}</a> <a id="1009" class="Symbol">(</a><a id="1010" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1010" class="Bound">Cᵉ</a> <a id="1013" class="Symbol">:</a> <a id="1015" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="1028" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#992" class="Bound">l1ᵉ</a> <a id="1032" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#996" class="Bound">l2ᵉ</a><a id="1035" class="Symbol">)</a>
  <a id="1039" class="Symbol">(</a><a id="1040" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1040" class="Bound">xᵉ</a> <a id="1043" class="Symbol">:</a> <a id="1045" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="1062" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1010" class="Bound">Cᵉ</a><a id="1064" class="Symbol">)</a>
  <a id="1068" class="Symbol">(</a><a id="1069" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1069" class="Bound">tᵉ</a> <a id="1072" class="Symbol">:</a> <a id="1074" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#754" class="Function">is-terminal-obj-Precategoryᵉ</a> <a id="1103" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1010" class="Bound">Cᵉ</a> <a id="1106" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1040" class="Bound">xᵉ</a><a id="1108" class="Symbol">)</a>
  <a id="1112" class="Keyword">where</a>

  <a id="1121" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1121" class="Function">hom-is-terminal-obj-Precategoryᵉ</a> <a id="1154" class="Symbol">:</a>
    <a id="1160" class="Symbol">(</a><a id="1161" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1161" class="Bound">yᵉ</a> <a id="1164" class="Symbol">:</a> <a id="1166" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="1183" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1010" class="Bound">Cᵉ</a><a id="1185" class="Symbol">)</a> <a id="1187" class="Symbol">→</a>
    <a id="1193" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="1210" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1010" class="Bound">Cᵉ</a> <a id="1213" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1161" class="Bound">yᵉ</a> <a id="1216" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1040" class="Bound">xᵉ</a>
  <a id="1221" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1121" class="Function">hom-is-terminal-obj-Precategoryᵉ</a> <a id="1254" class="Symbol">=</a> <a id="1256" href="foundation-core.contractible-types%25E1%25B5%2589.html#1016" class="Function">centerᵉ</a> <a id="1264" href="foundation-core.function-types%25E1%25B5%2589.html#476" class="Function Operator">∘ᵉ</a> <a id="1267" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1069" class="Bound">tᵉ</a>

  <a id="1273" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1273" class="Function">is-unique-hom-is-terminal-obj-Precategoryᵉ</a> <a id="1316" class="Symbol">:</a>
    <a id="1322" class="Symbol">(</a><a id="1323" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1323" class="Bound">yᵉ</a> <a id="1326" class="Symbol">:</a> <a id="1328" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="1345" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1010" class="Bound">Cᵉ</a><a id="1347" class="Symbol">)</a> <a id="1349" class="Symbol">→</a>
    <a id="1355" class="Symbol">(</a><a id="1356" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1356" class="Bound">fᵉ</a> <a id="1359" class="Symbol">:</a> <a id="1361" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="1378" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1010" class="Bound">Cᵉ</a> <a id="1381" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1323" class="Bound">yᵉ</a> <a id="1384" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1040" class="Bound">xᵉ</a><a id="1386" class="Symbol">)</a> <a id="1388" class="Symbol">→</a>
    <a id="1394" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1121" class="Function">hom-is-terminal-obj-Precategoryᵉ</a> <a id="1427" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1323" class="Bound">yᵉ</a> <a id="1430" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="1433" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1356" class="Bound">fᵉ</a>
  <a id="1438" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1273" class="Function">is-unique-hom-is-terminal-obj-Precategoryᵉ</a> <a id="1481" class="Symbol">=</a> <a id="1483" href="foundation-core.contractible-types%25E1%25B5%2589.html#1413" class="Function">contractionᵉ</a> <a id="1496" href="foundation-core.function-types%25E1%25B5%2589.html#476" class="Function Operator">∘ᵉ</a> <a id="1499" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1069" class="Bound">tᵉ</a>
</pre>
### Terminal objects in precategories

<pre class="Agda"><a id="terminal-obj-Precategoryᵉ"></a><a id="1554" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1554" class="Function">terminal-obj-Precategoryᵉ</a> <a id="1580" class="Symbol">:</a>
  <a id="1584" class="Symbol">{</a><a id="1585" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1585" class="Bound">l1ᵉ</a> <a id="1589" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1589" class="Bound">l2ᵉ</a> <a id="1593" class="Symbol">:</a> <a id="1595" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1600" class="Symbol">}</a> <a id="1602" class="Symbol">(</a><a id="1603" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1603" class="Bound">Cᵉ</a> <a id="1606" class="Symbol">:</a> <a id="1608" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="1621" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1585" class="Bound">l1ᵉ</a> <a id="1625" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1589" class="Bound">l2ᵉ</a><a id="1628" class="Symbol">)</a> <a id="1630" class="Symbol">→</a> <a id="1632" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1636" class="Symbol">(</a><a id="1637" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1585" class="Bound">l1ᵉ</a> <a id="1641" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1643" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1589" class="Bound">l2ᵉ</a><a id="1646" class="Symbol">)</a>
<a id="1648" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1554" class="Function">terminal-obj-Precategoryᵉ</a> <a id="1674" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1674" class="Bound">Cᵉ</a> <a id="1677" class="Symbol">=</a>
  <a id="1681" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="1684" class="Symbol">(</a><a id="1685" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="1702" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1674" class="Bound">Cᵉ</a><a id="1704" class="Symbol">)</a> <a id="1706" class="Symbol">(</a><a id="1707" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#754" class="Function">is-terminal-obj-Precategoryᵉ</a> <a id="1736" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1674" class="Bound">Cᵉ</a><a id="1738" class="Symbol">)</a>

<a id="1741" class="Keyword">module</a> <a id="1748" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1748" class="Module">_</a>
  <a id="1752" class="Symbol">{</a><a id="1753" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1753" class="Bound">l1ᵉ</a> <a id="1757" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1757" class="Bound">l2ᵉ</a> <a id="1761" class="Symbol">:</a> <a id="1763" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1768" class="Symbol">}</a>
  <a id="1772" class="Symbol">(</a><a id="1773" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1773" class="Bound">Cᵉ</a> <a id="1776" class="Symbol">:</a> <a id="1778" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="1791" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1753" class="Bound">l1ᵉ</a> <a id="1795" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1757" class="Bound">l2ᵉ</a><a id="1798" class="Symbol">)</a>
  <a id="1802" class="Symbol">(</a><a id="1803" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1803" class="Bound">tᵉ</a> <a id="1806" class="Symbol">:</a> <a id="1808" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1554" class="Function">terminal-obj-Precategoryᵉ</a> <a id="1834" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1773" class="Bound">Cᵉ</a><a id="1836" class="Symbol">)</a>
  <a id="1840" class="Keyword">where</a>

  <a id="1849" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1849" class="Function">obj-terminal-obj-Precategoryᵉ</a> <a id="1879" class="Symbol">:</a> <a id="1881" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="1898" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1773" class="Bound">Cᵉ</a>
  <a id="1903" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1849" class="Function">obj-terminal-obj-Precategoryᵉ</a> <a id="1933" class="Symbol">=</a> <a id="1935" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="1940" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1803" class="Bound">tᵉ</a>

  <a id="1946" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1946" class="Function">is-terminal-obj-terminal-obj-Precategoryᵉ</a> <a id="1988" class="Symbol">:</a>
    <a id="1994" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#754" class="Function">is-terminal-obj-Precategoryᵉ</a> <a id="2023" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1773" class="Bound">Cᵉ</a> <a id="2026" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1849" class="Function">obj-terminal-obj-Precategoryᵉ</a>
  <a id="2058" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1946" class="Function">is-terminal-obj-terminal-obj-Precategoryᵉ</a> <a id="2100" class="Symbol">=</a> <a id="2102" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2107" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1803" class="Bound">tᵉ</a>

  <a id="2113" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#2113" class="Function">hom-terminal-obj-Precategoryᵉ</a> <a id="2143" class="Symbol">:</a>
    <a id="2149" class="Symbol">(</a><a id="2150" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#2150" class="Bound">yᵉ</a> <a id="2153" class="Symbol">:</a> <a id="2155" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="2172" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1773" class="Bound">Cᵉ</a><a id="2174" class="Symbol">)</a> <a id="2176" class="Symbol">→</a>
    <a id="2182" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="2199" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1773" class="Bound">Cᵉ</a> <a id="2202" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#2150" class="Bound">yᵉ</a> <a id="2205" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1849" class="Function">obj-terminal-obj-Precategoryᵉ</a>
  <a id="2237" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#2113" class="Function">hom-terminal-obj-Precategoryᵉ</a> <a id="2267" class="Symbol">=</a>
    <a id="2273" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1121" class="Function">hom-is-terminal-obj-Precategoryᵉ</a> <a id="2306" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1773" class="Bound">Cᵉ</a>
      <a id="2315" class="Symbol">(</a> <a id="2317" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1849" class="Function">obj-terminal-obj-Precategoryᵉ</a><a id="2346" class="Symbol">)</a>
      <a id="2354" class="Symbol">(</a> <a id="2356" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1946" class="Function">is-terminal-obj-terminal-obj-Precategoryᵉ</a><a id="2397" class="Symbol">)</a>

  <a id="2402" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#2402" class="Function">is-unique-hom-terminal-obj-Precategoryᵉ</a> <a id="2442" class="Symbol">:</a>
    <a id="2448" class="Symbol">(</a><a id="2449" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#2449" class="Bound">yᵉ</a> <a id="2452" class="Symbol">:</a> <a id="2454" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="2471" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1773" class="Bound">Cᵉ</a><a id="2473" class="Symbol">)</a> <a id="2475" class="Symbol">→</a>
    <a id="2481" class="Symbol">(</a><a id="2482" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#2482" class="Bound">fᵉ</a> <a id="2485" class="Symbol">:</a> <a id="2487" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="2504" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1773" class="Bound">Cᵉ</a> <a id="2507" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#2449" class="Bound">yᵉ</a> <a id="2510" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1849" class="Function">obj-terminal-obj-Precategoryᵉ</a><a id="2539" class="Symbol">)</a> <a id="2541" class="Symbol">→</a>
    <a id="2547" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#2113" class="Function">hom-terminal-obj-Precategoryᵉ</a> <a id="2577" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#2449" class="Bound">yᵉ</a> <a id="2580" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="2583" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#2482" class="Bound">fᵉ</a>
  <a id="2588" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#2402" class="Function">is-unique-hom-terminal-obj-Precategoryᵉ</a> <a id="2628" class="Symbol">=</a>
    <a id="2634" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1273" class="Function">is-unique-hom-is-terminal-obj-Precategoryᵉ</a> <a id="2677" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1773" class="Bound">Cᵉ</a>
      <a id="2686" class="Symbol">(</a> <a id="2688" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1849" class="Function">obj-terminal-obj-Precategoryᵉ</a><a id="2717" class="Symbol">)</a>
      <a id="2725" class="Symbol">(</a> <a id="2727" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html#1946" class="Function">is-terminal-obj-terminal-obj-Precategoryᵉ</a><a id="2768" class="Symbol">)</a>
</pre>