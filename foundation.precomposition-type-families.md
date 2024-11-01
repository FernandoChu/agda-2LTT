# Precomposition of type families

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="foundation.precomposition-type-families.html" class="Module">foundation.precomposition-type-families</a> <a id="91" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="147" class="Keyword">open</a> <a id="152" class="Keyword">import</a> <a id="159" href="foundation.homotopy-induction.html" class="Module">foundation.homotopy-induction</a>
<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="foundation.transport-along-homotopies.html" class="Module">foundation.transport-along-homotopies</a>
<a id="239" class="Keyword">open</a> <a id="244" class="Keyword">import</a> <a id="251" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="278" class="Keyword">open</a> <a id="283" class="Keyword">import</a> <a id="290" href="foundation.whiskering-homotopies-composition.html" class="Module">foundation.whiskering-homotopies-composition</a>

<a id="336" class="Keyword">open</a> <a id="341" class="Keyword">import</a> <a id="348" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="379" class="Keyword">open</a> <a id="384" class="Keyword">import</a> <a id="391" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="418" class="Keyword">open</a> <a id="423" class="Keyword">import</a> <a id="430" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

## Idea

Any map `f : A → B` induces a
{{#concept "precomposition operation" Disambiguation="type families" Agda=precomp-family}}

```text
  (B → 𝒰) → (A → 𝒰)
```

given by [precomposing](foundation-core.precomposition-functions.md) any
`Q : B → 𝒰` to `Q ∘ f : A → 𝒰`.

## Definitions

### The precomposition operation on type familes

<pre class="Agda"><a id="822" class="Keyword">module</a> <a id="829" href="foundation.precomposition-type-families.html#829" class="Module">_</a>
  <a id="833" class="Symbol">{</a><a id="834" href="foundation.precomposition-type-families.html#834" class="Bound">l1</a> <a id="837" href="foundation.precomposition-type-families.html#837" class="Bound">l2</a> <a id="840" class="Symbol">:</a> <a id="842" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="847" class="Symbol">}</a> <a id="849" class="Symbol">{</a><a id="850" href="foundation.precomposition-type-families.html#850" class="Bound">A</a> <a id="852" class="Symbol">:</a> <a id="854" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="857" href="foundation.precomposition-type-families.html#834" class="Bound">l1</a><a id="859" class="Symbol">}</a> <a id="861" class="Symbol">{</a><a id="862" href="foundation.precomposition-type-families.html#862" class="Bound">B</a> <a id="864" class="Symbol">:</a> <a id="866" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="869" href="foundation.precomposition-type-families.html#837" class="Bound">l2</a><a id="871" class="Symbol">}</a> <a id="873" class="Symbol">(</a><a id="874" href="foundation.precomposition-type-families.html#874" class="Bound">f</a> <a id="876" class="Symbol">:</a> <a id="878" href="foundation.precomposition-type-families.html#850" class="Bound">A</a> <a id="880" class="Symbol">→</a> <a id="882" href="foundation.precomposition-type-families.html#862" class="Bound">B</a><a id="883" class="Symbol">)</a>
  <a id="887" class="Keyword">where</a>

  <a id="896" href="foundation.precomposition-type-families.html#896" class="Function">precomp-family</a> <a id="911" class="Symbol">:</a> <a id="913" class="Symbol">{</a><a id="914" href="foundation.precomposition-type-families.html#914" class="Bound">l</a> <a id="916" class="Symbol">:</a> <a id="918" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="923" class="Symbol">}</a> <a id="925" class="Symbol">→</a> <a id="927" class="Symbol">(</a><a id="928" href="foundation.precomposition-type-families.html#862" class="Bound">B</a> <a id="930" class="Symbol">→</a> <a id="932" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="935" href="foundation.precomposition-type-families.html#914" class="Bound">l</a><a id="936" class="Symbol">)</a> <a id="938" class="Symbol">→</a> <a id="940" class="Symbol">(</a><a id="941" href="foundation.precomposition-type-families.html#850" class="Bound">A</a> <a id="943" class="Symbol">→</a> <a id="945" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="948" href="foundation.precomposition-type-families.html#914" class="Bound">l</a><a id="949" class="Symbol">)</a>
  <a id="953" href="foundation.precomposition-type-families.html#896" class="Function">precomp-family</a> <a id="968" href="foundation.precomposition-type-families.html#968" class="Bound">Q</a> <a id="970" class="Symbol">=</a> <a id="972" href="foundation.precomposition-type-families.html#968" class="Bound">Q</a> <a id="974" href="foundation-core.function-types.html#455" class="Function Operator">∘</a> <a id="976" href="foundation.precomposition-type-families.html#874" class="Bound">f</a>
</pre>
## Properties

### Transport along homotopies in precomposed type families

[Transporting](foundation.transport-along-homotopies.md) along a
[homotopy](foundation.homotopies.md) `H : g ~ h` in the family `Q ∘ f` gives us
a map of families of elements

```text
  ((a : A) → Q (f (g a))) → ((a : A) → Q (f (h a))) .
```

We show that this map is homotopic to transporting along
`f ·l H : f ∘ g ~ f ∘ h` in the family `Q`.

<pre class="Agda"><a id="1412" class="Keyword">module</a> <a id="1419" href="foundation.precomposition-type-families.html#1419" class="Module">_</a>
  <a id="1423" class="Symbol">{</a><a id="1424" href="foundation.precomposition-type-families.html#1424" class="Bound">l1</a> <a id="1427" href="foundation.precomposition-type-families.html#1427" class="Bound">l2</a> <a id="1430" href="foundation.precomposition-type-families.html#1430" class="Bound">l3</a> <a id="1433" href="foundation.precomposition-type-families.html#1433" class="Bound">l4</a> <a id="1436" class="Symbol">:</a> <a id="1438" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1443" class="Symbol">}</a> <a id="1445" class="Symbol">{</a><a id="1446" href="foundation.precomposition-type-families.html#1446" class="Bound">A</a> <a id="1448" class="Symbol">:</a> <a id="1450" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1453" href="foundation.precomposition-type-families.html#1424" class="Bound">l1</a><a id="1455" class="Symbol">}</a> <a id="1457" class="Symbol">{</a><a id="1458" href="foundation.precomposition-type-families.html#1458" class="Bound">B</a> <a id="1460" class="Symbol">:</a> <a id="1462" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1465" href="foundation.precomposition-type-families.html#1427" class="Bound">l2</a><a id="1467" class="Symbol">}</a> <a id="1469" class="Symbol">(</a><a id="1470" href="foundation.precomposition-type-families.html#1470" class="Bound">f</a> <a id="1472" class="Symbol">:</a> <a id="1474" href="foundation.precomposition-type-families.html#1446" class="Bound">A</a> <a id="1476" class="Symbol">→</a> <a id="1478" href="foundation.precomposition-type-families.html#1458" class="Bound">B</a><a id="1479" class="Symbol">)</a> <a id="1481" class="Symbol">(</a><a id="1482" href="foundation.precomposition-type-families.html#1482" class="Bound">Q</a> <a id="1484" class="Symbol">:</a> <a id="1486" href="foundation.precomposition-type-families.html#1458" class="Bound">B</a> <a id="1488" class="Symbol">→</a> <a id="1490" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1493" href="foundation.precomposition-type-families.html#1430" class="Bound">l3</a><a id="1495" class="Symbol">)</a>
  <a id="1499" class="Symbol">{</a><a id="1500" href="foundation.precomposition-type-families.html#1500" class="Bound">X</a> <a id="1502" class="Symbol">:</a> <a id="1504" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1507" href="foundation.precomposition-type-families.html#1433" class="Bound">l4</a><a id="1509" class="Symbol">}</a> <a id="1511" class="Symbol">{</a><a id="1512" href="foundation.precomposition-type-families.html#1512" class="Bound">g</a> <a id="1514" class="Symbol">:</a> <a id="1516" href="foundation.precomposition-type-families.html#1500" class="Bound">X</a> <a id="1518" class="Symbol">→</a> <a id="1520" href="foundation.precomposition-type-families.html#1446" class="Bound">A</a><a id="1521" class="Symbol">}</a>
  <a id="1525" class="Keyword">where</a>

  <a id="1534" href="foundation.precomposition-type-families.html#1534" class="Function">statement-tr-htpy-precomp-family</a> <a id="1567" class="Symbol">:</a>
    <a id="1573" class="Symbol">{</a><a id="1574" href="foundation.precomposition-type-families.html#1574" class="Bound">h</a> <a id="1576" class="Symbol">:</a> <a id="1578" href="foundation.precomposition-type-families.html#1500" class="Bound">X</a> <a id="1580" class="Symbol">→</a> <a id="1582" href="foundation.precomposition-type-families.html#1446" class="Bound">A</a><a id="1583" class="Symbol">}</a> <a id="1585" class="Symbol">(</a><a id="1586" href="foundation.precomposition-type-families.html#1586" class="Bound">H</a> <a id="1588" class="Symbol">:</a> <a id="1590" href="foundation.precomposition-type-families.html#1512" class="Bound">g</a> <a id="1592" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1594" href="foundation.precomposition-type-families.html#1574" class="Bound">h</a><a id="1595" class="Symbol">)</a> <a id="1597" class="Symbol">→</a> <a id="1599" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1602" class="Symbol">(</a><a id="1603" href="foundation.precomposition-type-families.html#1430" class="Bound">l3</a> <a id="1606" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1608" href="foundation.precomposition-type-families.html#1433" class="Bound">l4</a><a id="1610" class="Symbol">)</a>
  <a id="1614" href="foundation.precomposition-type-families.html#1534" class="Function">statement-tr-htpy-precomp-family</a> <a id="1647" href="foundation.precomposition-type-families.html#1647" class="Bound">H</a> <a id="1649" class="Symbol">=</a>
    <a id="1655" href="foundation.transport-along-homotopies.html#1000" class="Function">tr-htpy</a> <a id="1663" class="Symbol">(λ</a> <a id="1666" href="foundation.precomposition-type-families.html#1666" class="Bound">_</a> <a id="1668" class="Symbol">→</a> <a id="1670" href="foundation.precomposition-type-families.html#896" class="Function">precomp-family</a> <a id="1685" href="foundation.precomposition-type-families.html#1470" class="Bound">f</a> <a id="1687" href="foundation.precomposition-type-families.html#1482" class="Bound">Q</a><a id="1688" class="Symbol">)</a> <a id="1690" href="foundation.precomposition-type-families.html#1647" class="Bound">H</a> <a id="1692" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1694" href="foundation.transport-along-homotopies.html#1000" class="Function">tr-htpy</a> <a id="1702" class="Symbol">(λ</a> <a id="1705" href="foundation.precomposition-type-families.html#1705" class="Bound">_</a> <a id="1707" class="Symbol">→</a> <a id="1709" href="foundation.precomposition-type-families.html#1482" class="Bound">Q</a><a id="1710" class="Symbol">)</a> <a id="1712" class="Symbol">(</a><a id="1713" href="foundation.precomposition-type-families.html#1470" class="Bound">f</a> <a id="1715" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l</a> <a id="1718" href="foundation.precomposition-type-families.html#1647" class="Bound">H</a><a id="1719" class="Symbol">)</a>

  <a id="1724" class="Keyword">abstract</a>
    <a id="1737" href="foundation.precomposition-type-families.html#1737" class="Function">tr-htpy-precomp-family</a> <a id="1760" class="Symbol">:</a>
      <a id="1768" class="Symbol">{</a><a id="1769" href="foundation.precomposition-type-families.html#1769" class="Bound">h</a> <a id="1771" class="Symbol">:</a> <a id="1773" href="foundation.precomposition-type-families.html#1500" class="Bound">X</a> <a id="1775" class="Symbol">→</a> <a id="1777" href="foundation.precomposition-type-families.html#1446" class="Bound">A</a><a id="1778" class="Symbol">}</a> <a id="1780" class="Symbol">(</a><a id="1781" href="foundation.precomposition-type-families.html#1781" class="Bound">H</a> <a id="1783" class="Symbol">:</a> <a id="1785" href="foundation.precomposition-type-families.html#1512" class="Bound">g</a> <a id="1787" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1789" href="foundation.precomposition-type-families.html#1769" class="Bound">h</a><a id="1790" class="Symbol">)</a> <a id="1792" class="Symbol">→</a>
      <a id="1800" href="foundation.precomposition-type-families.html#1534" class="Function">statement-tr-htpy-precomp-family</a> <a id="1833" href="foundation.precomposition-type-families.html#1781" class="Bound">H</a>
    <a id="1839" href="foundation.precomposition-type-families.html#1737" class="Function">tr-htpy-precomp-family</a> <a id="1862" class="Symbol">=</a>
      <a id="1870" href="foundation.homotopy-induction.html#4265" class="Function">ind-htpy</a> <a id="1879" href="foundation.precomposition-type-families.html#1512" class="Bound">g</a>
        <a id="1889" class="Symbol">(</a> <a id="1891" class="Symbol">λ</a> <a id="1893" href="foundation.precomposition-type-families.html#1893" class="Bound">h</a> <a id="1895" class="Symbol">→</a> <a id="1897" href="foundation.precomposition-type-families.html#1534" class="Function">statement-tr-htpy-precomp-family</a><a id="1929" class="Symbol">)</a>
        <a id="1939" class="Symbol">(</a> <a id="1941" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="1950" class="Symbol">)</a>

    <a id="1957" href="foundation.precomposition-type-families.html#1957" class="Function">compute-tr-htpy-precomp-family</a> <a id="1988" class="Symbol">:</a>
      <a id="1996" href="foundation.precomposition-type-families.html#1737" class="Function">tr-htpy-precomp-family</a> <a id="2019" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a> <a id="2029" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="2037" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
    <a id="2051" href="foundation.precomposition-type-families.html#1957" class="Function">compute-tr-htpy-precomp-family</a> <a id="2082" class="Symbol">=</a>
      <a id="2090" href="foundation.homotopy-induction.html#4496" class="Function">compute-ind-htpy</a> <a id="2107" href="foundation.precomposition-type-families.html#1512" class="Bound">g</a>
        <a id="2117" class="Symbol">(</a> <a id="2119" class="Symbol">λ</a> <a id="2121" href="foundation.precomposition-type-families.html#2121" class="Bound">h</a> <a id="2123" class="Symbol">→</a> <a id="2125" href="foundation.precomposition-type-families.html#1534" class="Function">statement-tr-htpy-precomp-family</a><a id="2157" class="Symbol">)</a>
        <a id="2167" class="Symbol">(</a> <a id="2169" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="2178" class="Symbol">)</a>
</pre>