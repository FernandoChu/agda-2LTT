# Whiskering higher homotopies with respect to composition

<pre class="Agda"><a id="69" class="Keyword">module</a> <a id="76" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html" class="Module">foundation.whiskering-higher-homotopies-compositionᵉ</a> <a id="129" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-functionsᵉ</a>
<a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
<a id="285" class="Keyword">open</a> <a id="290" class="Keyword">import</a> <a id="297" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html" class="Module">foundation.whiskering-homotopies-compositionᵉ</a>

<a id="344" class="Keyword">open</a> <a id="349" class="Keyword">import</a> <a id="356" href="foundation-core.homotopies%25E1%25B5%2589.html" class="Module">foundation-core.homotopiesᵉ</a>
</pre>
</details>

## Idea

Consider two dependent functions `f g : (x : A) → B x` equipped with two
[homotopies](foundation-core.homotopies.md) `H H' : f ~ g`, and consider a
family of maps `h : (x : A) → B x → C x`. Then we obtain a map

```text
  α ↦ ap h ·l α : H ~ H' → h ·l H ~ h ·l H'
```

This operation is called the
{{#concept "left whiskering" Disambiguation="`2`-homotopies with respect to composition" Agda=left-whisker-comp²}}.
Alternatively the left whiskering operation of `2`-homotopies can be defined
using the
[action on higher identifications of functions](foundation.action-on-higher-identifications-functions.md)
by

```text
  α x ↦ ap² h (α x).
```

Similarly, the
{{#concept "right whiskering" Disambiguation="2-homotopies with respect to composition" Agda=right-whisker-comp²}}
is defined to be the operation

```text
  (H ~ H') → (h : (x : A) → B x) → (H ·r h ~ H' ·r h)
```

given by

```text
  α h ↦ α ·r h,
```

for any pair of homotopies `H H' : f ~ g`, where
`f g : (x : A) (y : B x) → C x y`.

## Definitions

### Left whiskering higher homotopies

<pre class="Agda"><a id="1471" class="Keyword">module</a> <a id="1478" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1478" class="Module">_</a>
  <a id="1482" class="Symbol">{</a><a id="1483" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1483" class="Bound">l1ᵉ</a> <a id="1487" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1487" class="Bound">l2ᵉ</a> <a id="1491" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1491" class="Bound">l3ᵉ</a> <a id="1495" class="Symbol">:</a> <a id="1497" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1502" class="Symbol">}</a> <a id="1504" class="Symbol">{</a><a id="1505" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1505" class="Bound">Aᵉ</a> <a id="1508" class="Symbol">:</a> <a id="1510" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1514" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1483" class="Bound">l1ᵉ</a><a id="1517" class="Symbol">}</a> <a id="1519" class="Symbol">{</a><a id="1520" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1520" class="Bound">Bᵉ</a> <a id="1523" class="Symbol">:</a> <a id="1525" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1505" class="Bound">Aᵉ</a> <a id="1528" class="Symbol">→</a> <a id="1530" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1534" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1487" class="Bound">l2ᵉ</a><a id="1537" class="Symbol">}</a> <a id="1539" class="Symbol">{</a><a id="1540" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1540" class="Bound">Cᵉ</a> <a id="1543" class="Symbol">:</a> <a id="1545" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1505" class="Bound">Aᵉ</a> <a id="1548" class="Symbol">→</a> <a id="1550" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1554" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1491" class="Bound">l3ᵉ</a><a id="1557" class="Symbol">}</a>
  <a id="1561" class="Symbol">{</a><a id="1562" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1562" class="Bound">fᵉ</a> <a id="1565" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1565" class="Bound">gᵉ</a> <a id="1568" class="Symbol">:</a> <a id="1570" class="Symbol">(</a><a id="1571" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1571" class="Bound">xᵉ</a> <a id="1574" class="Symbol">:</a> <a id="1576" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1505" class="Bound">Aᵉ</a><a id="1578" class="Symbol">)</a> <a id="1580" class="Symbol">→</a> <a id="1582" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1520" class="Bound">Bᵉ</a> <a id="1585" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1571" class="Bound">xᵉ</a><a id="1587" class="Symbol">}</a>
  <a id="1591" class="Keyword">where</a>

  <a id="1600" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1600" class="Function">left-whisker-comp²ᵉ</a> <a id="1620" class="Symbol">:</a>
    <a id="1626" class="Symbol">(</a><a id="1627" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1627" class="Bound">hᵉ</a> <a id="1630" class="Symbol">:</a> <a id="1632" class="Symbol">{</a><a id="1633" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1633" class="Bound">xᵉ</a> <a id="1636" class="Symbol">:</a> <a id="1638" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1505" class="Bound">Aᵉ</a><a id="1640" class="Symbol">}</a> <a id="1642" class="Symbol">→</a> <a id="1644" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1520" class="Bound">Bᵉ</a> <a id="1647" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1633" class="Bound">xᵉ</a> <a id="1650" class="Symbol">→</a> <a id="1652" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1540" class="Bound">Cᵉ</a> <a id="1655" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1633" class="Bound">xᵉ</a><a id="1657" class="Symbol">)</a> <a id="1659" class="Symbol">{</a><a id="1660" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1660" class="Bound">Hᵉ</a> <a id="1663" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1663" class="Bound">H&#39;ᵉ</a> <a id="1667" class="Symbol">:</a> <a id="1669" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1562" class="Bound">fᵉ</a> <a id="1672" href="foundation-core.homotopies%25E1%25B5%2589.html#2800" class="Function Operator">~ᵉ</a> <a id="1675" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1565" class="Bound">gᵉ</a><a id="1677" class="Symbol">}</a> <a id="1679" class="Symbol">(</a><a id="1680" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1680" class="Bound">αᵉ</a> <a id="1683" class="Symbol">:</a> <a id="1685" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1660" class="Bound">Hᵉ</a> <a id="1688" href="foundation-core.homotopies%25E1%25B5%2589.html#2800" class="Function Operator">~ᵉ</a> <a id="1691" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1663" class="Bound">H&#39;ᵉ</a><a id="1694" class="Symbol">)</a> <a id="1696" class="Symbol">→</a> <a id="1698" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1627" class="Bound">hᵉ</a> <a id="1701" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#2417" class="Function Operator">·lᵉ</a> <a id="1705" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1660" class="Bound">Hᵉ</a> <a id="1708" href="foundation-core.homotopies%25E1%25B5%2589.html#2800" class="Function Operator">~ᵉ</a> <a id="1711" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1627" class="Bound">hᵉ</a> <a id="1714" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#2417" class="Function Operator">·lᵉ</a> <a id="1718" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1663" class="Bound">H&#39;ᵉ</a>
  <a id="1724" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1600" class="Function">left-whisker-comp²ᵉ</a> <a id="1744" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1744" class="Bound">hᵉ</a> <a id="1747" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1747" class="Bound">αᵉ</a> <a id="1750" class="Symbol">=</a> <a id="1752" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="1756" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1744" class="Bound">hᵉ</a> <a id="1759" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#2417" class="Function Operator">·lᵉ</a> <a id="1763" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1747" class="Bound">αᵉ</a>
</pre>
### Right whiskering higher homotopies

<pre class="Agda"><a id="1819" class="Keyword">module</a> <a id="1826" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1826" class="Module">_</a>
  <a id="1830" class="Symbol">{</a><a id="1831" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1831" class="Bound">l1ᵉ</a> <a id="1835" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1835" class="Bound">l2ᵉ</a> <a id="1839" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1839" class="Bound">l3ᵉ</a> <a id="1843" class="Symbol">:</a> <a id="1845" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1850" class="Symbol">}</a> <a id="1852" class="Symbol">{</a><a id="1853" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1853" class="Bound">Aᵉ</a> <a id="1856" class="Symbol">:</a> <a id="1858" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1862" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1831" class="Bound">l1ᵉ</a><a id="1865" class="Symbol">}</a> <a id="1867" class="Symbol">{</a><a id="1868" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1868" class="Bound">Bᵉ</a> <a id="1871" class="Symbol">:</a> <a id="1873" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1853" class="Bound">Aᵉ</a> <a id="1876" class="Symbol">→</a> <a id="1878" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1882" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1835" class="Bound">l2ᵉ</a><a id="1885" class="Symbol">}</a> <a id="1887" class="Symbol">{</a><a id="1888" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1888" class="Bound">Cᵉ</a> <a id="1891" class="Symbol">:</a> <a id="1893" class="Symbol">(</a><a id="1894" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1894" class="Bound">xᵉ</a> <a id="1897" class="Symbol">:</a> <a id="1899" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1853" class="Bound">Aᵉ</a><a id="1901" class="Symbol">)</a> <a id="1903" class="Symbol">→</a> <a id="1905" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1868" class="Bound">Bᵉ</a> <a id="1908" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1894" class="Bound">xᵉ</a> <a id="1911" class="Symbol">→</a> <a id="1913" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1917" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1839" class="Bound">l3ᵉ</a><a id="1920" class="Symbol">}</a>
  <a id="1924" class="Symbol">{</a><a id="1925" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1925" class="Bound">fᵉ</a> <a id="1928" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1928" class="Bound">gᵉ</a> <a id="1931" class="Symbol">:</a> <a id="1933" class="Symbol">{</a><a id="1934" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1934" class="Bound">xᵉ</a> <a id="1937" class="Symbol">:</a> <a id="1939" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1853" class="Bound">Aᵉ</a><a id="1941" class="Symbol">}</a> <a id="1943" class="Symbol">(</a><a id="1944" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1944" class="Bound">yᵉ</a> <a id="1947" class="Symbol">:</a> <a id="1949" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1868" class="Bound">Bᵉ</a> <a id="1952" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1934" class="Bound">xᵉ</a><a id="1954" class="Symbol">)</a> <a id="1956" class="Symbol">→</a> <a id="1958" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1888" class="Bound">Cᵉ</a> <a id="1961" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1934" class="Bound">xᵉ</a> <a id="1964" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1944" class="Bound">yᵉ</a><a id="1966" class="Symbol">}</a> <a id="1968" class="Symbol">{</a><a id="1969" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1969" class="Bound">Hᵉ</a> <a id="1972" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1972" class="Bound">H&#39;ᵉ</a> <a id="1976" class="Symbol">:</a> <a id="1978" class="Symbol">{</a><a id="1979" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1979" class="Bound">xᵉ</a> <a id="1982" class="Symbol">:</a> <a id="1984" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1853" class="Bound">Aᵉ</a><a id="1986" class="Symbol">}</a> <a id="1988" class="Symbol">→</a> <a id="1990" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1925" class="Bound">fᵉ</a> <a id="1993" class="Symbol">{</a><a id="1994" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1979" class="Bound">xᵉ</a><a id="1996" class="Symbol">}</a> <a id="1998" href="foundation-core.homotopies%25E1%25B5%2589.html#2800" class="Function Operator">~ᵉ</a> <a id="2001" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1928" class="Bound">gᵉ</a> <a id="2004" class="Symbol">{</a><a id="2005" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1979" class="Bound">xᵉ</a><a id="2007" class="Symbol">}}</a>
  <a id="2012" class="Keyword">where</a>

  <a id="2021" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2021" class="Function">right-whisker-comp²ᵉ</a> <a id="2042" class="Symbol">:</a>
    <a id="2048" class="Symbol">(</a><a id="2049" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2049" class="Bound">αᵉ</a> <a id="2052" class="Symbol">:</a> <a id="2054" class="Symbol">{</a><a id="2055" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2055" class="Bound">xᵉ</a> <a id="2058" class="Symbol">:</a> <a id="2060" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1853" class="Bound">Aᵉ</a><a id="2062" class="Symbol">}</a> <a id="2064" class="Symbol">→</a> <a id="2066" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1969" class="Bound">Hᵉ</a> <a id="2069" class="Symbol">{</a><a id="2070" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2055" class="Bound">xᵉ</a><a id="2072" class="Symbol">}</a> <a id="2074" href="foundation-core.homotopies%25E1%25B5%2589.html#2800" class="Function Operator">~ᵉ</a> <a id="2077" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1972" class="Bound">H&#39;ᵉ</a> <a id="2081" class="Symbol">{</a><a id="2082" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2055" class="Bound">xᵉ</a><a id="2084" class="Symbol">})</a> <a id="2087" class="Symbol">(</a><a id="2088" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2088" class="Bound">hᵉ</a> <a id="2091" class="Symbol">:</a> <a id="2093" class="Symbol">(</a><a id="2094" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2094" class="Bound">xᵉ</a> <a id="2097" class="Symbol">:</a> <a id="2099" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1853" class="Bound">Aᵉ</a><a id="2101" class="Symbol">)</a> <a id="2103" class="Symbol">→</a> <a id="2105" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1868" class="Bound">Bᵉ</a> <a id="2108" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2094" class="Bound">xᵉ</a><a id="2110" class="Symbol">)</a> <a id="2112" class="Symbol">→</a> <a id="2114" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1969" class="Bound">Hᵉ</a> <a id="2117" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#2836" class="Function Operator">·rᵉ</a> <a id="2121" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2088" class="Bound">hᵉ</a> <a id="2124" href="foundation-core.homotopies%25E1%25B5%2589.html#2800" class="Function Operator">~ᵉ</a> <a id="2127" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#1972" class="Bound">H&#39;ᵉ</a> <a id="2131" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#2836" class="Function Operator">·rᵉ</a> <a id="2135" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2088" class="Bound">hᵉ</a>
  <a id="2140" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2021" class="Function">right-whisker-comp²ᵉ</a> <a id="2161" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2161" class="Bound">αᵉ</a> <a id="2164" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2164" class="Bound">hᵉ</a> <a id="2167" class="Symbol">=</a> <a id="2169" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2161" class="Bound">αᵉ</a> <a id="2172" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#2836" class="Function Operator">·rᵉ</a> <a id="2176" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2164" class="Bound">hᵉ</a>
</pre>
### Double whiskering higher homotopies

<pre class="Agda"><a id="2233" class="Keyword">module</a> <a id="2240" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2240" class="Module">_</a>
  <a id="2244" class="Symbol">{</a><a id="2245" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2245" class="Bound">l1ᵉ</a> <a id="2249" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2249" class="Bound">l2ᵉ</a> <a id="2253" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2253" class="Bound">l3ᵉ</a> <a id="2257" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2257" class="Bound">l4ᵉ</a> <a id="2261" class="Symbol">:</a> <a id="2263" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2268" class="Symbol">}</a> <a id="2270" class="Symbol">{</a><a id="2271" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2271" class="Bound">Aᵉ</a> <a id="2274" class="Symbol">:</a> <a id="2276" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2280" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2245" class="Bound">l1ᵉ</a><a id="2283" class="Symbol">}</a> <a id="2285" class="Symbol">{</a><a id="2286" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2286" class="Bound">Bᵉ</a> <a id="2289" class="Symbol">:</a> <a id="2291" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2271" class="Bound">Aᵉ</a> <a id="2294" class="Symbol">→</a> <a id="2296" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2300" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2249" class="Bound">l2ᵉ</a><a id="2303" class="Symbol">}</a>
  <a id="2307" class="Symbol">{</a><a id="2308" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2308" class="Bound">Cᵉ</a> <a id="2311" class="Symbol">:</a> <a id="2313" class="Symbol">(</a><a id="2314" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2314" class="Bound">xᵉ</a> <a id="2317" class="Symbol">:</a> <a id="2319" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2271" class="Bound">Aᵉ</a><a id="2321" class="Symbol">)</a> <a id="2323" class="Symbol">→</a> <a id="2325" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2286" class="Bound">Bᵉ</a> <a id="2328" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2314" class="Bound">xᵉ</a> <a id="2331" class="Symbol">→</a> <a id="2333" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2337" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2253" class="Bound">l3ᵉ</a><a id="2340" class="Symbol">}</a> <a id="2342" class="Symbol">{</a><a id="2343" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2343" class="Bound">Dᵉ</a> <a id="2346" class="Symbol">:</a> <a id="2348" class="Symbol">(</a><a id="2349" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2349" class="Bound">xᵉ</a> <a id="2352" class="Symbol">:</a> <a id="2354" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2271" class="Bound">Aᵉ</a><a id="2356" class="Symbol">)</a> <a id="2358" class="Symbol">→</a> <a id="2360" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2286" class="Bound">Bᵉ</a> <a id="2363" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2349" class="Bound">xᵉ</a> <a id="2366" class="Symbol">→</a> <a id="2368" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2372" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2257" class="Bound">l4ᵉ</a><a id="2375" class="Symbol">}</a>
  <a id="2379" class="Symbol">{</a><a id="2380" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2380" class="Bound">fᵉ</a> <a id="2383" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2383" class="Bound">gᵉ</a> <a id="2386" class="Symbol">:</a> <a id="2388" class="Symbol">{</a><a id="2389" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2389" class="Bound">xᵉ</a> <a id="2392" class="Symbol">:</a> <a id="2394" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2271" class="Bound">Aᵉ</a><a id="2396" class="Symbol">}</a> <a id="2398" class="Symbol">(</a><a id="2399" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2399" class="Bound">yᵉ</a> <a id="2402" class="Symbol">:</a> <a id="2404" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2286" class="Bound">Bᵉ</a> <a id="2407" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2389" class="Bound">xᵉ</a><a id="2409" class="Symbol">)</a> <a id="2411" class="Symbol">→</a> <a id="2413" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2308" class="Bound">Cᵉ</a> <a id="2416" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2389" class="Bound">xᵉ</a> <a id="2419" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2399" class="Bound">yᵉ</a><a id="2421" class="Symbol">}</a> <a id="2423" class="Symbol">{</a><a id="2424" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2424" class="Bound">Hᵉ</a> <a id="2427" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2427" class="Bound">H&#39;ᵉ</a> <a id="2431" class="Symbol">:</a> <a id="2433" class="Symbol">{</a><a id="2434" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2434" class="Bound">xᵉ</a> <a id="2437" class="Symbol">:</a> <a id="2439" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2271" class="Bound">Aᵉ</a><a id="2441" class="Symbol">}</a> <a id="2443" class="Symbol">→</a> <a id="2445" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2380" class="Bound">fᵉ</a> <a id="2448" class="Symbol">{</a><a id="2449" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2434" class="Bound">xᵉ</a><a id="2451" class="Symbol">}</a> <a id="2453" href="foundation-core.homotopies%25E1%25B5%2589.html#2800" class="Function Operator">~ᵉ</a> <a id="2456" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2383" class="Bound">gᵉ</a> <a id="2459" class="Symbol">{</a><a id="2460" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2434" class="Bound">xᵉ</a><a id="2462" class="Symbol">}}</a>
  <a id="2467" class="Keyword">where</a>

  <a id="2476" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2476" class="Function">double-whisker-comp²ᵉ</a> <a id="2498" class="Symbol">:</a>
    <a id="2504" class="Symbol">(</a><a id="2505" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2505" class="Bound">leftᵉ</a> <a id="2511" class="Symbol">:</a> <a id="2513" class="Symbol">{</a><a id="2514" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2514" class="Bound">xᵉ</a> <a id="2517" class="Symbol">:</a> <a id="2519" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2271" class="Bound">Aᵉ</a><a id="2521" class="Symbol">}</a> <a id="2523" class="Symbol">{</a><a id="2524" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2524" class="Bound">yᵉ</a> <a id="2527" class="Symbol">:</a> <a id="2529" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2286" class="Bound">Bᵉ</a> <a id="2532" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2514" class="Bound">xᵉ</a><a id="2534" class="Symbol">}</a> <a id="2536" class="Symbol">→</a> <a id="2538" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2308" class="Bound">Cᵉ</a> <a id="2541" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2514" class="Bound">xᵉ</a> <a id="2544" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2524" class="Bound">yᵉ</a> <a id="2547" class="Symbol">→</a> <a id="2549" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2343" class="Bound">Dᵉ</a> <a id="2552" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2514" class="Bound">xᵉ</a> <a id="2555" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2524" class="Bound">yᵉ</a><a id="2557" class="Symbol">)</a>
    <a id="2563" class="Symbol">(</a><a id="2564" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2564" class="Bound">αᵉ</a> <a id="2567" class="Symbol">:</a> <a id="2569" class="Symbol">{</a><a id="2570" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2570" class="Bound">xᵉ</a> <a id="2573" class="Symbol">:</a> <a id="2575" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2271" class="Bound">Aᵉ</a><a id="2577" class="Symbol">}</a> <a id="2579" class="Symbol">→</a> <a id="2581" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2424" class="Bound">Hᵉ</a> <a id="2584" class="Symbol">{</a><a id="2585" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2570" class="Bound">xᵉ</a><a id="2587" class="Symbol">}</a> <a id="2589" href="foundation-core.homotopies%25E1%25B5%2589.html#2800" class="Function Operator">~ᵉ</a> <a id="2592" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2427" class="Bound">H&#39;ᵉ</a> <a id="2596" class="Symbol">{</a><a id="2597" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2570" class="Bound">xᵉ</a><a id="2599" class="Symbol">})</a>
    <a id="2606" class="Symbol">(</a><a id="2607" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2607" class="Bound">rightᵉ</a> <a id="2614" class="Symbol">:</a> <a id="2616" class="Symbol">(</a><a id="2617" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2617" class="Bound">xᵉ</a> <a id="2620" class="Symbol">:</a> <a id="2622" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2271" class="Bound">Aᵉ</a><a id="2624" class="Symbol">)</a> <a id="2626" class="Symbol">→</a> <a id="2628" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2286" class="Bound">Bᵉ</a> <a id="2631" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2617" class="Bound">xᵉ</a><a id="2633" class="Symbol">)</a> <a id="2635" class="Symbol">→</a>
    <a id="2641" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2505" class="Bound">leftᵉ</a> <a id="2647" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#2417" class="Function Operator">·lᵉ</a> <a id="2651" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2424" class="Bound">Hᵉ</a> <a id="2654" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#2836" class="Function Operator">·rᵉ</a> <a id="2658" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2607" class="Bound">rightᵉ</a> <a id="2665" href="foundation-core.homotopies%25E1%25B5%2589.html#2800" class="Function Operator">~ᵉ</a> <a id="2668" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2505" class="Bound">leftᵉ</a> <a id="2674" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#2417" class="Function Operator">·lᵉ</a> <a id="2678" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2427" class="Bound">H&#39;ᵉ</a> <a id="2682" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#2836" class="Function Operator">·rᵉ</a> <a id="2686" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2607" class="Bound">rightᵉ</a>
  <a id="2695" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2476" class="Function">double-whisker-comp²ᵉ</a> <a id="2717" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2717" class="Bound">leftᵉ</a> <a id="2723" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2723" class="Bound">αᵉ</a> <a id="2726" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2726" class="Bound">rightᵉ</a> <a id="2733" class="Symbol">=</a> <a id="2735" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#3069" class="Function">double-whisker-compᵉ</a> <a id="2756" class="Symbol">(</a><a id="2757" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2761" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2717" class="Bound">leftᵉ</a><a id="2766" class="Symbol">)</a> <a id="2768" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2723" class="Bound">αᵉ</a> <a id="2771" href="foundation.whiskering-higher-homotopies-composition%25E1%25B5%2589.html#2726" class="Bound">rightᵉ</a>
</pre>