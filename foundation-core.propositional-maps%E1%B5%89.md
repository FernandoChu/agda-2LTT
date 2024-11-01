# Propositional maps

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="foundation-core.propositional-maps%25E1%25B5%2589.html" class="Module">foundation-core.propositional-mapsᵉ</a> <a id="74" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="130" class="Keyword">open</a> <a id="135" class="Keyword">import</a> <a id="142" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-functionsᵉ</a>
<a id="190" class="Keyword">open</a> <a id="195" class="Keyword">import</a> <a id="202" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="235" class="Keyword">open</a> <a id="240" class="Keyword">import</a> <a id="247" href="foundation.fundamental-theorem-of-identity-types%25E1%25B5%2589.html" class="Module">foundation.fundamental-theorem-of-identity-typesᵉ</a>
<a id="297" class="Keyword">open</a> <a id="302" class="Keyword">import</a> <a id="309" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="foundation-core.contractible-types%25E1%25B5%2589.html" class="Module">foundation-core.contractible-typesᵉ</a>
<a id="386" class="Keyword">open</a> <a id="391" class="Keyword">import</a> <a id="398" href="foundation-core.embeddings%25E1%25B5%2589.html" class="Module">foundation-core.embeddingsᵉ</a>
<a id="426" class="Keyword">open</a> <a id="431" class="Keyword">import</a> <a id="438" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html" class="Module">foundation-core.fibers-of-mapsᵉ</a>
<a id="470" class="Keyword">open</a> <a id="475" class="Keyword">import</a> <a id="482" href="foundation-core.identity-types%25E1%25B5%2589.html" class="Module">foundation-core.identity-typesᵉ</a>
<a id="514" class="Keyword">open</a> <a id="519" class="Keyword">import</a> <a id="526" href="foundation-core.propositions%25E1%25B5%2589.html" class="Module">foundation-core.propositionsᵉ</a>
</pre>
</details>

## Idea

A map is said to be **propositional** if its
[fibers](foundation-core.fibers-of-maps.md) are
[propositions](foundation-core.propositions.md). This condition is the same as
the condition of being a
[`-1`-truncated map](foundation-core.truncated-maps.md), and it is
[equivalent](foundation-core.equivalences.md) to being an
[embedding](foundation-core.embeddings.md).

**Note:** Of the three equivalent conditions mentioned above, propositional
maps, `-1`-truncated maps, and embeddings, the central notion of in the
agda-unimath library is that of embedding. This means that most infrastructure
is available for embeddings, and that it is easy to convert from any of the
other two notions to the notion of embedding.

## Definitions

### The predicate of being a propositional map

<pre class="Agda"><a id="1371" class="Keyword">module</a> <a id="1378" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1378" class="Module">_</a>
  <a id="1382" class="Symbol">{</a><a id="1383" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1383" class="Bound">l1ᵉ</a> <a id="1387" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1387" class="Bound">l2ᵉ</a> <a id="1391" class="Symbol">:</a> <a id="1393" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1398" class="Symbol">}</a> <a id="1400" class="Symbol">{</a><a id="1401" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1401" class="Bound">Aᵉ</a> <a id="1404" class="Symbol">:</a> <a id="1406" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1410" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1383" class="Bound">l1ᵉ</a><a id="1413" class="Symbol">}</a> <a id="1415" class="Symbol">{</a><a id="1416" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1416" class="Bound">Bᵉ</a> <a id="1419" class="Symbol">:</a> <a id="1421" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1425" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1387" class="Bound">l2ᵉ</a><a id="1428" class="Symbol">}</a>
  <a id="1432" class="Keyword">where</a>

  <a id="1441" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1441" class="Function">is-prop-mapᵉ</a> <a id="1454" class="Symbol">:</a> <a id="1456" class="Symbol">(</a><a id="1457" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1401" class="Bound">Aᵉ</a> <a id="1460" class="Symbol">→</a> <a id="1462" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1416" class="Bound">Bᵉ</a><a id="1464" class="Symbol">)</a> <a id="1466" class="Symbol">→</a> <a id="1468" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1472" class="Symbol">(</a><a id="1473" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1383" class="Bound">l1ᵉ</a> <a id="1477" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1479" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1387" class="Bound">l2ᵉ</a><a id="1482" class="Symbol">)</a>
  <a id="1486" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1441" class="Function">is-prop-mapᵉ</a> <a id="1499" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1499" class="Bound">fᵉ</a> <a id="1502" class="Symbol">=</a> <a id="1504" class="Symbol">(</a><a id="1505" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1505" class="Bound">bᵉ</a> <a id="1508" class="Symbol">:</a> <a id="1510" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1416" class="Bound">Bᵉ</a><a id="1512" class="Symbol">)</a> <a id="1514" class="Symbol">→</a> <a id="1516" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="1525" class="Symbol">(</a><a id="1526" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html#962" class="Function">fiberᵉ</a> <a id="1533" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1499" class="Bound">fᵉ</a> <a id="1536" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1505" class="Bound">bᵉ</a><a id="1538" class="Symbol">)</a>
</pre>
### The type of propositional maps

<pre class="Agda"><a id="1589" class="Keyword">module</a> <a id="1596" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1596" class="Module">_</a>
  <a id="1600" class="Symbol">{</a><a id="1601" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1601" class="Bound">l1ᵉ</a> <a id="1605" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1605" class="Bound">l2ᵉ</a> <a id="1609" class="Symbol">:</a> <a id="1611" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1616" class="Symbol">}</a>
  <a id="1620" class="Keyword">where</a>

  <a id="1629" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1629" class="Function">prop-mapᵉ</a> <a id="1639" class="Symbol">:</a> <a id="1641" class="Symbol">(</a><a id="1642" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1642" class="Bound">Aᵉ</a> <a id="1645" class="Symbol">:</a> <a id="1647" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1651" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1601" class="Bound">l1ᵉ</a><a id="1654" class="Symbol">)</a> <a id="1656" class="Symbol">(</a><a id="1657" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1657" class="Bound">Bᵉ</a> <a id="1660" class="Symbol">:</a> <a id="1662" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1666" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1605" class="Bound">l2ᵉ</a><a id="1669" class="Symbol">)</a> <a id="1671" class="Symbol">→</a> <a id="1673" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1677" class="Symbol">(</a><a id="1678" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1601" class="Bound">l1ᵉ</a> <a id="1682" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1684" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1605" class="Bound">l2ᵉ</a><a id="1687" class="Symbol">)</a>
  <a id="1691" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1629" class="Function">prop-mapᵉ</a> <a id="1701" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1701" class="Bound">Aᵉ</a> <a id="1704" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1704" class="Bound">Bᵉ</a> <a id="1707" class="Symbol">=</a> <a id="1709" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="1712" class="Symbol">(</a><a id="1713" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1701" class="Bound">Aᵉ</a> <a id="1716" class="Symbol">→</a> <a id="1718" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1704" class="Bound">Bᵉ</a><a id="1720" class="Symbol">)</a> <a id="1722" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1441" class="Function">is-prop-mapᵉ</a>

  <a id="1738" class="Keyword">module</a> <a id="1745" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1745" class="Module">_</a>
    <a id="1751" class="Symbol">{</a><a id="1752" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1752" class="Bound">Aᵉ</a> <a id="1755" class="Symbol">:</a> <a id="1757" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1761" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1601" class="Bound">l1ᵉ</a><a id="1764" class="Symbol">}</a> <a id="1766" class="Symbol">{</a><a id="1767" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1767" class="Bound">Bᵉ</a> <a id="1770" class="Symbol">:</a> <a id="1772" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1776" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1605" class="Bound">l2ᵉ</a><a id="1779" class="Symbol">}</a> <a id="1781" class="Symbol">(</a><a id="1782" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1782" class="Bound">fᵉ</a> <a id="1785" class="Symbol">:</a> <a id="1787" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1629" class="Function">prop-mapᵉ</a> <a id="1797" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1752" class="Bound">Aᵉ</a> <a id="1800" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1767" class="Bound">Bᵉ</a><a id="1802" class="Symbol">)</a>
    <a id="1808" class="Keyword">where</a>

    <a id="1819" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1819" class="Function">map-prop-mapᵉ</a> <a id="1833" class="Symbol">:</a> <a id="1835" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1752" class="Bound">Aᵉ</a> <a id="1838" class="Symbol">→</a> <a id="1840" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1767" class="Bound">Bᵉ</a>
    <a id="1847" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1819" class="Function">map-prop-mapᵉ</a> <a id="1861" class="Symbol">=</a> <a id="1863" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="1868" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1782" class="Bound">fᵉ</a>

    <a id="1876" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1876" class="Function">is-prop-map-prop-mapᵉ</a> <a id="1898" class="Symbol">:</a> <a id="1900" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1441" class="Function">is-prop-mapᵉ</a> <a id="1913" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1819" class="Function">map-prop-mapᵉ</a>
    <a id="1931" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1876" class="Function">is-prop-map-prop-mapᵉ</a> <a id="1953" class="Symbol">=</a> <a id="1955" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="1960" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1782" class="Bound">fᵉ</a>
</pre>
## Properties

### The fibers of a map are propositions if and only if it is an embedding

<pre class="Agda"><a id="2067" class="Keyword">module</a> <a id="2074" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2074" class="Module">_</a>
  <a id="2078" class="Symbol">{</a><a id="2079" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2079" class="Bound">l1ᵉ</a> <a id="2083" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2083" class="Bound">l2ᵉ</a> <a id="2087" class="Symbol">:</a> <a id="2089" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2094" class="Symbol">}</a> <a id="2096" class="Symbol">{</a><a id="2097" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2097" class="Bound">Aᵉ</a> <a id="2100" class="Symbol">:</a> <a id="2102" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2106" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2079" class="Bound">l1ᵉ</a><a id="2109" class="Symbol">}</a> <a id="2111" class="Symbol">{</a><a id="2112" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2112" class="Bound">Bᵉ</a> <a id="2115" class="Symbol">:</a> <a id="2117" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2121" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2083" class="Bound">l2ᵉ</a><a id="2124" class="Symbol">}</a> <a id="2126" class="Symbol">{</a><a id="2127" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2130" class="Symbol">:</a> <a id="2132" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2097" class="Bound">Aᵉ</a> <a id="2135" class="Symbol">→</a> <a id="2137" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2112" class="Bound">Bᵉ</a><a id="2139" class="Symbol">}</a>
  <a id="2143" class="Keyword">where</a>

  <a id="2152" class="Keyword">abstract</a>
    <a id="2165" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2165" class="Function">is-emb-is-prop-mapᵉ</a> <a id="2185" class="Symbol">:</a> <a id="2187" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1441" class="Function">is-prop-mapᵉ</a> <a id="2200" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2203" class="Symbol">→</a> <a id="2205" href="foundation-core.embeddings%25E1%25B5%2589.html#1101" class="Function">is-embᵉ</a> <a id="2213" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a>
    <a id="2220" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2165" class="Function">is-emb-is-prop-mapᵉ</a> <a id="2240" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2240" class="Bound">is-prop-map-fᵉ</a> <a id="2255" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2255" class="Bound">xᵉ</a> <a id="2258" class="Symbol">=</a>
      <a id="2266" href="foundation.fundamental-theorem-of-identity-types%25E1%25B5%2589.html#2064" class="Function">fundamental-theorem-idᵉ</a>
        <a id="2298" class="Symbol">(</a> <a id="2300" href="foundation-core.contractible-types%25E1%25B5%2589.html#3162" class="Function">is-contr-equiv&#39;ᵉ</a>
          <a id="2327" class="Symbol">(</a> <a id="2329" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html#962" class="Function">fiberᵉ</a> <a id="2336" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2339" class="Symbol">(</a><a id="2340" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2343" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2255" class="Bound">xᵉ</a><a id="2345" class="Symbol">))</a>
          <a id="2358" class="Symbol">(</a> <a id="2360" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html#6929" class="Function">equiv-fiberᵉ</a> <a id="2373" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2376" class="Symbol">(</a><a id="2377" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2380" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2255" class="Bound">xᵉ</a><a id="2382" class="Symbol">))</a>
          <a id="2395" class="Symbol">(</a> <a id="2397" href="foundation-core.propositions%25E1%25B5%2589.html#3028" class="Function">is-proof-irrelevant-is-propᵉ</a> <a id="2426" class="Symbol">(</a><a id="2427" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2240" class="Bound">is-prop-map-fᵉ</a> <a id="2442" class="Symbol">(</a><a id="2443" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2446" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2255" class="Bound">xᵉ</a><a id="2448" class="Symbol">))</a> <a id="2451" class="Symbol">(</a><a id="2452" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2255" class="Bound">xᵉ</a> <a id="2455" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2458" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a><a id="2463" class="Symbol">)))</a>
        <a id="2475" class="Symbol">(</a> <a id="2477" class="Symbol">λ</a> <a id="2479" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2479" class="Bound">_</a> <a id="2481" class="Symbol">→</a> <a id="2483" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2487" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a><a id="2489" class="Symbol">)</a>

  <a id="2494" class="Keyword">abstract</a>
    <a id="2507" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2507" class="Function">is-prop-map-is-embᵉ</a> <a id="2527" class="Symbol">:</a> <a id="2529" href="foundation-core.embeddings%25E1%25B5%2589.html#1101" class="Function">is-embᵉ</a> <a id="2537" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2540" class="Symbol">→</a> <a id="2542" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1441" class="Function">is-prop-mapᵉ</a> <a id="2555" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a>
    <a id="2562" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2507" class="Function">is-prop-map-is-embᵉ</a> <a id="2582" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2582" class="Bound">is-emb-fᵉ</a> <a id="2592" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2592" class="Bound">yᵉ</a> <a id="2595" class="Symbol">=</a>
      <a id="2603" href="foundation-core.propositions%25E1%25B5%2589.html#3210" class="Function">is-prop-is-proof-irrelevantᵉ</a> <a id="2632" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2653" class="Function">αᵉ</a>
      <a id="2641" class="Keyword">where</a>
      <a id="2653" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2653" class="Function">αᵉ</a> <a id="2656" class="Symbol">:</a> <a id="2658" class="Symbol">(</a><a id="2659" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2659" class="Bound">tᵉ</a> <a id="2662" class="Symbol">:</a> <a id="2664" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html#962" class="Function">fiberᵉ</a> <a id="2671" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2674" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2592" class="Bound">yᵉ</a><a id="2676" class="Symbol">)</a> <a id="2678" class="Symbol">→</a> <a id="2680" href="foundation-core.contractible-types%25E1%25B5%2589.html#908" class="Function">is-contrᵉ</a> <a id="2690" class="Symbol">(</a><a id="2691" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html#962" class="Function">fiberᵉ</a> <a id="2698" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2701" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2592" class="Bound">yᵉ</a><a id="2703" class="Symbol">)</a>
      <a id="2711" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2653" class="Function">αᵉ</a> <a id="2714" class="Symbol">(</a><a id="2715" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2715" class="Bound">xᵉ</a> <a id="2718" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2721" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a><a id="2726" class="Symbol">)</a> <a id="2728" class="Symbol">=</a>
        <a id="2738" href="foundation-core.contractible-types%25E1%25B5%2589.html#2606" class="Function">is-contr-equivᵉ</a>
          <a id="2764" class="Symbol">(</a> <a id="2766" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html#1028" class="Function">fiber&#39;ᵉ</a> <a id="2774" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2777" class="Symbol">(</a><a id="2778" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2781" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2715" class="Bound">xᵉ</a><a id="2783" class="Symbol">))</a>
          <a id="2796" class="Symbol">(</a> <a id="2798" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html#6929" class="Function">equiv-fiberᵉ</a> <a id="2811" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2814" class="Symbol">(</a><a id="2815" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a> <a id="2818" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2715" class="Bound">xᵉ</a><a id="2820" class="Symbol">))</a>
          <a id="2833" class="Symbol">(</a> <a id="2835" href="foundation.fundamental-theorem-of-identity-types%25E1%25B5%2589.html#2352" class="Function">fundamental-theorem-id&#39;ᵉ</a> <a id="2860" class="Symbol">(λ</a> <a id="2863" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2863" class="Bound">_</a> <a id="2865" class="Symbol">→</a> <a id="2867" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2871" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2127" class="Bound">fᵉ</a><a id="2873" class="Symbol">)</a> <a id="2875" class="Symbol">(</a><a id="2876" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2582" class="Bound">is-emb-fᵉ</a> <a id="2886" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2715" class="Bound">xᵉ</a><a id="2888" class="Symbol">))</a>

<a id="2892" class="Keyword">module</a> <a id="2899" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2899" class="Module">_</a>
  <a id="2903" class="Symbol">{</a><a id="2904" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2904" class="Bound">l1ᵉ</a> <a id="2908" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2908" class="Bound">l2ᵉ</a> <a id="2912" class="Symbol">:</a> <a id="2914" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2919" class="Symbol">}</a> <a id="2921" class="Symbol">{</a><a id="2922" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2922" class="Bound">Aᵉ</a> <a id="2925" class="Symbol">:</a> <a id="2927" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2931" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2904" class="Bound">l1ᵉ</a><a id="2934" class="Symbol">}</a> <a id="2936" class="Symbol">{</a><a id="2937" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2937" class="Bound">Bᵉ</a> <a id="2940" class="Symbol">:</a> <a id="2942" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2946" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2908" class="Bound">l2ᵉ</a><a id="2949" class="Symbol">}</a>
  <a id="2953" class="Keyword">where</a>

  <a id="2962" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2962" class="Function">emb-prop-mapᵉ</a> <a id="2976" class="Symbol">:</a> <a id="2978" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1629" class="Function">prop-mapᵉ</a> <a id="2988" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2922" class="Bound">Aᵉ</a> <a id="2991" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2937" class="Bound">Bᵉ</a> <a id="2994" class="Symbol">→</a> <a id="2996" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2922" class="Bound">Aᵉ</a> <a id="2999" href="foundation-core.embeddings%25E1%25B5%2589.html#1585" class="Function Operator">↪ᵉ</a> <a id="3002" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2937" class="Bound">Bᵉ</a>
  <a id="3007" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3012" class="Symbol">(</a><a id="3013" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2962" class="Function">emb-prop-mapᵉ</a> <a id="3027" class="Symbol">(</a><a id="3028" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3028" class="Bound">fᵉ</a> <a id="3031" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="3034" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3034" class="Bound">pᵉ</a><a id="3036" class="Symbol">))</a> <a id="3039" class="Symbol">=</a> <a id="3041" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3028" class="Bound">fᵉ</a>
  <a id="3046" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="3051" class="Symbol">(</a><a id="3052" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2962" class="Function">emb-prop-mapᵉ</a> <a id="3066" class="Symbol">(</a><a id="3067" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3067" class="Bound">fᵉ</a> <a id="3070" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="3073" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3073" class="Bound">pᵉ</a><a id="3075" class="Symbol">))</a> <a id="3078" class="Symbol">=</a> <a id="3080" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2165" class="Function">is-emb-is-prop-mapᵉ</a> <a id="3100" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3073" class="Bound">pᵉ</a>

  <a id="3106" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3106" class="Function">prop-map-embᵉ</a> <a id="3120" class="Symbol">:</a> <a id="3122" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2922" class="Bound">Aᵉ</a> <a id="3125" href="foundation-core.embeddings%25E1%25B5%2589.html#1585" class="Function Operator">↪ᵉ</a> <a id="3128" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2937" class="Bound">Bᵉ</a> <a id="3131" class="Symbol">→</a> <a id="3133" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1629" class="Function">prop-mapᵉ</a> <a id="3143" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2922" class="Bound">Aᵉ</a> <a id="3146" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2937" class="Bound">Bᵉ</a>
  <a id="3151" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3156" class="Symbol">(</a><a id="3157" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3106" class="Function">prop-map-embᵉ</a> <a id="3171" class="Symbol">(</a><a id="3172" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3172" class="Bound">fᵉ</a> <a id="3175" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="3178" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3178" class="Bound">pᵉ</a><a id="3180" class="Symbol">))</a> <a id="3183" class="Symbol">=</a> <a id="3185" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3172" class="Bound">fᵉ</a>
  <a id="3190" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="3195" class="Symbol">(</a><a id="3196" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3106" class="Function">prop-map-embᵉ</a> <a id="3210" class="Symbol">(</a><a id="3211" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3211" class="Bound">fᵉ</a> <a id="3214" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="3217" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3217" class="Bound">pᵉ</a><a id="3219" class="Symbol">))</a> <a id="3222" class="Symbol">=</a> <a id="3224" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2507" class="Function">is-prop-map-is-embᵉ</a> <a id="3244" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3217" class="Bound">pᵉ</a>

  <a id="3250" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3250" class="Function">is-prop-map-embᵉ</a> <a id="3267" class="Symbol">:</a> <a id="3269" class="Symbol">(</a><a id="3270" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3270" class="Bound">fᵉ</a> <a id="3273" class="Symbol">:</a> <a id="3275" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2922" class="Bound">Aᵉ</a> <a id="3278" href="foundation-core.embeddings%25E1%25B5%2589.html#1585" class="Function Operator">↪ᵉ</a> <a id="3281" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2937" class="Bound">Bᵉ</a><a id="3283" class="Symbol">)</a> <a id="3285" class="Symbol">→</a> <a id="3287" href="foundation-core.propositional-maps%25E1%25B5%2589.html#1441" class="Function">is-prop-mapᵉ</a> <a id="3300" class="Symbol">(</a><a id="3301" href="foundation-core.embeddings%25E1%25B5%2589.html#1753" class="Function">map-embᵉ</a> <a id="3310" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3270" class="Bound">fᵉ</a><a id="3312" class="Symbol">)</a>
  <a id="3316" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3250" class="Function">is-prop-map-embᵉ</a> <a id="3333" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3333" class="Bound">fᵉ</a> <a id="3336" class="Symbol">=</a> <a id="3338" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2507" class="Function">is-prop-map-is-embᵉ</a> <a id="3358" class="Symbol">(</a><a id="3359" href="foundation-core.embeddings%25E1%25B5%2589.html#1804" class="Function">is-emb-map-embᵉ</a> <a id="3375" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3333" class="Bound">fᵉ</a><a id="3377" class="Symbol">)</a>

  <a id="3382" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3382" class="Function">is-prop-map-emb&#39;ᵉ</a> <a id="3400" class="Symbol">:</a> <a id="3402" class="Symbol">(</a><a id="3403" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3403" class="Bound">fᵉ</a> <a id="3406" class="Symbol">:</a> <a id="3408" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2922" class="Bound">Aᵉ</a> <a id="3411" href="foundation-core.embeddings%25E1%25B5%2589.html#1585" class="Function Operator">↪ᵉ</a> <a id="3414" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2937" class="Bound">Bᵉ</a><a id="3416" class="Symbol">)</a> <a id="3418" class="Symbol">→</a> <a id="3420" class="Symbol">(</a><a id="3421" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3421" class="Bound">bᵉ</a> <a id="3424" class="Symbol">:</a> <a id="3426" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2937" class="Bound">Bᵉ</a><a id="3428" class="Symbol">)</a> <a id="3430" class="Symbol">→</a> <a id="3432" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="3441" class="Symbol">(</a><a id="3442" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html#1028" class="Function">fiber&#39;ᵉ</a> <a id="3450" class="Symbol">(</a><a id="3451" href="foundation-core.embeddings%25E1%25B5%2589.html#1753" class="Function">map-embᵉ</a> <a id="3460" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3403" class="Bound">fᵉ</a><a id="3462" class="Symbol">)</a> <a id="3464" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3421" class="Bound">bᵉ</a><a id="3466" class="Symbol">)</a>
  <a id="3470" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3382" class="Function">is-prop-map-emb&#39;ᵉ</a> <a id="3488" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3488" class="Bound">fᵉ</a> <a id="3491" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3491" class="Bound">yᵉ</a> <a id="3494" class="Symbol">=</a>
    <a id="3500" href="foundation-core.propositions%25E1%25B5%2589.html#4311" class="Function">is-prop-equiv&#39;ᵉ</a> <a id="3516" class="Symbol">(</a><a id="3517" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html#6929" class="Function">equiv-fiberᵉ</a> <a id="3530" class="Symbol">(</a><a id="3531" href="foundation-core.embeddings%25E1%25B5%2589.html#1753" class="Function">map-embᵉ</a> <a id="3540" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3488" class="Bound">fᵉ</a><a id="3542" class="Symbol">)</a> <a id="3544" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3491" class="Bound">yᵉ</a><a id="3546" class="Symbol">)</a> <a id="3548" class="Symbol">(</a><a id="3549" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3250" class="Function">is-prop-map-embᵉ</a> <a id="3566" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3488" class="Bound">fᵉ</a> <a id="3569" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3491" class="Bound">yᵉ</a><a id="3571" class="Symbol">)</a>

  <a id="3576" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3576" class="Function">fiber-emb-Propᵉ</a> <a id="3592" class="Symbol">:</a> <a id="3594" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2922" class="Bound">Aᵉ</a> <a id="3597" href="foundation-core.embeddings%25E1%25B5%2589.html#1585" class="Function Operator">↪ᵉ</a> <a id="3600" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2937" class="Bound">Bᵉ</a> <a id="3603" class="Symbol">→</a> <a id="3605" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2937" class="Bound">Bᵉ</a> <a id="3608" class="Symbol">→</a> <a id="3610" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="3616" class="Symbol">(</a><a id="3617" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2904" class="Bound">l1ᵉ</a> <a id="3621" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3623" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2908" class="Bound">l2ᵉ</a><a id="3626" class="Symbol">)</a>
  <a id="3630" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3635" class="Symbol">(</a><a id="3636" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3576" class="Function">fiber-emb-Propᵉ</a> <a id="3652" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3652" class="Bound">fᵉ</a> <a id="3655" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3655" class="Bound">yᵉ</a><a id="3657" class="Symbol">)</a> <a id="3659" class="Symbol">=</a> <a id="3661" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html#962" class="Function">fiberᵉ</a> <a id="3668" class="Symbol">(</a><a id="3669" href="foundation-core.embeddings%25E1%25B5%2589.html#1753" class="Function">map-embᵉ</a> <a id="3678" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3652" class="Bound">fᵉ</a><a id="3680" class="Symbol">)</a> <a id="3682" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3655" class="Bound">yᵉ</a>
  <a id="3687" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="3692" class="Symbol">(</a><a id="3693" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3576" class="Function">fiber-emb-Propᵉ</a> <a id="3709" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3709" class="Bound">fᵉ</a> <a id="3712" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3712" class="Bound">yᵉ</a><a id="3714" class="Symbol">)</a> <a id="3716" class="Symbol">=</a> <a id="3718" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3250" class="Function">is-prop-map-embᵉ</a> <a id="3735" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3709" class="Bound">fᵉ</a> <a id="3738" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3712" class="Bound">yᵉ</a>

  <a id="3744" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3744" class="Function">fiber-emb-Prop&#39;ᵉ</a> <a id="3761" class="Symbol">:</a> <a id="3763" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2922" class="Bound">Aᵉ</a> <a id="3766" href="foundation-core.embeddings%25E1%25B5%2589.html#1585" class="Function Operator">↪ᵉ</a> <a id="3769" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2937" class="Bound">Bᵉ</a> <a id="3772" class="Symbol">→</a> <a id="3774" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2937" class="Bound">Bᵉ</a> <a id="3777" class="Symbol">→</a> <a id="3779" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="3785" class="Symbol">(</a><a id="3786" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2904" class="Bound">l1ᵉ</a> <a id="3790" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3792" href="foundation-core.propositional-maps%25E1%25B5%2589.html#2908" class="Bound">l2ᵉ</a><a id="3795" class="Symbol">)</a>
  <a id="3799" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3804" class="Symbol">(</a><a id="3805" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3744" class="Function">fiber-emb-Prop&#39;ᵉ</a> <a id="3822" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3822" class="Bound">fᵉ</a> <a id="3825" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3825" class="Bound">yᵉ</a><a id="3827" class="Symbol">)</a> <a id="3829" class="Symbol">=</a> <a id="3831" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html#1028" class="Function">fiber&#39;ᵉ</a> <a id="3839" class="Symbol">(</a><a id="3840" href="foundation-core.embeddings%25E1%25B5%2589.html#1753" class="Function">map-embᵉ</a> <a id="3849" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3822" class="Bound">fᵉ</a><a id="3851" class="Symbol">)</a> <a id="3853" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3825" class="Bound">yᵉ</a>
  <a id="3858" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="3863" class="Symbol">(</a><a id="3864" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3744" class="Function">fiber-emb-Prop&#39;ᵉ</a> <a id="3881" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3881" class="Bound">fᵉ</a> <a id="3884" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3884" class="Bound">yᵉ</a><a id="3886" class="Symbol">)</a> <a id="3888" class="Symbol">=</a> <a id="3890" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3382" class="Function">is-prop-map-emb&#39;ᵉ</a> <a id="3908" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3881" class="Bound">fᵉ</a> <a id="3911" href="foundation-core.propositional-maps%25E1%25B5%2589.html#3884" class="Bound">yᵉ</a>
</pre>