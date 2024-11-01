# The type of natural numbers

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="228" class="Keyword">open</a> <a id="233" class="Keyword">import</a> <a id="240" href="foundation-core.empty-types.html" class="Module">foundation-core.empty-types</a>
<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="311" class="Keyword">open</a> <a id="316" class="Keyword">import</a> <a id="323" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="354" class="Keyword">open</a> <a id="359" class="Keyword">import</a> <a id="366" href="foundation-core.injective-maps.html" class="Module">foundation-core.injective-maps</a>
<a id="397" class="Keyword">open</a> <a id="402" class="Keyword">import</a> <a id="409" href="foundation-core.negation.html" class="Module">foundation-core.negation</a>
</pre>
</details>

## Idea

The {{#concept "natural numbers" WD="natural number" WDID=Q21199 Agda=ℕ}} is an
inductively generated type by the zero element and the successor function. The
induction principle for the natural numbers works to construct sections of type
families over the natural numbers.

## Definitions

### The inductive definition of the type of natural numbers

<pre class="Agda"><a id="820" class="Keyword">data</a> <a id="ℕ"></a><a id="825" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="827" class="Symbol">:</a> <a id="829" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="832" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="838" class="Keyword">where</a>
  <a id="ℕ.zero-ℕ"></a><a id="846" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="853" class="Symbol">:</a> <a id="855" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
  <a id="ℕ.succ-ℕ"></a><a id="859" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="866" class="Symbol">:</a> <a id="868" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="870" class="Symbol">→</a> <a id="872" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>

<a id="875" class="Symbol">{-#</a> <a id="879" class="Keyword">BUILTIN</a> <a id="887" class="Keyword">NATURAL</a> <a id="895" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="897" class="Symbol">#-}</a>

<a id="second-succ-ℕ"></a><a id="902" href="elementary-number-theory.natural-numbers.html#902" class="Function">second-succ-ℕ</a> <a id="916" class="Symbol">:</a> <a id="918" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="920" class="Symbol">→</a> <a id="922" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="924" href="elementary-number-theory.natural-numbers.html#902" class="Function">second-succ-ℕ</a> <a id="938" class="Symbol">=</a> <a id="940" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="947" href="foundation-core.function-types.html#455" class="Function Operator">∘</a> <a id="949" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a>

<a id="third-succ-ℕ"></a><a id="957" href="elementary-number-theory.natural-numbers.html#957" class="Function">third-succ-ℕ</a> <a id="970" class="Symbol">:</a> <a id="972" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="974" class="Symbol">→</a> <a id="976" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="978" href="elementary-number-theory.natural-numbers.html#957" class="Function">third-succ-ℕ</a> <a id="991" class="Symbol">=</a> <a id="993" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1000" href="foundation-core.function-types.html#455" class="Function Operator">∘</a> <a id="1002" href="elementary-number-theory.natural-numbers.html#902" class="Function">second-succ-ℕ</a>

<a id="fourth-succ-ℕ"></a><a id="1017" href="elementary-number-theory.natural-numbers.html#1017" class="Function">fourth-succ-ℕ</a> <a id="1031" class="Symbol">:</a> <a id="1033" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1035" class="Symbol">→</a> <a id="1037" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1039" href="elementary-number-theory.natural-numbers.html#1017" class="Function">fourth-succ-ℕ</a> <a id="1053" class="Symbol">=</a> <a id="1055" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1062" href="foundation-core.function-types.html#455" class="Function Operator">∘</a> <a id="1064" href="elementary-number-theory.natural-numbers.html#957" class="Function">third-succ-ℕ</a>
</pre>
### Useful predicates on the natural numbers

These predicates can of course be asserted directly without much trouble.
However, using the defined predicates ensures uniformity, and helps naming
definitions.

<pre class="Agda"><a id="is-zero-ℕ"></a><a id="1299" href="elementary-number-theory.natural-numbers.html#1299" class="Function">is-zero-ℕ</a> <a id="1309" class="Symbol">:</a> <a id="1311" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1313" class="Symbol">→</a> <a id="1315" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1318" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1324" href="elementary-number-theory.natural-numbers.html#1299" class="Function">is-zero-ℕ</a> <a id="1334" href="elementary-number-theory.natural-numbers.html#1334" class="Bound">n</a> <a id="1336" class="Symbol">=</a> <a id="1338" class="Symbol">(</a><a id="1339" href="elementary-number-theory.natural-numbers.html#1334" class="Bound">n</a> <a id="1341" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1343" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a><a id="1349" class="Symbol">)</a>

<a id="is-zero-ℕ&#39;"></a><a id="1352" href="elementary-number-theory.natural-numbers.html#1352" class="Function">is-zero-ℕ&#39;</a> <a id="1363" class="Symbol">:</a> <a id="1365" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1367" class="Symbol">→</a> <a id="1369" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1372" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1378" href="elementary-number-theory.natural-numbers.html#1352" class="Function">is-zero-ℕ&#39;</a> <a id="1389" href="elementary-number-theory.natural-numbers.html#1389" class="Bound">n</a> <a id="1391" class="Symbol">=</a> <a id="1393" class="Symbol">(</a><a id="1394" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="1401" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1403" href="elementary-number-theory.natural-numbers.html#1389" class="Bound">n</a><a id="1404" class="Symbol">)</a>

<a id="is-successor-ℕ"></a><a id="1407" href="elementary-number-theory.natural-numbers.html#1407" class="Function">is-successor-ℕ</a> <a id="1422" class="Symbol">:</a> <a id="1424" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1426" class="Symbol">→</a> <a id="1428" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1431" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1437" href="elementary-number-theory.natural-numbers.html#1407" class="Function">is-successor-ℕ</a> <a id="1452" href="elementary-number-theory.natural-numbers.html#1452" class="Bound">n</a> <a id="1454" class="Symbol">=</a> <a id="1456" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1458" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1460" class="Symbol">(λ</a> <a id="1463" href="elementary-number-theory.natural-numbers.html#1463" class="Bound">y</a> <a id="1465" class="Symbol">→</a> <a id="1467" href="elementary-number-theory.natural-numbers.html#1452" class="Bound">n</a> <a id="1469" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1471" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1478" href="elementary-number-theory.natural-numbers.html#1463" class="Bound">y</a><a id="1479" class="Symbol">)</a>

<a id="is-nonzero-ℕ"></a><a id="1482" href="elementary-number-theory.natural-numbers.html#1482" class="Function">is-nonzero-ℕ</a> <a id="1495" class="Symbol">:</a> <a id="1497" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1499" class="Symbol">→</a> <a id="1501" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1504" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1510" href="elementary-number-theory.natural-numbers.html#1482" class="Function">is-nonzero-ℕ</a> <a id="1523" href="elementary-number-theory.natural-numbers.html#1523" class="Bound">n</a> <a id="1525" class="Symbol">=</a> <a id="1527" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="1529" class="Symbol">(</a><a id="1530" href="elementary-number-theory.natural-numbers.html#1299" class="Function">is-zero-ℕ</a> <a id="1540" href="elementary-number-theory.natural-numbers.html#1523" class="Bound">n</a><a id="1541" class="Symbol">)</a>

<a id="is-one-ℕ"></a><a id="1544" href="elementary-number-theory.natural-numbers.html#1544" class="Function">is-one-ℕ</a> <a id="1553" class="Symbol">:</a> <a id="1555" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1557" class="Symbol">→</a> <a id="1559" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1562" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1568" href="elementary-number-theory.natural-numbers.html#1544" class="Function">is-one-ℕ</a> <a id="1577" href="elementary-number-theory.natural-numbers.html#1577" class="Bound">n</a> <a id="1579" class="Symbol">=</a> <a id="1581" class="Symbol">(</a><a id="1582" href="elementary-number-theory.natural-numbers.html#1577" class="Bound">n</a> <a id="1584" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1586" class="Number">1</a><a id="1587" class="Symbol">)</a>

<a id="is-one-ℕ&#39;"></a><a id="1590" href="elementary-number-theory.natural-numbers.html#1590" class="Function">is-one-ℕ&#39;</a> <a id="1600" class="Symbol">:</a> <a id="1602" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1604" class="Symbol">→</a> <a id="1606" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1609" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1615" href="elementary-number-theory.natural-numbers.html#1590" class="Function">is-one-ℕ&#39;</a> <a id="1625" href="elementary-number-theory.natural-numbers.html#1625" class="Bound">n</a> <a id="1627" class="Symbol">=</a> <a id="1629" class="Symbol">(</a><a id="1630" class="Number">1</a> <a id="1632" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1634" href="elementary-number-theory.natural-numbers.html#1625" class="Bound">n</a><a id="1635" class="Symbol">)</a>

<a id="is-not-one-ℕ"></a><a id="1638" href="elementary-number-theory.natural-numbers.html#1638" class="Function">is-not-one-ℕ</a> <a id="1651" class="Symbol">:</a> <a id="1653" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1655" class="Symbol">→</a> <a id="1657" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1660" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1666" href="elementary-number-theory.natural-numbers.html#1638" class="Function">is-not-one-ℕ</a> <a id="1679" href="elementary-number-theory.natural-numbers.html#1679" class="Bound">n</a> <a id="1681" class="Symbol">=</a> <a id="1683" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="1685" class="Symbol">(</a><a id="1686" href="elementary-number-theory.natural-numbers.html#1544" class="Function">is-one-ℕ</a> <a id="1695" href="elementary-number-theory.natural-numbers.html#1679" class="Bound">n</a><a id="1696" class="Symbol">)</a>

<a id="is-not-one-ℕ&#39;"></a><a id="1699" href="elementary-number-theory.natural-numbers.html#1699" class="Function">is-not-one-ℕ&#39;</a> <a id="1713" class="Symbol">:</a> <a id="1715" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1717" class="Symbol">→</a> <a id="1719" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1722" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1728" href="elementary-number-theory.natural-numbers.html#1699" class="Function">is-not-one-ℕ&#39;</a> <a id="1742" href="elementary-number-theory.natural-numbers.html#1742" class="Bound">n</a> <a id="1744" class="Symbol">=</a> <a id="1746" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="1748" class="Symbol">(</a><a id="1749" href="elementary-number-theory.natural-numbers.html#1590" class="Function">is-one-ℕ&#39;</a> <a id="1759" href="elementary-number-theory.natural-numbers.html#1742" class="Bound">n</a><a id="1760" class="Symbol">)</a>
</pre>
## Properties

### The induction principle of ℕ

The induction principle of the natural numbers is the 74th theorem on
[Freek Wiedijk's](http://www.cs.ru.nl/F.Wiedijk/) list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

<pre class="Agda"><a id="ind-ℕ"></a><a id="2019" href="elementary-number-theory.natural-numbers.html#2019" class="Function">ind-ℕ</a> <a id="2025" class="Symbol">:</a>
  <a id="2029" class="Symbol">{</a><a id="2030" href="elementary-number-theory.natural-numbers.html#2030" class="Bound">l</a> <a id="2032" class="Symbol">:</a> <a id="2034" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2039" class="Symbol">}</a> <a id="2041" class="Symbol">{</a><a id="2042" href="elementary-number-theory.natural-numbers.html#2042" class="Bound">P</a> <a id="2044" class="Symbol">:</a> <a id="2046" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2048" class="Symbol">→</a> <a id="2050" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2053" href="elementary-number-theory.natural-numbers.html#2030" class="Bound">l</a><a id="2054" class="Symbol">}</a> <a id="2056" class="Symbol">→</a>
  <a id="2060" href="elementary-number-theory.natural-numbers.html#2042" class="Bound">P</a> <a id="2062" class="Number">0</a> <a id="2064" class="Symbol">→</a> <a id="2066" class="Symbol">((</a><a id="2068" href="elementary-number-theory.natural-numbers.html#2068" class="Bound">n</a> <a id="2070" class="Symbol">:</a> <a id="2072" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2073" class="Symbol">)</a> <a id="2075" class="Symbol">→</a> <a id="2077" href="elementary-number-theory.natural-numbers.html#2042" class="Bound">P</a> <a id="2079" href="elementary-number-theory.natural-numbers.html#2068" class="Bound">n</a> <a id="2081" class="Symbol">→</a> <a id="2083" href="elementary-number-theory.natural-numbers.html#2042" class="Bound">P</a> <a id="2085" class="Symbol">(</a><a id="2086" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2093" href="elementary-number-theory.natural-numbers.html#2068" class="Bound">n</a><a id="2094" class="Symbol">))</a> <a id="2097" class="Symbol">→</a> <a id="2099" class="Symbol">((</a><a id="2101" href="elementary-number-theory.natural-numbers.html#2101" class="Bound">n</a> <a id="2103" class="Symbol">:</a> <a id="2105" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2106" class="Symbol">)</a> <a id="2108" class="Symbol">→</a> <a id="2110" href="elementary-number-theory.natural-numbers.html#2042" class="Bound">P</a> <a id="2112" href="elementary-number-theory.natural-numbers.html#2101" class="Bound">n</a><a id="2113" class="Symbol">)</a>
<a id="2115" href="elementary-number-theory.natural-numbers.html#2019" class="Function">ind-ℕ</a> <a id="2121" href="elementary-number-theory.natural-numbers.html#2121" class="Bound">p-zero</a> <a id="2128" href="elementary-number-theory.natural-numbers.html#2128" class="Bound">p-succ</a> <a id="2135" class="Number">0</a> <a id="2137" class="Symbol">=</a> <a id="2139" href="elementary-number-theory.natural-numbers.html#2121" class="Bound">p-zero</a>
<a id="2146" href="elementary-number-theory.natural-numbers.html#2019" class="Function">ind-ℕ</a> <a id="2152" href="elementary-number-theory.natural-numbers.html#2152" class="Bound">p-zero</a> <a id="2159" href="elementary-number-theory.natural-numbers.html#2159" class="Bound">p-succ</a> <a id="2166" class="Symbol">(</a><a id="2167" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2174" href="elementary-number-theory.natural-numbers.html#2174" class="Bound">n</a><a id="2175" class="Symbol">)</a> <a id="2177" class="Symbol">=</a> <a id="2179" href="elementary-number-theory.natural-numbers.html#2159" class="Bound">p-succ</a> <a id="2186" href="elementary-number-theory.natural-numbers.html#2174" class="Bound">n</a> <a id="2188" class="Symbol">(</a><a id="2189" href="elementary-number-theory.natural-numbers.html#2019" class="Function">ind-ℕ</a> <a id="2195" href="elementary-number-theory.natural-numbers.html#2152" class="Bound">p-zero</a> <a id="2202" href="elementary-number-theory.natural-numbers.html#2159" class="Bound">p-succ</a> <a id="2209" href="elementary-number-theory.natural-numbers.html#2174" class="Bound">n</a><a id="2210" class="Symbol">)</a>
</pre>
### The recursion principle of ℕ

<pre class="Agda"><a id="rec-ℕ"></a><a id="2259" href="elementary-number-theory.natural-numbers.html#2259" class="Function">rec-ℕ</a> <a id="2265" class="Symbol">:</a> <a id="2267" class="Symbol">{</a><a id="2268" href="elementary-number-theory.natural-numbers.html#2268" class="Bound">l</a> <a id="2270" class="Symbol">:</a> <a id="2272" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2277" class="Symbol">}</a> <a id="2279" class="Symbol">{</a><a id="2280" href="elementary-number-theory.natural-numbers.html#2280" class="Bound">A</a> <a id="2282" class="Symbol">:</a> <a id="2284" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2287" href="elementary-number-theory.natural-numbers.html#2268" class="Bound">l</a><a id="2288" class="Symbol">}</a> <a id="2290" class="Symbol">→</a> <a id="2292" href="elementary-number-theory.natural-numbers.html#2280" class="Bound">A</a> <a id="2294" class="Symbol">→</a> <a id="2296" class="Symbol">(</a><a id="2297" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2299" class="Symbol">→</a> <a id="2301" href="elementary-number-theory.natural-numbers.html#2280" class="Bound">A</a> <a id="2303" class="Symbol">→</a> <a id="2305" href="elementary-number-theory.natural-numbers.html#2280" class="Bound">A</a><a id="2306" class="Symbol">)</a> <a id="2308" class="Symbol">→</a> <a id="2310" class="Symbol">(</a><a id="2311" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2313" class="Symbol">→</a> <a id="2315" href="elementary-number-theory.natural-numbers.html#2280" class="Bound">A</a><a id="2316" class="Symbol">)</a>
<a id="2318" href="elementary-number-theory.natural-numbers.html#2259" class="Function">rec-ℕ</a> <a id="2324" class="Symbol">=</a> <a id="2326" href="elementary-number-theory.natural-numbers.html#2019" class="Function">ind-ℕ</a>
</pre>
### The successor function on ℕ is injective

<pre class="Agda"><a id="is-injective-succ-ℕ"></a><a id="2391" href="elementary-number-theory.natural-numbers.html#2391" class="Function">is-injective-succ-ℕ</a> <a id="2411" class="Symbol">:</a> <a id="2413" href="foundation-core.injective-maps.html#990" class="Function">is-injective</a> <a id="2426" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a>
<a id="2433" href="elementary-number-theory.natural-numbers.html#2391" class="Function">is-injective-succ-ℕ</a> <a id="2453" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="2458" class="Symbol">=</a> <a id="2460" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
### Successors are nonzero

<pre class="Agda"><a id="is-nonzero-succ-ℕ"></a><a id="2506" href="elementary-number-theory.natural-numbers.html#2506" class="Function">is-nonzero-succ-ℕ</a> <a id="2524" class="Symbol">:</a> <a id="2526" class="Symbol">(</a><a id="2527" href="elementary-number-theory.natural-numbers.html#2527" class="Bound">x</a> <a id="2529" class="Symbol">:</a> <a id="2531" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2532" class="Symbol">)</a> <a id="2534" class="Symbol">→</a> <a id="2536" href="elementary-number-theory.natural-numbers.html#1482" class="Function">is-nonzero-ℕ</a> <a id="2549" class="Symbol">(</a><a id="2550" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2557" href="elementary-number-theory.natural-numbers.html#2527" class="Bound">x</a><a id="2558" class="Symbol">)</a>
<a id="2560" href="elementary-number-theory.natural-numbers.html#2506" class="Function">is-nonzero-succ-ℕ</a> <a id="2578" href="elementary-number-theory.natural-numbers.html#2578" class="Bound">x</a> <a id="2580" class="Symbol">()</a>

<a id="is-nonzero-is-successor-ℕ"></a><a id="2584" href="elementary-number-theory.natural-numbers.html#2584" class="Function">is-nonzero-is-successor-ℕ</a> <a id="2610" class="Symbol">:</a> <a id="2612" class="Symbol">{</a><a id="2613" href="elementary-number-theory.natural-numbers.html#2613" class="Bound">x</a> <a id="2615" class="Symbol">:</a> <a id="2617" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2618" class="Symbol">}</a> <a id="2620" class="Symbol">→</a> <a id="2622" href="elementary-number-theory.natural-numbers.html#1407" class="Function">is-successor-ℕ</a> <a id="2637" href="elementary-number-theory.natural-numbers.html#2613" class="Bound">x</a> <a id="2639" class="Symbol">→</a> <a id="2641" href="elementary-number-theory.natural-numbers.html#1482" class="Function">is-nonzero-ℕ</a> <a id="2654" href="elementary-number-theory.natural-numbers.html#2613" class="Bound">x</a>
<a id="2656" href="elementary-number-theory.natural-numbers.html#2584" class="Function">is-nonzero-is-successor-ℕ</a> <a id="2682" class="Symbol">(</a><a id="2683" href="elementary-number-theory.natural-numbers.html#2683" class="Bound">x</a> <a id="2685" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2687" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="2691" class="Symbol">)</a> <a id="2693" class="Symbol">()</a>

<a id="is-successor-is-nonzero-ℕ"></a><a id="2697" href="elementary-number-theory.natural-numbers.html#2697" class="Function">is-successor-is-nonzero-ℕ</a> <a id="2723" class="Symbol">:</a> <a id="2725" class="Symbol">{</a><a id="2726" href="elementary-number-theory.natural-numbers.html#2726" class="Bound">x</a> <a id="2728" class="Symbol">:</a> <a id="2730" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2731" class="Symbol">}</a> <a id="2733" class="Symbol">→</a> <a id="2735" href="elementary-number-theory.natural-numbers.html#1482" class="Function">is-nonzero-ℕ</a> <a id="2748" href="elementary-number-theory.natural-numbers.html#2726" class="Bound">x</a> <a id="2750" class="Symbol">→</a> <a id="2752" href="elementary-number-theory.natural-numbers.html#1407" class="Function">is-successor-ℕ</a> <a id="2767" href="elementary-number-theory.natural-numbers.html#2726" class="Bound">x</a>
<a id="2769" href="elementary-number-theory.natural-numbers.html#2697" class="Function">is-successor-is-nonzero-ℕ</a> <a id="2795" class="Symbol">{</a><a id="2796" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a><a id="2802" class="Symbol">}</a> <a id="2804" href="elementary-number-theory.natural-numbers.html#2804" class="Bound">H</a> <a id="2806" class="Symbol">=</a> <a id="2808" href="foundation-core.empty-types.html#904" class="Function">ex-falso</a> <a id="2817" class="Symbol">(</a><a id="2818" href="elementary-number-theory.natural-numbers.html#2804" class="Bound">H</a> <a id="2820" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="2824" class="Symbol">)</a>
<a id="2826" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2830" class="Symbol">(</a><a id="2831" href="elementary-number-theory.natural-numbers.html#2697" class="Function">is-successor-is-nonzero-ℕ</a> <a id="2857" class="Symbol">{</a><a id="2858" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2865" href="elementary-number-theory.natural-numbers.html#2865" class="Bound">x</a><a id="2866" class="Symbol">}</a> <a id="2868" href="elementary-number-theory.natural-numbers.html#2868" class="Bound">H</a><a id="2869" class="Symbol">)</a> <a id="2871" class="Symbol">=</a> <a id="2873" href="elementary-number-theory.natural-numbers.html#2865" class="Bound">x</a>
<a id="2875" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2879" class="Symbol">(</a><a id="2880" href="elementary-number-theory.natural-numbers.html#2697" class="Function">is-successor-is-nonzero-ℕ</a> <a id="2906" class="Symbol">{</a><a id="2907" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2914" href="elementary-number-theory.natural-numbers.html#2914" class="Bound">x</a><a id="2915" class="Symbol">}</a> <a id="2917" href="elementary-number-theory.natural-numbers.html#2917" class="Bound">H</a><a id="2918" class="Symbol">)</a> <a id="2920" class="Symbol">=</a> <a id="2922" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="has-no-fixed-points-succ-ℕ"></a><a id="2928" href="elementary-number-theory.natural-numbers.html#2928" class="Function">has-no-fixed-points-succ-ℕ</a> <a id="2955" class="Symbol">:</a> <a id="2957" class="Symbol">(</a><a id="2958" href="elementary-number-theory.natural-numbers.html#2958" class="Bound">x</a> <a id="2960" class="Symbol">:</a> <a id="2962" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2963" class="Symbol">)</a> <a id="2965" class="Symbol">→</a> <a id="2967" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="2969" class="Symbol">(</a><a id="2970" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2977" href="elementary-number-theory.natural-numbers.html#2958" class="Bound">x</a> <a id="2979" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2981" href="elementary-number-theory.natural-numbers.html#2958" class="Bound">x</a><a id="2982" class="Symbol">)</a>
<a id="2984" href="elementary-number-theory.natural-numbers.html#2928" class="Function">has-no-fixed-points-succ-ℕ</a> <a id="3011" href="elementary-number-theory.natural-numbers.html#3011" class="Bound">x</a> <a id="3013" class="Symbol">()</a>
</pre>
### Basic nonequalities

<pre class="Agda"><a id="is-nonzero-one-ℕ"></a><a id="3054" href="elementary-number-theory.natural-numbers.html#3054" class="Function">is-nonzero-one-ℕ</a> <a id="3071" class="Symbol">:</a> <a id="3073" href="elementary-number-theory.natural-numbers.html#1482" class="Function">is-nonzero-ℕ</a> <a id="3086" class="Number">1</a>
<a id="3088" href="elementary-number-theory.natural-numbers.html#3054" class="Function">is-nonzero-one-ℕ</a> <a id="3105" class="Symbol">()</a>

<a id="is-not-one-zero-ℕ"></a><a id="3109" href="elementary-number-theory.natural-numbers.html#3109" class="Function">is-not-one-zero-ℕ</a> <a id="3127" class="Symbol">:</a> <a id="3129" href="elementary-number-theory.natural-numbers.html#1638" class="Function">is-not-one-ℕ</a> <a id="3142" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a>
<a id="3149" href="elementary-number-theory.natural-numbers.html#3109" class="Function">is-not-one-zero-ℕ</a> <a id="3167" class="Symbol">()</a>

<a id="is-nonzero-two-ℕ"></a><a id="3171" href="elementary-number-theory.natural-numbers.html#3171" class="Function">is-nonzero-two-ℕ</a> <a id="3188" class="Symbol">:</a> <a id="3190" href="elementary-number-theory.natural-numbers.html#1482" class="Function">is-nonzero-ℕ</a> <a id="3203" class="Number">2</a>
<a id="3205" href="elementary-number-theory.natural-numbers.html#3171" class="Function">is-nonzero-two-ℕ</a> <a id="3222" class="Symbol">()</a>

<a id="is-not-one-two-ℕ"></a><a id="3226" href="elementary-number-theory.natural-numbers.html#3226" class="Function">is-not-one-two-ℕ</a> <a id="3243" class="Symbol">:</a> <a id="3245" href="elementary-number-theory.natural-numbers.html#1638" class="Function">is-not-one-ℕ</a> <a id="3258" class="Number">2</a>
<a id="3260" href="elementary-number-theory.natural-numbers.html#3226" class="Function">is-not-one-two-ℕ</a> <a id="3277" class="Symbol">()</a>
</pre>
## See also

- The based induction principle is defined in
  [`based-induction-natural-numbers`](elementary-number-theory.based-induction-natural-numbers.md).
- The strong induction principle is defined in
  [`strong-induction-natural-numbers`](elementary-number-theory.strong-induction-natural-numbers.md).
- The based strong induction principle is defined in
  [`based-strong-induction-natural-numbers`](elementary-number-theory.based-strong-induction-natural-numbers.md).

## References

{{#bibliography}}