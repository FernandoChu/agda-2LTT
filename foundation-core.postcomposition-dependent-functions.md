# Postcomposition of dependent functions

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="foundation-core.postcomposition-dependent-functions.html" class="Module">foundation-core.postcomposition-dependent-functions</a> <a id="110" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="166" class="Keyword">open</a> <a id="171" class="Keyword">import</a> <a id="178" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

Given a type `A` and a family of maps `f : {a : A} → X a → Y a`, the
{{#concept "postcomposition function" Disambiguation="of dependent functions by a family of maps" Agda=postcomp-Π}}
of dependent functions `(a : A) → X a` by the family of maps `f`

```text
  postcomp-Π A f : ((a : A) → X a) → ((a : A) → Y a)
```

is defined by `λ h x → f (h x)`.

Note that, since the definition of the family of maps `f` depends on the base
`A`, postcomposition of dependent functions does not generalize
[postcomposition of functions](foundation-core.postcomposition-functions.md) in
the same way that
[precomposition of dependent functions](foundation-core.precomposition-dependent-functions.md)
generalizes
[precomposition of functions](foundation-core.precomposition-functions.md). If
`A` can vary while keeping `f` fixed, we have necessarily reduced to the case of
[postcomposition of functions](foundation-core.postcomposition-functions.md).

## Definitions

### Postcomposition of dependent functions

<pre class="Agda"><a id="1280" class="Keyword">module</a> <a id="1287" href="foundation-core.postcomposition-dependent-functions.html#1287" class="Module">_</a>
  <a id="1291" class="Symbol">{</a><a id="1292" href="foundation-core.postcomposition-dependent-functions.html#1292" class="Bound">l1</a> <a id="1295" href="foundation-core.postcomposition-dependent-functions.html#1295" class="Bound">l2</a> <a id="1298" href="foundation-core.postcomposition-dependent-functions.html#1298" class="Bound">l3</a> <a id="1301" class="Symbol">:</a> <a id="1303" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1308" class="Symbol">}</a> <a id="1310" class="Symbol">(</a><a id="1311" href="foundation-core.postcomposition-dependent-functions.html#1311" class="Bound">A</a> <a id="1313" class="Symbol">:</a> <a id="1315" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1318" href="foundation-core.postcomposition-dependent-functions.html#1292" class="Bound">l1</a><a id="1320" class="Symbol">)</a> <a id="1322" class="Symbol">{</a><a id="1323" href="foundation-core.postcomposition-dependent-functions.html#1323" class="Bound">X</a> <a id="1325" class="Symbol">:</a> <a id="1327" href="foundation-core.postcomposition-dependent-functions.html#1311" class="Bound">A</a> <a id="1329" class="Symbol">→</a> <a id="1331" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1334" href="foundation-core.postcomposition-dependent-functions.html#1295" class="Bound">l2</a><a id="1336" class="Symbol">}</a> <a id="1338" class="Symbol">{</a><a id="1339" href="foundation-core.postcomposition-dependent-functions.html#1339" class="Bound">Y</a> <a id="1341" class="Symbol">:</a> <a id="1343" href="foundation-core.postcomposition-dependent-functions.html#1311" class="Bound">A</a> <a id="1345" class="Symbol">→</a> <a id="1347" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1350" href="foundation-core.postcomposition-dependent-functions.html#1298" class="Bound">l3</a><a id="1352" class="Symbol">}</a>
  <a id="1356" class="Keyword">where</a>

  <a id="1365" href="foundation-core.postcomposition-dependent-functions.html#1365" class="Function">postcomp-Π</a> <a id="1376" class="Symbol">:</a> <a id="1378" class="Symbol">({</a><a id="1380" href="foundation-core.postcomposition-dependent-functions.html#1380" class="Bound">a</a> <a id="1382" class="Symbol">:</a> <a id="1384" href="foundation-core.postcomposition-dependent-functions.html#1311" class="Bound">A</a><a id="1385" class="Symbol">}</a> <a id="1387" class="Symbol">→</a> <a id="1389" href="foundation-core.postcomposition-dependent-functions.html#1323" class="Bound">X</a> <a id="1391" href="foundation-core.postcomposition-dependent-functions.html#1380" class="Bound">a</a> <a id="1393" class="Symbol">→</a> <a id="1395" href="foundation-core.postcomposition-dependent-functions.html#1339" class="Bound">Y</a> <a id="1397" href="foundation-core.postcomposition-dependent-functions.html#1380" class="Bound">a</a><a id="1398" class="Symbol">)</a> <a id="1400" class="Symbol">→</a> <a id="1402" class="Symbol">((</a><a id="1404" href="foundation-core.postcomposition-dependent-functions.html#1404" class="Bound">a</a> <a id="1406" class="Symbol">:</a> <a id="1408" href="foundation-core.postcomposition-dependent-functions.html#1311" class="Bound">A</a><a id="1409" class="Symbol">)</a> <a id="1411" class="Symbol">→</a> <a id="1413" href="foundation-core.postcomposition-dependent-functions.html#1323" class="Bound">X</a> <a id="1415" href="foundation-core.postcomposition-dependent-functions.html#1404" class="Bound">a</a><a id="1416" class="Symbol">)</a> <a id="1418" class="Symbol">→</a> <a id="1420" class="Symbol">((</a><a id="1422" href="foundation-core.postcomposition-dependent-functions.html#1422" class="Bound">a</a> <a id="1424" class="Symbol">:</a> <a id="1426" href="foundation-core.postcomposition-dependent-functions.html#1311" class="Bound">A</a><a id="1427" class="Symbol">)</a> <a id="1429" class="Symbol">→</a> <a id="1431" href="foundation-core.postcomposition-dependent-functions.html#1339" class="Bound">Y</a> <a id="1433" href="foundation-core.postcomposition-dependent-functions.html#1422" class="Bound">a</a><a id="1434" class="Symbol">)</a>
  <a id="1438" href="foundation-core.postcomposition-dependent-functions.html#1365" class="Function">postcomp-Π</a> <a id="1449" href="foundation-core.postcomposition-dependent-functions.html#1449" class="Bound">f</a> <a id="1451" class="Symbol">=</a> <a id="1453" href="foundation-core.postcomposition-dependent-functions.html#1449" class="Bound">f</a> <a id="1455" href="foundation-core.function-types.html#455" class="Function Operator">∘_</a>
</pre>