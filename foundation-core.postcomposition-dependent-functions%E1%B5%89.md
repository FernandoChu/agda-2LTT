# Postcomposition of dependent functions

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html" class="Module">foundation-core.postcomposition-dependent-functionsᵉ</a> <a id="111" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="167" class="Keyword">open</a> <a id="172" class="Keyword">import</a> <a id="179" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="208" class="Keyword">open</a> <a id="213" class="Keyword">import</a> <a id="220" href="foundation-core.function-types%25E1%25B5%2589.html" class="Module">foundation-core.function-typesᵉ</a>
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

<pre class="Agda"><a id="1283" class="Keyword">module</a> <a id="1290" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1290" class="Module">_</a>
  <a id="1294" class="Symbol">{</a><a id="1295" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1295" class="Bound">l1ᵉ</a> <a id="1299" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1299" class="Bound">l2ᵉ</a> <a id="1303" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1303" class="Bound">l3ᵉ</a> <a id="1307" class="Symbol">:</a> <a id="1309" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1314" class="Symbol">}</a> <a id="1316" class="Symbol">(</a><a id="1317" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1317" class="Bound">Aᵉ</a> <a id="1320" class="Symbol">:</a> <a id="1322" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1326" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1295" class="Bound">l1ᵉ</a><a id="1329" class="Symbol">)</a> <a id="1331" class="Symbol">{</a><a id="1332" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1332" class="Bound">Xᵉ</a> <a id="1335" class="Symbol">:</a> <a id="1337" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1317" class="Bound">Aᵉ</a> <a id="1340" class="Symbol">→</a> <a id="1342" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1346" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1299" class="Bound">l2ᵉ</a><a id="1349" class="Symbol">}</a> <a id="1351" class="Symbol">{</a><a id="1352" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1352" class="Bound">Yᵉ</a> <a id="1355" class="Symbol">:</a> <a id="1357" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1317" class="Bound">Aᵉ</a> <a id="1360" class="Symbol">→</a> <a id="1362" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1366" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1303" class="Bound">l3ᵉ</a><a id="1369" class="Symbol">}</a>
  <a id="1373" class="Keyword">where</a>

  <a id="1382" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1382" class="Function">postcomp-Πᵉ</a> <a id="1394" class="Symbol">:</a> <a id="1396" class="Symbol">({</a><a id="1398" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1398" class="Bound">aᵉ</a> <a id="1401" class="Symbol">:</a> <a id="1403" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1317" class="Bound">Aᵉ</a><a id="1405" class="Symbol">}</a> <a id="1407" class="Symbol">→</a> <a id="1409" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1332" class="Bound">Xᵉ</a> <a id="1412" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1398" class="Bound">aᵉ</a> <a id="1415" class="Symbol">→</a> <a id="1417" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1352" class="Bound">Yᵉ</a> <a id="1420" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1398" class="Bound">aᵉ</a><a id="1422" class="Symbol">)</a> <a id="1424" class="Symbol">→</a> <a id="1426" class="Symbol">((</a><a id="1428" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1428" class="Bound">aᵉ</a> <a id="1431" class="Symbol">:</a> <a id="1433" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1317" class="Bound">Aᵉ</a><a id="1435" class="Symbol">)</a> <a id="1437" class="Symbol">→</a> <a id="1439" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1332" class="Bound">Xᵉ</a> <a id="1442" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1428" class="Bound">aᵉ</a><a id="1444" class="Symbol">)</a> <a id="1446" class="Symbol">→</a> <a id="1448" class="Symbol">((</a><a id="1450" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1450" class="Bound">aᵉ</a> <a id="1453" class="Symbol">:</a> <a id="1455" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1317" class="Bound">Aᵉ</a><a id="1457" class="Symbol">)</a> <a id="1459" class="Symbol">→</a> <a id="1461" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1352" class="Bound">Yᵉ</a> <a id="1464" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1450" class="Bound">aᵉ</a><a id="1466" class="Symbol">)</a>
  <a id="1470" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1382" class="Function">postcomp-Πᵉ</a> <a id="1482" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1482" class="Bound">fᵉ</a> <a id="1485" class="Symbol">=</a> <a id="1487" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1482" class="Bound">fᵉ</a> <a id="1490" href="foundation-core.function-types%25E1%25B5%2589.html#476" class="Function Operator">∘ᵉ_</a>
</pre>