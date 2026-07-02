# Section 3 Online Half-Rich Covering Strategy

This note records the intended proof strategy for the main improving-descriptions
statement used in Section 3.

## Target

The primary theorem is the complexity-improvement half:

```lean
ManyIJDescriptions U x i j k ->
  InDescriptionProfile U x (i - k + O(log(n+i+j))) (j + O(log(n+i+j)))
```

In words: if `x` has at least `2^k` different `(i,j)` descriptions, then `x`
has an `(i-k, j)` description, up to visible logarithmic slack.  The
size-improvement form `(i, j-k)` should be derived later as a corollary by the
ordinary portion/description-shift lemma, not proved as a separate foundational
selector construction.

## Enumerations

For fixed parameters `i,j,k`:

1. There is an effective enumeration of all `(i,j)` descriptions, i.e. finite
   sets/models of prefix complexity at most `i` and cardinality at most `2^j`.
2. From this, there is an effective multiplicity enumeration of elements: when a
   newly enumerated set appears, all of its elements receive one additional
   occurrence.  Thus an element's multiplicity is monotone in time.

Define:

- `rich`: multiplicity at least `2^k`;
- `half-rich`: multiplicity at least `2^(k-1)`.

Richness and half-richness are lower-semicomputable events in this enumeration.

## Online Chunking Algorithm

The algorithm streams finite chunks, each of size at most `2^j`.

Maintain a set of elements already placed into some emitted chunk.  Run the two
enumeration processes above.  Whenever a new rich element appears that has not
yet been placed into any chunk, open a new chunk and fill it with currently
unplaced half-rich elements, up to the size limit `2^j`.  Emit that chunk.

Consequences:

- Every emitted chunk has cardinality at most `2^j`.
- If `x` is rich, then at the moment it first becomes rich, either it has already
  been placed into an earlier chunk, or it triggers a new chunk and is placed
  then.  Hence all rich elements are covered.
- The code of a chunk is described by the fixed online algorithm, the visible
  parameters `i,j,k`, and the ordinal number of the chunk in the stream.  There
  is no need to know the total number of chunks, the final stabilized rich set,
  or a halting-count/stabilization certificate.

Thus the real proof obligation is to bound the number of emitted chunks by
`2^(i-k+O(1))`.

## Counting Bound for Chunks

Split emitted chunks into full and non-full chunks.

### Full chunks

A full chunk has size exactly `2^j`, and every element placed into it is
half-rich, i.e. appears in at least `2^(k-1)` descriptions.  Since there are at
most about `2^(i+1)` descriptions and each has size at most `2^j`, the total
incidence mass is at most `2^(i+1) * 2^j`.  Therefore the number of full chunks
is at most roughly

```text
(2^(i+1) * 2^j) / (2^(k-1) * 2^j) = 2^(i-k+2).
```

This is the standard half-rich double-counting estimate.

### Non-full chunks

If a chunk is non-full, then after emitting it there were no unplaced half-rich
elements left at that moment.  For a later chunk to be triggered, choose one
witness element that triggers that later chunk.  At the previous non-full time it
was not half-rich; at the trigger time it is rich.  Therefore this single witness
element has acquired at least `2^(k-1)` fresh `(i,j)` descriptions during the
intervening time interval.

Charge those fresh descriptions to the later non-full/full trigger interval.
The intervals between successive non-full chunks are disjoint in enumeration
time, so the charged description occurrences for the chosen witnesses use
disjoint newly enumerated description codes.  Importantly, this is a charge to
fresh descriptions containing one chosen trigger element per interval, not to the
whole incidence mass of all elements in all newly enumerated sets.  Hence the
total charge is bounded by the total number of `(i,j)` descriptions, about
`2^i` (or `2^(i+1)` with the current prefix-code convention).  Thus the number
of non-full-triggering phases is at most roughly
`2^i / 2^(k-1) = 2^(i-k+1)`.

Therefore the total number of chunks is bounded by `2^(i-k+O(1))`.

## Lean Decomposition Suggested

Do not try to recover a final stabilized rich set and then chunk it.  That route
introduces an unnecessary halt-count/stabilization certificate and overuses the
short chunk address.

Instead, formalize the online stream directly.  Suggested intermediate lemmas:

1. `onlineHalfRichChunks_size_le`: every emitted chunk has card `<= 2^j`.
2. `onlineHalfRichChunks_cover_rich`: every rich element appears in some emitted
   chunk.
3. `onlineHalfRichChunks_full_count_le`: full chunks are bounded by the
   half-rich incidence count, `<= 2^(i-k+O(1))`.
4. `onlineHalfRichChunks_nonfull_count_le`: non-full chunks are bounded by the
   number of fresh occurrences needed to create a new rich element after all
   half-rich elements have been exhausted, again `<= 2^(i-k+O(1))`.
5. `partrec_onlineHalfRichChunkSelector`: given `i,j,k,h`, run the online stream
   until the `h`-th chunk is emitted and output its canonical uniform code.
6. `halfRichComplexityPortion_selector_correct`: if `x` is rich, choose the
   ordinal `h` of a chunk covering `x`; the chunk-count bound gives
   `h < 2^(i-k+O(1))`, and the selector code plus `h` yields the desired
   complexity bound.

## Points Requiring Care

- The threshold `2^(k-1)` needs a convention for `k = 0`; use truncated
  subtraction or handle this case separately.
- The total number of `(i,j)` descriptions may be stated as `<= 2^(i+1)` in the
  current project, depending on prefix-code conventions.  Constants are harmless
  but should be kept explicit.
- The non-full chunk argument must charge fresh descriptions for one chosen
  trigger element per interval.  Do not bound it by total incidence mass, which
  would introduce an unwanted extra `2^j` factor.  The disjointness comes from
  disjoint time intervals between successive non-full chunks.
- Emitted chunks may contain elements that later become richer; this is fine
  because elements are placed at most once.
- The selector should enumerate chunks by ordinal and halt when the requested
  ordinal appears.  It should not require knowing whether the stream has ended.
