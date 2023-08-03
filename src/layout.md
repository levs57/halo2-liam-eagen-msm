Circuit layout description.

NL = NUM_LIMBS
B = BASE
S = SKIP
N - amount of points
BSIZE - batch size
PSIZE - polynomial batch size
D - amount of digits
LOGTABLESIZE - log_2 size of the lookup table we are using

following conditions must be satisfied:


NL = log_B(p) / (2*LOGTABLESIZE)
(NL+1)*B + SKIP = BSIZE --- to fit the structure of 1 batch
PSIZE | BSIZE           --- to ensure that skips are populated regularly
SKIP >= BSIZE / PSIZE   --- to ensure that polynomial batching fits into skips
BSIZE | N+B+1           --- to ensure that our (N+B+1) polynomials coefficients are fit into batches regularly (can be relaxed but I'm lazy and this is not too restrictive, just add few points lol)

D = ceil(log_B(q)/2) - to ensure that we can encode at least sqrt(q)-sized scalar

denote BA = (N+B+1)/BSIZE --- batch amount

circuit has 3 advice tables, a, b, c, in first, second, and third phases respectively

high-level region structure is as follows (these are not regions in halo2 library, from halo2 library standpoint circuit is monolithic):


**The column a** consists of one large region of size ``D*(N+B+1)``

it hosts ``D*BA`` batches, which are also observable in columns b and c (so other regions do not end in a middle of a batch)

each ``BA`` batch is populated by the same coefficient of the polynomials of Liam Eagen's argument


**The column b** has three different regions:

Region 1 is populated by scalars, which are contained in batches - each batch serves exactly 1 scalar. The total amount of scalars is ``N``, so there is, totally, ``N*BSIZE`` rows.

We assume that this region ``(B1)`` is smaller than ``(A1)`` - otherwise this description will not be efficient.

**?** - do I need a buffer empty batch here? I think I do, and this is fairly minor, so for now I assume it is here.

((buffer batch))

The region ``(B2)`` effective rows must be of the same size as lookup table. First, it populates ``D*BA - N - 1`` batches, using all non-skipped rows in them, therefore, it consumes ``(D*BA - N - 1)*(NL+1)*B`` of the lookup table. If ``2**LOGTABLESIZE`` is larger than that, it then takes up ``2**LOGTABLESIZE - (D*BA - N - 1)*(NL+1)*B`` consequent rows. For reasons that will be clear after, we ,might also copy last element of the table up until it fits into a full batch.

Third region ``(B3)`` is relatively small and must also not intersect ``(A1)`` (which is a trivial requirement if ``(B1)`` and ``(B2)`` span more than it). I'm currently thinking it can be allocated in the lower end of the column (and there also must ``BSIZE`` sized buffer zone at negative range before row zero).

It has the size ``4*D`` and hosts values of our polynomials and their derivatives in 2 challenge points (we actually only need to know linear combination of derivatives, so ``2`` values per point).


**The column c** has two different regions:

Region ``(C1)`` coincides with whatever of ``A1`` and ``B1+B2` is larger. It hosts, in parallel, three different computations - one is computing linear combination of polynomials (and it is allocated against skipped cells of each batch). Another computation is lookup - and it takes up all the cells that are taken by limbs or integrity elements.
Third computation is computation of rhs of Liam Eagen's argument, and it exactly populates every row corresponding to each scalar.

**Structure of an individual batch in (B1):**

|                  |                     |
| ---------------- | ------------------- |
|b                 |i                    |
|                  |                     |
|sc                | 0                   |
|integrity[0]      | 1                   |
|...               |                     |
|integrity[NL-1]   | NL                  |
|sc_bucket[1]      | NL+1                | 
|sc_limb[1][0]     | NL+2                |
|sc_limb[1][1]     | NL+3                |
|...               |  ..                 |
|sc_limb[1][NL-1]  | 2*NL+1              |
|sc_bucket[2]      | 2*NL+2              | 
|...               |                     |
|...               |                     |
|sc_limb[B-1][NL-1]| (NL+1)*B-1          |
|  skip            | (NL+1)*B            |
|  ...             |                     |
|  skip            | (NL+1)*B+S-1        |


**The following gates are activated:**

(these are technically not gates, as we will combine them later if they are activated on non-intersecting subsets, true gates with already formed selectors will be capitalized in this document to distinguish)

---

``sc_from_buckets``: ``sc = sc_bucket[1] + 2*sc_bucket[2]  + ... + (B-1)*sc_bucket[b-1]``

in terms of offsets:

``b[0] = b[NL+1] + 2*b[2*NL+2] + ... + (B-1)b[(B-1)(NL+1)]``

activated at each row hosting a scalar, i.e. ``i%BSIZE == 0``, ``i<N*BSIZE``.

This is a singular selector, which we call ``S1``.

---

``bucket_from_limbs`` : ``sc_bucket[i] = sc_limb[i][0] + (-B)**(LOGTABLESIZE) sc_limb[i][1] + ... +(-B)**((NL-1)*LOGTABLESIZE)sc_limb[i][NL-1]``

in terms of offsets:

``b[0] = b[1] + (-B)**(...) b[2] + ... +(-B)**(...) b[NL-1]``

it is activated at each row hosting a bucket, and so can be activated with the following selector (obtained from S1):

``S_sec = S1[-(NL+1)] + S1[-2*(NL+1)] + ... S1[-(B-1)*(NL+1)]``

---

``limb_integrity_check:`` ``integrity[i] = sc_limb[1][i] + sc_limb[2][i] + ... sc_limb[B-1][i]``

in terms of offsets, it fits nicely with the first gate (which abuses nice cartesian structure of this layout):

``b[0] = b[NL+1] + b[2*NL+2] + ... + b[(B-1)(NL+1)]``

it is activated by another custom selector obtained by rotations of S1:

``S_prim = S1[-1] + S1[-2] + ... + S1[-NL]``

---

These three "gates" are activated on disjoint domain, and so can be freely combined as follows:

``B_GATE = S1 * sc_from_buckets + S_prim * limb_integrity_check + S_sec * bucket_from_limbs``

---

Lookup gates operate over ``(B1)`` and ``(B2)``, in columns b and c. The set being looked up are all limbs and all integrity checks, i.e., anything living in ``i%BSIZE < (NL+1)*B & (i%BSIZE)%(NL+1)!=0``.

In the region ``(B2)``, against every table entry prover puts the amount of accesses to this element of the table. Then, in a phase 3, it is given a challenge ``v``, and intent is to compute the following sum:

``sum{by i in (B2)} b[i]/(b-t[i])`` and ensure that it equals ``sum{by i in (B1)} 1/(v-b[i])``

We declare the following gates:

``lookup_rhs_1 = (c[1]-c[0])*(v-b[1]) - 1`` - which is activated using the selector ``S3``, which is active in ``(B1)`` at every *non-first* limb / integrity check - i.e. it is actually ``S_sec[-2]+S_sec[-3]+...``.
``lookup_rhs_2 = (c[1]-c[-1])*(v-b[1]) - 1`` - which is activated at ``S_sec`` - i.e. against each bucket
``lookup_rhs_3 = (c[1]-c[-1-S])*(v-b[1]) - 1`` - which is activated at ``S1`` - i.e. against each scalar

The initial condition is ``c[-1-S] == 0``, and this system of equations ensures that the value in ``c[N*BSIZE-S-1]`` is actually the rhs.

Now, we need to subtract the lhs.

We declare the following gates:

``lookup_lhs_1 = (c[1] - c[0])*(v-t) + b[1]``
``lookup_lhs_2 = (c[1] - c[-1-S])*(v-t) + b[1]``

We need to activate first one in every row corresponding to a table, except of the ones with that are ``i%BSIZE==0`` and live in ``(A1)``, on which we need to activate the second one.

I did not manage to do it without introducing additional selectors, but I can do it using only one:

Selector ``S_TABLE`` is defined as follows: it is nonzero in the whole region ``(B2)`` that the table populates (including skips), and it is either ``1`` or ``-1``, switching the sign at the end of each skip (i.e. in the end of each full batch). Out of the region (A1) there are no skips, and hence no sign switches anymore.

To obtain the second selector, we just compute ``S_TABLE - S_TABLE[-1]`` - due to the sign switching behavior, this is nonzero only at the row just after skip, and on the edges - the starting edge being activated is a desirable behavior, and end edge being activated doesn't matter, as we just sacrifice this ``c`` entry and not use it anymore.

To obtain the first selector, we compute ``S_TABLE + S_TABLE[S]`` - which is activated in all appropriate rows, and also in last skip ones, which doesn't matter because we have the buffer batch.

An illustration:

Batch structure:

``0000(xxxxxxxxsss)(xxxxxxxxsss)(xxxxxxxxsss)xxxxxxxxxxxx0000``

S_TABLE:

``0000(+++++++++++)(-----------)(+++++++++++)------------0000``

S_TABLE-S_TABLE[-1]

``0000(x0000000000)(x0000000000)(x0000000000)x00000000000x000 ``

S_TABLE+S_TABLE[S]

``0xxx(xxxxxxxx000)(xxxxxxxx000)(xxxxxxxx000)xxxxxxxxxxxx0000``

where ``Q`` is basically a selector to whether we need to jump. There are various ways of constructing such selector, to which I propose rotating ``S1`` forward: ``S1[N+B+]``

activated at i % BATCH_SIZE == 0 aka s1

integrity[i] = sc_limb[1][i] + sc_limb[2][i] + ... sc_limb[B-1][i]; for all i

b[0] = b[NL] + b[2\*NL+2] + ... +b[(B-1)(NL+1)]; activated at (s1[-1] + ... s1[-NL])


c[i+1] - c[i] = 1/(v-b[i])

234233

000010
100010
010001
001000

~2^15

5^15

