Circuit layout description - retry.

I've realised previous version was a bit messy, so here is a new one. Main difference is that instead of having "batch" fitting 1 scalar operation as a primitive, we consider the polynomials processing as a "primary" computation, and try to fit everything around it. This also generalises a bit to multi-column setting (which I'm not doing here, but have in mind for future).

I've also ceased the idea of using selector rotations for now - it can always be added later if the layout is regular, but for now it strays me away from my main goal.

Primary concept is batch, which is a vertical space fitting linear combination of NUM_DIGITS coefficients. BATCH_SIZE = NUM_DIGITS + BATCH_OFFSET (which is optional).

We have a POLY_FAN_IN parameter (expected to be ~10), which is amount of different rotations that we are free to use in computing the linear combination.

Particular set of parameters that I have in mind is the following: BASE=5 --> NUM_DIGITS=55, with POLY_FAN_IN=11 it takes 5 cells in the end of this vertical space in the column C (what previously was SKIP, but now it is contained in the tail end of the big batch). This allows to set BATCH_OFFSET=0.

I.e. SKIP = ceil(BATCH_SIZE / POLY_FAN_IN).

In the column b, the SKIP must be left empty (as it seems nothing useful can be written there except *maybe* scalars, but that breaks cartesian structure in a way that is extremely unpleasant).

The effective space BATCH_EFF = BATCH_SIZE - SKIP is divided into chunks of size (NUM_LIMBS+1)*BASE, hosting our standard cartesian structure (here, chunks are relatively large, so it makes sense to leave option to artificially increase main chunk using BATCH_OFFSET).

However, in ours, particularly pleasant case, BATCH_EFF = 50, which nicely hosts exactly 2 chunks of size 25.

Therefore, of (N+B+1) batches, ceil(N/2) is taken by our scalars (the last batch needs to be either treated separately, or I will require 2|N, we will see what is more convenient). Then, the lookup is allocated.

The arithmetic gate can still be allocated in the initial batches, if they are not taken by the lookup. Asymptotically, for large N, it is the case. I need to decide on exact functioning of the arithmetic gate later.