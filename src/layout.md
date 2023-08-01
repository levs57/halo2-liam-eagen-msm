cheatsheet for layout:

NL = NUM_LIMBS
B = BASE
S = SKIP

column b:
| | |
| -----------    | ----------- |
|sc[0]           | 0           |
|sc_bucket[1]    | 1           |
|sc_limb[1][0]   | 2           |
|sc_limb[1][1]   | 3           |
|...             |  ..         |
|sc_limb[1][NL]  | NL+2        |
|sc_bucket[2]    | NL+3        |
|...             |             |
|...             |             |
|sc_limb[B-1][NL]| (NL+2)*(B-1)    |
|  blank         | (NL+2)*(B-1)+1  |
|  ...           |                 |
|  blank         | (NL+2)*(B-1)+S  |
| | |
| | |
|sc[1]           | (NL+2)*(B-1)+S+1|
