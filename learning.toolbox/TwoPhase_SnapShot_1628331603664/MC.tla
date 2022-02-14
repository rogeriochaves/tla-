---- MODULE MC ----
EXTENDS learning, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
const_162833159948144000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_162833159948145000 == 
Permutations(const_162833159948144000)
----

=============================================================================
\* Modification History
\* Created Sat Aug 07 12:19:59 CEST 2021 by rchaves
