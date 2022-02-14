---- MODULE MC ----
EXTENDS learning, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
const_162833163429948000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_162833163429949000 == 
Permutations(const_162833163429948000)
----

=============================================================================
\* Modification History
\* Created Sat Aug 07 12:20:34 CEST 2021 by rchaves
