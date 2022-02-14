---- MODULE MC ----
EXTENDS learning, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
const_162833140729633000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_162833140729634000 == 
Permutations(const_162833140729633000)
----

=============================================================================
\* Modification History
\* Created Sat Aug 07 12:16:47 CEST 2021 by rchaves
