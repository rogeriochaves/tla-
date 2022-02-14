---- MODULE MC ----
EXTENDS learning, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
const_162833164890252000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_162833164890253000 == 
Permutations(const_162833164890252000)
----

=============================================================================
\* Modification History
\* Created Sat Aug 07 12:20:48 CEST 2021 by rchaves
